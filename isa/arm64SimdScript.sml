(* AdvSIMD integer lane arithmetic, Arm DDI 0487. Lane 0 occupies the least
   significant bits of a vector; an element is held zero-extended in a word64. *)
Theory arm64Simd
Ancestors arm64Crypto integer_word integer words
Libs wordsLib

Definition simd_lane_mask_def:
  simd_lane_mask bits : word128 = (1w << bits) - 1w
End

Definition leading_zeros_def:
  leading_zeros 0 (x:word64) = 0 ∧
  leading_zeros (SUC n) x = if word_bit n x then 0 else SUC (leading_zeros n x)
End

(* Reverse the order of elements within each group. *)
Definition simd_reverse_def:
  simd_reverse 0 group width (x:word128) = (0w:word128) ∧
  simd_reverse (SUC n) group width x =
    (let i = n DIV group * group + (group - 1 - n MOD group);
         v = (x >>> (width * i)) && simd_lane_mask width
     in simd_reverse n group width x || (v << (width * n)))
End

Definition elem_def:
  elem esize i (x:word128) : word64 = w2w ((x >>> (esize * i)) && simd_lane_mask esize)
End

Definition put_lane_def:
  put_lane esize i (v:word64) : word128 = (w2w v && simd_lane_mask esize) << (esize * i)
End

Definition simd_copy_size_def:
  simd_copy_size (imm5:word5) : word2 =
    if word_bit 0 imm5 then 0w else if word_bit 1 imm5 then 1w
    else if word_bit 2 imm5 then 2w else 3w
End

Definition simd_copy_index_def:
  simd_copy_index (imm5:word5) sz = w2n (imm5 >>> (sz + 1))
End

Definition simd_copy_source_index_def:
  simd_copy_source_index (imm4:word4) sz = w2n (imm4 >>> sz)
End

Definition simd_copy_replicate_def:
  simd_copy_replicate esize 0 (x:word64) = (0w:word128) ∧
  simd_copy_replicate esize (SUC k) x =
    simd_copy_replicate esize k x || put_lane esize k x
End

Definition simd_copy_insert_def:
  simd_copy_insert esize (imm5:word5) x old =
    old && ¬(simd_lane_mask esize << (esize * simd_copy_index imm5
      (w2n (simd_copy_size imm5)))) ||
    put_lane esize (simd_copy_index imm5 (w2n (simd_copy_size imm5))) x
End

Definition simd_pair_elem_def:
  simd_pair_elem esize elements j (n:word128) (m:word128) =
    if j < elements then elem esize j n else elem esize (j - elements) m
End

Definition simd_permute_elem_def:
  simd_permute_elem esize (opcode:num) elements k
      (n:word128) (m:word128) =
    let part = if opcode < 4 then 0 else 1;
        pair = k DIV 2;
        index = if opcode = 1 ∨ opcode = 5 then 2 * k + part
                else if opcode = 2 ∨ opcode = 6 then 2 * pair + part
                else pair + part * (elements DIV 2)
    in if opcode = 1 ∨ opcode = 5 then simd_pair_elem esize elements index n m
       else elem esize index (if k MOD 2 = 0 then n else m)
End

Definition simd_permute_lanes_def:
  simd_permute_lanes esize opcode elements 0 n m = (0w:word128) ∧
  simd_permute_lanes esize opcode elements (SUC k) n m =
    simd_permute_lanes esize opcode elements k n m ||
    put_lane esize k (simd_permute_elem esize opcode elements k n m)
End

Definition simd_permute_value_def:
  simd_permute_value q (sz:word2) (opcode:word3) n m =
    let esize = 8 * 2 ** w2n sz;
        elements = (if q then 128 else 64) DIV esize
    in simd_permute_lanes esize (w2n opcode) elements elements n m
End

Definition simd_table_byte_def:
  simd_table_byte q (regs:num) index table0 table1 table2 table3 (old:word64) =
    let bytes = 16 in
    if index < bytes then elem 8 index table0
    else if regs > 1 ∧ index < 2 * bytes then elem 8 (index - bytes) table1
    else if regs > 2 ∧ index < 3 * bytes then elem 8 (index - 2 * bytes) table2
    else if regs > 3 ∧ index < 4 * bytes then elem 8 (index - 3 * bytes) table3
    else old
End

Definition simd_table_lanes_def:
  simd_table_lanes q (regs:num) 0 table0 table1 table2 table3 indices old =
    (0w:word128) ∧
  simd_table_lanes q regs (SUC k) table0 table1 table2 table3 indices old =
    simd_table_lanes q regs k table0 table1 table2 table3 indices old ||
    put_lane 8 k (simd_table_byte q regs (w2n (elem 8 k indices))
      table0 table1 table2 table3 (elem 8 k old))
End

Definition simd_table_value_def:
  simd_table_value q is_tbl (len:word2) table0 table1 table2 table3
      indices old =
    let elements = if q then 16 else 8;
        regs = w2n len + 1
    in simd_table_lanes q regs elements table0 table1 table2 table3 indices
         (if is_tbl then 0w else old)
End

Definition simd_extract_value_def:
  simd_extract_value q (imm4:word4) lo hi =
    let shift = 8 * w2n imm4;
        low = simd_lane_mask 64;
        value = if q then (lo >>> shift) || (hi << (128 - shift))
                else ((lo && low) >>> shift) || ((hi && low) << (64 - shift))
    in if q then value else value && simd_lane_mask 64
End

Definition elem_int_def:
  elem_int unsigned esize (x:word64) : int =
    if ¬unsigned ∧ word_bit (esize - 1) x then &w2n x - &(2 ** esize) else &w2n x
End

Definition simd_copy_gpr_def:
  simd_copy_gpr q signed esize (x:word64) =
    let value : word64 = if signed then i2w (elem_int F esize x) else x
    in if q then value else w2w (w2w value : word32)
End

(* SatQ: clamp to the unsigned or signed range of esize bits. *)
Definition saturate_def:
  saturate unsigned esize (v:int) : word64 =
    let top : int = if unsigned then &(2 ** esize) - 1 else &(2 ** (esize - 1)) - 1;
        bottom : int = if unsigned then 0 else -&(2 ** (esize - 1))
    in i2w (if top < v then top else if v < bottom then bottom else v)
End

Definition test_mask_def:
  test_mask b : word64 = if b then ¬0w else 0w
End

(* Integer >> rounds towards minus infinity. *)
Definition int_shr_def:
  int_shr (v:int) n = v / &(2 ** n)
End

(* RShr for 0 < n. *)
Definition rshr_def:
  rshr rounding (v:int) n = int_shr (if rounding then v + &(2 ** (n - 1)) else v) n
End

(* SSHL, SQSHL, SRSHL, SQRSHL and their unsigned forms shift by the signed
   low byte of the second element; a negative shift goes right. *)
Definition shift_elem_def:
  shift_elem unsigned saturating rounding esize (a:word64) (b:word64) =
    let x = elem_int unsigned esize a;
        shift = w2i (w2w b : word8);
        v = if 0 ≤ shift then x * &(2 ** Num shift) else rshr rounding x (Num (-shift))
    in if saturating then saturate unsigned esize v else i2w v
End

(* AND, BIC, ORR and ORN by size; EOR, BSL, BIT and BIF by size when u. *)
Definition logical_elem_def:
  logical_elem u (size:word2) (a:word64) b c =
    if u then
      if size = 0w then a ?? b
      else if size = 1w then b ?? ((b ?? a) && c)
      else if size = 2w then c ?? ((c ?? a) && b)
      else c ?? ((c ?? a) && ¬b)
    else if size = 0w then a && b
    else if size = 1w then a && ¬b
    else if size = 2w then a || b
    else a || ¬b
End

(* An element of the three-same group with opcode code: a and b come from n
   and m, or from adjacent elements of m:n for the pairwise opcodes 20, 21 and
   23; c is the destination element the accumulating forms read. *)
Definition three_same_elem_def:
  three_same_elem u size (code:num) esize (a:word64) (b:word64) (c:word64) : word64 =
    let x = elem_int u esize a; y = elem_int u esize b in
      if code = 0 then i2w (int_shr (x + y) 1)
      else if code = 1 then saturate u esize (x + y)
      else if code = 2 then i2w (int_shr (x + y + 1) 1)
      else if code = 3 then logical_elem u size a b c
      else if code = 4 then i2w (int_shr (x - y) 1)
      else if code = 5 then saturate u esize (x - y)
      else if code = 6 then test_mask (y < x)
      else if code = 7 then test_mask (y ≤ x)
      else if code < 12 then shift_elem u (code = 9 ∨ code = 11) (10 ≤ code) esize a b
      else if code = 12 ∨ code = 20 then (if x < y then b else a)
      else if code = 13 ∨ code = 21 then (if x < y then a else b)
      else if code = 14 then i2w (if x < y then y - x else x - y)
      else if code = 15 then c + i2w (if x < y then y - x else x - y)
      else if code = 16 ∨ code = 23 then (if u then a - b else a + b)
      else if code = 17 then test_mask (if u then a = b else a && b ≠ 0w)
      else if code = 18 then (if u then c - a * b else c + a * b)
      else if code = 19 then (if u then w2w (clmul esize a b) else a * b)
      else saturate F esize
             (rshr u (2 * elem_int F esize a * elem_int F esize b) esize)
End

Definition pair_elem_def:
  pair_elem esize elements j (n:word128) (m:word128) =
    if j < elements then elem esize j n else elem esize (j - elements) m
End

Definition three_same_lanes_def:
  three_same_lanes u size (code:num) esize elements 0 n m d = (0w:word128) ∧
  three_same_lanes u size code esize elements (SUC k) n m d =
    let pairwise = (code = 20 ∨ code = 21 ∨ code = 23);
        a = if pairwise then pair_elem esize elements (2 * k) n m else elem esize k n;
        b = if pairwise then pair_elem esize elements (2 * k + 1) n m else elem esize k m
    in three_same_lanes u size code esize elements k n m d ||
       put_lane esize k (three_same_elem u size code esize a b (elem esize k d))
End

Definition three_same_value_def:
  three_same_value scalar q u (size:word2) (opc:word5) n m d =
    let esize = 8 * 2 ** w2n size;
        elements = (if scalar then esize else if q then 128 else 64) DIV esize
    in three_same_lanes u size (w2n opc) esize elements elements n m d
End

(* RecipEstimate and RecipSqrtEstimate, without increased precision. The
   search runs while a * (b + 1)^2 < 2^28; 512 steps reach every b it can
   stop at. *)
Definition recip_estimate_def:
  recip_estimate a = (2 ** 19 DIV (a * 2 + 1) + 1) DIV 2
End

Definition rsqrt_search_def:
  rsqrt_search 0 (a:num) (b:num) = b ∧
  rsqrt_search (SUC fuel) a b =
    if a * (b + 1) * (b + 1) < 2 ** 28 then rsqrt_search fuel a (b + 1) else b
End

Definition rsqrt_estimate_def:
  rsqrt_estimate a =
    let scaled = if a < 256 then a * 2 + 1 else (a DIV 2 * 2 + 1) * 2
    in (rsqrt_search 512 scaled 512 + 1) DIV 2
End

(* An element of the two-register miscellaneous group with opcode code, from
   element a of n and c of the destination. CLS counts the bits below the
   sign bit that equal it. *)
Definition two_misc_elem_def:
  two_misc_elem u (size:word2) (code:num) esize (a:word64) (c:word64) : word64 =
    let x = elem_int F esize a in
      if code = 3 then saturate u esize (elem_int (¬u) esize a + elem_int u esize c)
      else if code = 4 then
        n2w (if u then leading_zeros esize a else leading_zeros (esize - 1) (a ?? (a >>> 1)))
      else if code = 5 then
        (if ¬u then n2w (bit_count (w2w a : word8))
         else if size = 0w then ¬a
         else n2w (BIT_REVERSE 8 (w2n a)))
      else if code = 7 then saturate F esize (if u ∨ x < 0 then -x else x)
      else if code = 8 then test_mask (if u then 0 ≤ x else 0 < x)
      else if code = 9 then test_mask (if u then x ≤ 0 else x = 0)
      else if code = 10 then test_mask (x < 0)
      else if code = 11 then i2w (if u ∨ x < 0 then -x else x)
      else if u then
        (if w2n a < 2 ** 30 then 0xffffffffw
         else n2w (rsqrt_estimate (w2n a DIV 2 ** 23)) << 23)
      else if word_bit 31 a then n2w (recip_estimate (w2n a DIV 2 ** 23)) << 23
      else 0xffffffffw
End

Definition two_misc_lanes_def:
  two_misc_lanes u size (code:num) esize 0 n d = (0w:word128) ∧
  two_misc_lanes u size code esize (SUC k) n d =
    two_misc_lanes u size code esize k n d ||
    put_lane esize k (two_misc_elem u size code esize (elem esize k n) (elem esize k d))
End

(* SADDLP, UADDLP, SADALP and UADALP: double-width sums of adjacent pairs. *)
Definition pair_add_lanes_def:
  pair_add_lanes u acc esize 0 n d = (0w:word128) ∧
  pair_add_lanes u acc esize (SUC k) n d =
    let total = elem_int u esize (elem esize (2 * k) n) +
                elem_int u esize (elem esize (2 * k + 1) n);
        prior = if acc then elem (2 * esize) k d else 0w
    in pair_add_lanes u acc esize k n d || put_lane (2 * esize) k (prior + i2w total)
End

(* XTN (code 18), SQXTUN (code 18 with u), SQXTN and UQXTN (code 20) narrow
   double-width elements. *)
Definition narrow_lanes_def:
  narrow_lanes u (code:num) esize 0 (n:word128) = (0w:word128) ∧
  narrow_lanes u code esize (SUC k) n =
    let a = elem (2 * esize) k n;
        r = if code = 20 then saturate u esize (elem_int u (2 * esize) a)
            else if u then saturate T esize (elem_int F (2 * esize) a)
            else a
    in narrow_lanes u code esize k n || put_lane esize k r
End

Definition shll_lanes_def:
  shll_lanes esize 0 (n:word128) = (0w:word128) ∧
  shll_lanes esize (SUC k) n =
    shll_lanes esize k n || put_lane (2 * esize) k (elem esize k n << esize)
End

(* The vector forms of XTN, SQXTUN, SQXTN and UQXTN with q write the upper
   half and keep the lower; SHLL with q reads the upper half. *)
Definition two_misc_value_def:
  two_misc_value scalar q u (size:word2) (opc:word5) (n:word128) (d:word128) =
    let code = w2n opc;
        esize = if code = 5 then 8 else 8 * 2 ** w2n size;
        elements = (if scalar then esize else if q then 128 else 64) DIV esize
    in
      if code = 0 then simd_reverse elements ((if u then 32 else 64) DIV esize) esize n
      else if code = 1 then simd_reverse elements (16 DIV esize) esize n
      else if code = 2 ∨ code = 6 then pair_add_lanes u (code = 6) esize (elements DIV 2) n d
      else if code = 19 then shll_lanes esize (64 DIV esize) (if q then n >>> 64 else n)
      else if code = 18 ∨ code = 20 then
        (let r = narrow_lanes u code esize (if scalar then 1 else 64 DIV esize) n in
           if q ∧ ¬scalar then (r << 64) || (d && simd_lane_mask 64) else r)
      else two_misc_lanes u size code esize elements n d
End

Definition lane_sum_def:
  lane_sum u esize 0 (x:word128) = (0:int) ∧
  lane_sum u esize (SUC k) x = lane_sum u esize k x + elem_int u esize (elem esize k x)
End

Definition lane_best_def:
  lane_best u least esize 0 (x:word128) = elem esize 0 x ∧
  lane_best u least esize (SUC k) x =
    let a = lane_best u least esize k x; b = elem esize (SUC k) x;
        y = elem_int u esize a; z = elem_int u esize b
    in if (if least then z < y else y < z) then b else a
End

(* SADDLV and UADDLV (opcode 3), SMAXV and UMAXV (10), SMINV and UMINV (26),
   ADDV and the scalar ADDP (27), which adds the two 64-bit elements. *)
Definition across_value_def:
  across_value q u (size:word2) (opc:word5) (n:word128) =
    let esize = 8 * 2 ** w2n size;
        elements = (if q then 128 else 64) DIV esize
    in
      if opc = 3w then put_lane (2 * esize) 0 (i2w (lane_sum u esize elements n))
      else if opc = 27w then put_lane esize 0 (i2w (lane_sum F esize elements n))
      else put_lane esize 0 (lane_best u (word_bit 4 opc) esize (elements - 1) n)
End
