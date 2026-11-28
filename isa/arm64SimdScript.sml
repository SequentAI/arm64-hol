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

Definition elem_int_def:
  elem_int unsigned esize (x:word64) : int =
    if ¬unsigned ∧ word_bit (esize - 1) x then &w2n x - &(2 ** esize) else &w2n x
End

(* SatQ: clamp to the unsigned or signed range of esize bits. *)
Definition saturate_int_def:
  saturate_int unsigned esize (v:int) =
    let top : int = if unsigned then &(2 ** esize) - 1 else &(2 ** (esize - 1)) - 1;
        bottom : int = if unsigned then 0 else -&(2 ** (esize - 1))
    in if top < v then top else if v < bottom then bottom else v
End

Definition saturate_def:
  saturate unsigned esize v : word64 = i2w (saturate_int unsigned esize v)
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

Definition shift_imm_size_def:
  shift_imm_size (immh:word4) : num =
    if word_bit 3 immh then 64 else if word_bit 2 immh then 32
    else if word_bit 1 immh then 16 else 8
End

Definition shift_imm_elem_def:
  shift_imm_elem u (code:num) esize amount (a:word64) (c:word64) =
    let x = elem_int u esize a; y = elem_int u esize c;
        mask : word64 = w2w (simd_lane_mask esize)
    in if code = 0 then i2w (int_shr x amount)
       else if code = 2 then i2w (y + int_shr x amount)
       else if code = 4 then i2w (rshr T x amount)
       else if code = 6 then i2w (y + rshr T x amount)
       else if code = 8 then
         ((a && mask) >>> amount) ||
         (c && (mask << (esize - amount)))
       else if code = 10 ∧ ¬u then (a << amount) && mask
       else if code = 10 then
         ((a << amount) && mask) ||
         (c && (mask >>> (esize - amount)))
       else if code = 12 then saturate T esize (elem_int F esize a * &(2 ** amount))
       else if code = 14 then saturate u esize (x * &(2 ** amount))
       else 0w
End

Definition shift_imm_lanes_def:
  shift_imm_lanes 0 u (code:num) esize amount n d = (0w:word128) ∧
  shift_imm_lanes (SUC k) u code esize amount n d =
    shift_imm_lanes k u code esize amount n d ||
    put_lane esize k
      (shift_imm_elem u code esize amount (elem esize k n) (elem esize k d))
End

Definition shift_narrow_lanes_def:
  shift_narrow_lanes 0 u (code:num) esize amount n = (0w:word128) ∧
  shift_narrow_lanes (SUC k) u code esize amount n =
    let x = elem_int (if code < 18 then ¬u else u) (2 * esize)
                     (elem (2 * esize) k n);
        shifted = rshr (ODD code) x amount;
        r = if code < 18 ∧ ¬u then i2w shifted else saturate u esize shifted
    in shift_narrow_lanes k u code esize amount n || put_lane esize k r
End

Definition shift_long_lanes_def:
  shift_long_lanes 0 u esize amount n = (0w:word128) ∧
  shift_long_lanes (SUC k) u esize amount n =
    shift_long_lanes k u esize amount n ||
    put_lane (2 * esize) k
      (i2w (elem_int u esize (elem esize k n) * &(2 ** amount)))
End

Definition shift_imm_value_def:
  shift_imm_value scalar q u (immh:word4) (immb:word3) (opc:word5)
      (n:word128) (d:word128) =
    let code = w2n opc; esize = shift_imm_size immh;
        imm = 8 * w2n immh + w2n immb;
        right = 2 * esize - imm; left = imm - esize;
        bits = if scalar then esize else if q then 128 else 64;
        normal = bits DIV esize
    in if code < 16 then
         shift_imm_lanes normal u code esize
           (if code = 8 ∨ code = 0 ∨ code = 2 ∨ code = 4 ∨ code = 6
            then right else left) n d
       else if code < 20 then
         let r = shift_narrow_lanes (if scalar then 1 else 64 DIV esize)
               u code esize right n
         in if q ∧ ¬scalar then (r << 64) || (d && simd_lane_mask 64) else r
       else
         shift_long_lanes (64 DIV esize) u esize left (if q then n >>> 64 else n)
End

Definition three_diff_elem_def:
  three_diff_elem u (code:num) esize (a:word64) (b:word64) (c:word64) =
    let wide = 2 * esize;
        x = elem_int u (if code = 2 ∨ code = 6 then wide else esize) a;
        y = elem_int u esize b;
        z = elem_int u wide c
    in if code = 0 ∨ code = 2 then i2w (x + y)
       else if code = 4 ∨ code = 6 then i2w (x - y)
       else if code = 8 ∨ code = 12 then
         i2w (rshr u (if code = 8 then &w2n a + &w2n b else &w2n a - &w2n b) esize)
       else if code = 10 ∨ code = 14 then
         i2w ((if code = 10 then z else 0) + (if x < y then y - x else x - y))
       else if code = 16 then i2w (z + x * y)
       else if code = 20 then i2w (z - x * y)
       else if code = 24 then i2w (x * y)
       else
         let product = saturate_int F wide (2 * x * y) in
         saturate F wide (if code = 18 then z + product
                          else if code = 22 then z - product else product)
End

Definition three_diff_lanes_def:
  three_diff_lanes 0 u (code:num) esize n m d = (0w:word128) ∧
  three_diff_lanes (SUC k) u code esize n m d =
    let wide = 2 * esize;
        narrow = (code = 8 ∨ code = 12);
        a = elem (if narrow ∨ code = 2 ∨ code = 6 then wide else esize) k n;
        b = elem (if narrow then wide else esize) k m
    in three_diff_lanes k u code esize n m d ||
       put_lane (if narrow then esize else wide) k
         (three_diff_elem u code esize a b (elem wide k d))
End

Definition pmull_bytes_def:
  pmull_bytes 0 (n:word128) (m:word128) = (0w:word128) ∧
  pmull_bytes (SUC k) n m =
    pmull_bytes k n m ||
    put_lane 16 k (w2w (clmul 8 (elem 8 k n) (elem 8 k m)))
End

Definition three_diff_value_def:
  three_diff_value scalar q u (size:word2) (opc:word5)
      (n:word128) (m:word128) (d:word128) =
    let code = w2n opc; esize = 8 * 2 ** w2n size;
        narrow = (code = 8 ∨ code = 12);
        upper = (q ∧ ¬scalar ∧ ¬narrow);
        a = if upper ∧ code ≠ 2 ∧ code ≠ 6 then n >>> 64 else n;
        b = if upper then m >>> 64 else m
    in if code = 28 then
         if size = 3w then pmull_value q n m else pmull_bytes 8 a b
       else
         let r = three_diff_lanes (if scalar then 1 else 64 DIV esize) u code esize a b d
         in if narrow ∧ q then (d && simd_lane_mask 64) || (r << 64) else r
End

Definition rdm_elem_def:
  rdm_elem add esize (a:word64) (b:word64) (c:word64) =
    let p = 2 * elem_int F esize a * elem_int F esize b;
        z = elem_int F esize c * &(2 ** esize)
    in saturate F esize (rshr T (if add then z + p else z - p) esize)
End

Definition by_element_lanes_def:
  by_element_lanes 0 u (code:num) esize (index:num) n m d = (0w:word128) ∧
  by_element_lanes (SUC k) u code esize index n m d =
    let long = MEM code [2; 3; 6; 7; 10; 11];
        width = if long then 2 * esize else esize;
        a = elem esize k n; b = elem esize index m; c = elem width k d;
        value = if code = 0 then c + a * b
                else if code = 4 then c - a * b
                else if code = 8 then a * b
                else if long then
                  three_diff_elem u
                    (if code = 2 then 16 else if code = 3 then 18
                     else if code = 6 then 20 else if code = 7 then 22
                     else if code = 10 then 24 else 26) esize a b c
                else if u then rdm_elem (code = 13) esize a b c
                else three_same_elem (code = 13) 0w 22 esize a b c
    in by_element_lanes k u code esize index n m d || put_lane width k value
End

(* Dot product uses four byte products per lane. Matrix multiply uses eight. *)
Definition byte_products_def:
  byte_products 0 un um (i:num) (j:num) (n:word128) (m:word128) = (0:int) ∧
  byte_products (SUC k) un um i j n m =
    byte_products k un um i j n m +
    elem_int un 8 (elem 8 (i + k) n) * elem_int um 8 (elem 8 (j + k) m)
End

Definition dot_lanes_def:
  dot_lanes 0 un um indexed (index:num) n m d = (0w:word128) ∧
  dot_lanes (SUC k) un um indexed index n m d =
    let j = if indexed then index else k;
        sum = byte_products 4 un um (4 * k) (4 * j) n m
    in dot_lanes k un um indexed index n m d ||
       put_lane 32 k (elem 32 k d + i2w sum)
End

Definition by_element_value_def:
  by_element_value scalar q u (size:word2) l mbit (opc:word4) h
      (n:word128) (m:word128) (d:word128) =
    let code = w2n opc; esize = 8 * 2 ** w2n size;
        pair = (if h then 2 else 0) + (if l then 1 else 0);
        index = if size = 1w then 2 * pair + (if mbit then 1 else 0) else pair;
        long = MEM code [2; 3; 6; 7; 10; 11];
        bits = if q ∧ ¬long then 128 else 64;
        elements = if scalar then 1 else bits DIV esize;
        source = if q ∧ long ∧ ¬scalar then n >>> 64 else n
    in if code = 14 then dot_lanes (if q then 4 else 2) u u T index n m d
       else if code = 15 ∧ ¬u then
         dot_lanes (if q then 4 else 2) (size = 2w) (size = 0w) T index n m d
       else by_element_lanes elements u code esize index source m d
End

Definition rdm_lanes_def:
  rdm_lanes 0 add esize n m d = (0w:word128) ∧
  rdm_lanes (SUC k) add esize n m d =
    rdm_lanes k add esize n m d || put_lane esize k
      (rdm_elem add esize (elem esize k n) (elem esize k m) (elem esize k d))
End

Definition matrix_lanes_def:
  matrix_lanes 0 un um n m d = (0w:word128) ∧
  matrix_lanes (SUC k) un um n m d =
    let sum = byte_products 8 un um (8 * (k DIV 2)) (8 * (k MOD 2)) n m
    in matrix_lanes k un um n m d || put_lane 32 k (elem 32 k d + i2w sum)
End

Definition extension_value_def:
  extension_value scalar q u (size:word2) (opc:word5)
      (n:word128) (m:word128) (d:word128) =
    let esize = 8 * 2 ** w2n size;
        bits = if q then 128 else 64
    in if opc = 16w ∨ opc = 17w then
         rdm_lanes (if scalar then 1 else bits DIV esize) (opc = 16w) esize n m d
       else if opc = 18w then dot_lanes (bits DIV 32) u u F 0 n m d
       else if opc = 19w then dot_lanes (bits DIV 32) T F F 0 n m d
       else matrix_lanes 4 (u ∨ opc = 21w) u n m d
End
