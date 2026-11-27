(* A64 little-endian EL0 instructions, Arm DDI 0487 and DDI 0602. *)
Theory arm64Isa
Ancestors arm64Crypto words list
Libs wordsLib
val () = app (fn n =>
  type_abbrev ("word" ^ Int.toString n, wordsSyntax.mk_word_type
    (fcpLib.index_type (Arbnum.fromInt n)))) [14, 19, 21, 26];

Datatype:
  arm64_feat = <| asimd : bool; crc32 : bool; aes : bool; pmull : bool;
                  sha1 : bool; sha256 : bool; sha512 : bool; sha3 : bool;
                  sm3 : bool; sm4 : bool |>
End

Definition armv9_4_def:
  armv9_4 = <| asimd := T; crc32 := T; aes := T; pmull := T;
               sha1 := T; sha256 := T; sha512 := T; sha3 := T;
               sm3 := T; sm4 := T |>
End

Datatype:
  perm = <| read : bool; write : bool; execute : bool |>
End

Datatype:
  arm64_machine = <|
    regs : 'g;
    sp : word64;
    pc : word64;
    nzcv : bool # bool # bool # bool;
    vregs : 'v;
    mem : 'm;
    perms : 'p
  |>
End

Type arm64_state = ``:(word5 -> word64, word64 -> word8, word64 -> perm, word5 -> word128) arm64_machine``

Datatype:
  arm64_storage = <|
    get_reg : 'g -> word5 -> word64;
    put_reg : word5 -> word64 -> 'g -> 'g;
    get_vec : 'v -> word5 -> word128;
    put_vec : word5 -> word128 -> 'v -> 'v;
    get_byte : 'm -> word64 -> word8;
    put_byte : word64 -> word8 -> 'm -> 'm;
    get_perm : 'p -> word64 -> perm
  |>
End

Definition functional_storage_def:
  functional_storage = <|
    get_reg := (λf (r:word5). f r);
    put_reg := (λ(r:word5) (v:word64) f. (r =+ v) f);
    get_vec := (λf (r:word5). f r);
    put_vec := (λ(r:word5) (v:word128) f. (r =+ v) f);
    get_byte := (λf (a:word64). f a);
    put_byte := (λ(a:word64) (v:word8) f. (a =+ v) f);
    get_perm := (λf (a:word64). f a)
  |>
End

(* Unprivileged loads and stores (LDTR, STTR) behave as ordinary accesses at
   EL0; NonTemporal names the LDNP and STNP pair forms. *)
Datatype:
  index_mode = Offset | PreIndex | PostIndex | Unprivileged | NonTemporal
End

Datatype:
  mem_immediate = Scaled word12 | Unscaled index_mode word9
End

Datatype:
  simd_binary = Add4S | Add2D | Cmeq16B | Eor16B | Orr16B
End

Datatype:
  simd_unary = CmeqZero16B | Uminv16B | Addv4S | Addv8H | Uaddlp16B | Uadalp16B
             | Cnt8B | Addv8B
             | Rev16B | Rev32B | Rev32H | Rev64B | Rev64H | Rev64S
End

Datatype:
  simd_shift = Shl | Ushr | Sri
End

Datatype:
  simd_transfer = FmovW | FmovX | UmovB0 | UmovD1 | Dup2D | FmovToD
End

Datatype:
  bit_op = Clz | Cls | Rbit | Rev | Rev16 | Rev32
End

Datatype:
  arm64_instr =
    BranchImm bool word26
  | BCond word4 word19
  | CompareBranch bool bool word5 word19
  | TestBranch bool word6 word5 word14
  | Br word5
  | Blr word5
  | Ret word5
  | MoveWide bool word2 word2 word5 word16
  | AddImm bool bool bool bool word5 word5 word12
  | AddShift bool bool bool word2 word5 word5 word5 word6
  | AddExtend bool bool bool word3 word5 word5 word5 word3
  | AddCarry bool bool bool word5 word5 word5
  | CondCompare bool bool bool word5 word5 word4 word4
  | LogicalReg bool word2 bool word2 word5 word5 word5 word6
  | LogicalImm bool word2 bool word6 word6 word5 word5
  | VariableShift bool word2 word5 word5 word5
  | Bitfield bool word2 word5 word5 word6 word6
  | Extract bool word5 word5 word5 word6
  | Select bool word2 word5 word5 word5 word4
  | MulAdd bool bool word5 word5 word5 word5
  | MulLong bool bool word5 word5 word5 word5
  | MulHigh bool word5 word5 word5
  | Divide bool bool word5 word5 word5
  | BitOp bool bit_op word5 word5
  | PcAddress bool word5 word21
  | LoadLiteral bool word2 word5 word19
  | MemImm bool word2 word2 word5 word5 mem_immediate
  | MemReg bool word2 word2 word5 word5 word5 word3 bool
  | MemPair bool word2 bool index_mode word5 word5 word5 word7
  | MemMulti bool bool bool word5 word4 word2 word5 word5
  | MemLane bool bool bool word5 bool word3 bool word2 word5 word5
  | SimdImm bool bool word4 word8 word5
  | SimdBinary simd_binary word5 word5 word5
  | SimdUnary simd_unary word5 word5
  | Crc32 bool word2 word5 word5 word5
  | Pmull bool word5 word5 word5
  | Aes aes_op word5 word5
  | ShaThree word3 word5 word5 word5
  | ShaTwo word5 word5 word5
  | CryptoFour word2 word5 word5 word5 word5
  | Sm3Tt word2 word2 word5 word5 word5
  | CryptoThree bool word2 word5 word5 word5
  | Xar word5 word5 word5 word6
  | CryptoTwo word2 word5 word5
  | SimdTable bool word5 word5 word5
  | SimdExtract word5 word5 word5 word4
  | SimdShift simd_shift word5 word5 word7
  | SimdTransfer simd_transfer word5 word5
  | Nop
End

Datatype:
  fault_kind = Unsupported | PCAlignment | SPAlignment | Fetch | Load | Store
End

Datatype:
  arm64_result = Next 's | Fault fault_kind
End

Type step_result = ``:arm64_state arm64_result``

Definition insert_field_def:
  insert_field shift (value : 'a word) : word32 = w2w value << shift
End

Definition pair_encoding_def:
  pair_encoding base t u n imm =
    base || insert_field 0 (t:word5) || insert_field 5 (n:word5) ||
    insert_field 10 (u:word5) || insert_field 15 (imm:word7)
End

Definition flag_field_def:
  flag_field b n : word32 = if b then 1w << n else 0w
End

Definition reg_fields_def:
  reg_fields (d:word5) (n:word5) (m:word5) =
    insert_field 0 d || insert_field 5 n || insert_field 16 m
End

Definition writes_back_def:
  writes_back mode ⇔ mode = PreIndex ∨ mode = PostIndex
End

(* A general-register transfer that writes back its base register must not
   also transfer that register: the result is CONSTRAINED UNPREDICTABLE. *)
Definition writeback_ok_def:
  writeback_ok mode (n:word5) t ⇔ ¬writes_back mode ∨ n = 31w ∨ n ≠ t
End

(* size:opc of a single-register transfer. A SIMD&FP opc<1> selects the
   128-bit Q form (with size 0); a general opc of 2 or 3 sign-extends to 64 or
   32 bits, and size 3 with opc 2 is a prefetch. *)
Definition mem_opc_ok_def:
  mem_opc_ok vec (opc:word2) (size:word2) ⇔
    if vec then ¬word_bit 1 opc ∨ size = 0w else opc ≠ 3w ∨ w2n size < 2
End

Definition is_prefetch_def:
  is_prefetch vec (opc:word2) (size:word2) ⇔ ¬vec ∧ opc = 2w ∧ size = 3w
End

Definition mem_load_def:
  mem_load vec (opc:word2) ⇔ if vec then word_bit 0 opc else opc ≠ 0w
End

Definition transfer_scale_def:
  transfer_scale vec (opc:word2) (size:word2) =
    w2n size + (if vec ∧ word_bit 1 opc then 4 else 0)
End

Definition mem_base_def:
  mem_base vec (opc:word2) (size:word2) t n =
    0x38000000w || insert_field 30 size || flag_field vec 26 ||
    insert_field 22 opc || reg_fields t n 0w
End

Definition single_encoding_def:
  single_encoding vec opc size t n (Scaled imm) =
    SOME (mem_base vec opc size t n || 0x01000000w || insert_field 10 imm) ∧
  single_encoding vec opc size t n (Unscaled mode imm) =
    if mode = NonTemporal ∨ (vec ∧ mode = Unprivileged) ∨
       (is_prefetch vec opc size ∧ mode ≠ Offset) ∨
       (¬vec ∧ ¬writeback_ok mode n t) then NONE
    else
      SOME (mem_base vec opc size t n || insert_field 12 imm ||
        (case mode of PostIndex => 0x400w | Unprivileged => 0x800w
                    | PreIndex => 0xc00w | _ => 0w))
End

Definition pair_mode_bits_def:
  pair_mode_bits NonTemporal = 0w ∧
  pair_mode_bits PostIndex = 0x00800000w ∧
  pair_mode_bits Offset = 0x01000000w ∧
  pair_mode_bits PreIndex = 0x01800000w ∧
  pair_mode_bits Unprivileged = (0w:word32)
End

(* General pairs: opc 0 is 32-bit, 1 is LDPSW, 2 is 64-bit. SIMD&FP pairs:
   opc 0, 1, 2 are S, D, Q. *)
Definition pair_ok_def:
  pair_ok vec (opc:word2) load mode (t:word5) u n ⇔
    opc ≠ 3w ∧ mode ≠ Unprivileged ∧ ¬(load ∧ t = u) ∧
    (vec ∨ (writeback_ok mode n t ∧ writeback_ok mode n u ∧
            (opc = 1w ⇒ load ∧ mode ≠ NonTemporal)))
End

(* Multiple-structure transfers (LD1-LD4, ST1-ST4) take q, load, post-index,
   m, opcode, size, t and n. The opcode gives the number of registers each
   structure element spans (selem) and how many times the transfer repeats
   (rpt); one of the two is 1. *)
Definition multi_layout_def:
  multi_layout (opc:word4) =
    if opc = 0w then (1,4) else if opc = 2w then (4,1)
    else if opc = 4w then (1,3) else if opc = 6w then (3,1)
    else if opc = 7w then (1,1) else if opc = 8w then (1,2) else (2,1)
End

Definition multi_ok_def:
  multi_ok q (opc:word4) (size:word2) ⇔
    MEM (w2n opc) [0; 2; 4; 6; 7; 8; 10] ∧
    ¬(size = 3w ∧ ¬q ∧ SND (multi_layout opc) ≠ 1)
End

(* Single-structure transfers take q, load, post-index, m, R, opcode, S,
   size, t and n. opcode<2:1> = 3 replicates one element to every lane
   (LD1R-LD4R); otherwise q:S:size select the lane. *)
Definition lane_ok_def:
  lane_ok load (opc:word3) S (size:word2) ⇔
    let scale = w2n opc DIV 2 in
      if scale = 3 then load ∧ ¬S
      else if scale = 1 then ¬word_bit 0 size
      else if scale = 2 then ¬word_bit 1 size ∧ ¬(word_bit 0 size ∧ S)
      else T
End

(* Element size in bytes and lane index of a single-structure transfer. *)
Definition lane_layout_def:
  lane_layout q (opc:word3) S (size:word2) =
    let scale = w2n opc DIV 2;
        qs = (if q then 2 else 0) + (if S then 1 else 0)
    in
      if scale = 3 then (2 ** w2n size, 0)
      else if scale = 0 then (1, qs * 4 + w2n size)
      else if scale = 1 then (2, qs * 2 + w2n size DIV 2)
      else if word_bit 0 size then (8, if q then 1 else 0)
      else (4, qs)
End

(* AND, ORR, EOR and ANDS (immediate) and the bitfield moves describe their
   masks by N:imms:immr; DecodeBitMasks in the Arm ARM. *)
Definition bit_mask_len_def:
  bit_mask_len N (imms:word6) =
    if N then 6 else if ¬word_bit 5 imms then 5 else if ¬word_bit 4 imms then 4
    else if ¬word_bit 3 imms then 3 else if ¬word_bit 2 imms then 2
    else if ¬word_bit 1 imms then 1 else 0
End

Definition bit_masks_ok_def:
  bit_masks_ok N imms immediate ⇔
    let len = bit_mask_len N imms in
      0 < len ∧ ¬(immediate ∧ w2n imms MOD 2 ** len = 2 ** len - 1)
End

Definition low_mask_def:
  low_mask n : word64 = (1w << n) - 1w
End

Definition replicate_def:
  replicate esize 0 (x:word64) = 0w ∧
  replicate esize (SUC k) x = x || (replicate esize k x << esize)
End

Definition bit_masks_def:
  bit_masks N (imms:word6) (immr:word6) =
    let esize = 2 ** bit_mask_len N imms;
        s = w2n imms MOD esize;
        r = w2n immr MOD esize;
        welem = low_mask (s + 1);
        wrot = ((welem >>> r) || (welem << (esize - r))) && low_mask esize;
        telem = low_mask ((s + esize - r) MOD esize + 1)
    in (replicate esize (64 DIV esize) wrot, replicate esize (64 DIV esize) telem)
End

Definition simd_binary_base_def:
  simd_binary_base Add4S = 0x4ea08400w ∧
  simd_binary_base Add2D = 0x4ee08400w ∧
  simd_binary_base Cmeq16B = 0x6e208c00w ∧
  simd_binary_base Eor16B = 0x6e201c00w ∧
  simd_binary_base Orr16B = 0x4ea01c00w
End

Definition simd_unary_base_def:
  simd_unary_base CmeqZero16B = 0x4e209800w ∧
  simd_unary_base Uminv16B = 0x6e31a800w ∧
  simd_unary_base Addv4S = 0x4eb1b800w ∧
  simd_unary_base Addv8H = 0x4e71b800w ∧
  simd_unary_base Uaddlp16B = 0x6e202800w ∧
  simd_unary_base Uadalp16B = 0x6e206800w ∧
  simd_unary_base Cnt8B = 0x0e205800w ∧
  simd_unary_base Addv8B = 0x0e31b800w ∧
  simd_unary_base Rev16B = 0x4e201800w ∧
  simd_unary_base Rev32B = 0x6e200800w ∧
  simd_unary_base Rev32H = 0x6e600800w ∧
  simd_unary_base Rev64B = 0x4e200800w ∧
  simd_unary_base Rev64H = 0x4e600800w ∧
  simd_unary_base Rev64S = 0x4ea00800w
End

Definition simd_transfer_base_def:
  simd_transfer_base FmovW = 0x1e260000w ∧
  simd_transfer_base FmovX = 0x9e660000w ∧
  simd_transfer_base UmovB0 = 0x0e013c00w ∧
  simd_transfer_base UmovD1 = 0x4e183c00w ∧
  simd_transfer_base Dup2D = 0x4e080c00w ∧
  simd_transfer_base FmovToD = 0x9e670000w
End

Definition simd_shift_base_def:
  simd_shift_base Shl = 0x4f005400w ∧
  simd_shift_base Ushr = 0x6f000400w ∧
  simd_shift_base Sri = 0x6f004400w
End

(* The high bits of immh:immb select a 32- or 64-bit lane. *)
Definition simd_shift_imm_ok_def:
  simd_shift_imm_ok (imm:word7) ⇔ 32 ≤ w2n imm
End

Definition aes_base_def:
  aes_base Aese = 0x4e284800w ∧
  aes_base Aesd = 0x4e285800w ∧
  aes_base Aesmc = 0x4e286800w ∧
  aes_base Aesimc = 0x4e287800w
End

Definition classify_simd_def:
  classify_simd feat (w:word32) (d:word5) (n:word5) (m:word5) =
    if w && 0x9ff80c00w = 0x0f000400w then
      SOME (SimdImm (word_bit 30 w) (word_bit 29 w) (w2w (w >>> 12))
              (w2w (w >>> 11) && 0xe0w || w2w (w >>> 5) && 31w) d)
    else
      let binary = w && 0xffe0fc00w; unary = w && 0xfffffc00w;
          shift = w && 0xff80fc00w; imm : word7 = w2w (w >>> 16)
      in
      if binary = simd_binary_base Add4S then SOME (SimdBinary Add4S d n m)
      else if binary = simd_binary_base Add2D then SOME (SimdBinary Add2D d n m)
      else if binary = simd_binary_base Cmeq16B then SOME (SimdBinary Cmeq16B d n m)
      else if binary = simd_binary_base Eor16B then SOME (SimdBinary Eor16B d n m)
      else if binary = simd_binary_base Orr16B then SOME (SimdBinary Orr16B d n m)
      else if feat.pmull ∧ w && 0xbfe0fc00w = 0x0ee0e000w then
        SOME (Pmull (word_bit 30 w) d n m)
      else if feat.aes ∧ unary = aes_base Aese then SOME (Aes Aese d n)
      else if feat.aes ∧ unary = aes_base Aesd then SOME (Aes Aesd d n)
      else if feat.aes ∧ unary = aes_base Aesmc then SOME (Aes Aesmc d n)
      else if feat.aes ∧ unary = aes_base Aesimc then SOME (Aes Aesimc d n)
      else if w && 0xffe08c00w = 0x5e000000w ∧
              (if word_bit 14 w then feat.sha256 else feat.sha1) then
        SOME (ShaThree (w2w (w >>> 12)) d n m)
      else if w && 0xfffe0c00w = 0x5e280800w ∧
              (if word_bit 13 w then feat.sha256 else feat.sha1) then
        SOME (ShaTwo (w2w (w >>> 12)) d n)
      else if w && 0xff808000w = 0xce000000w ∧
              (if word_bit 22 w then feat.sm3 else feat.sha3) then
        SOME (CryptoFour (w2w (w >>> 21)) d n m (w2w (w >>> 10)))
      else if feat.sm3 ∧ w && 0xffe0c000w = 0xce408000w then
        SOME (Sm3Tt (w2w (w >>> 10)) (w2w (w >>> 12)) d n m)
      else if w && 0xffe0b000w = 0xce608000w ∧
              (if word_bit 14 w then
                 if word_bit 11 w then feat.sm4 else feat.sm3
               else if w && 0xc00w = 0xc00w then feat.sha3 else feat.sha512) then
        SOME (CryptoThree (word_bit 14 w) (w2w (w >>> 10)) d n m)
      else if feat.sha3 ∧ w && 0xffe00000w = 0xce800000w then
        SOME (Xar d n m (w2w (w >>> 10)))
      else if w && 0xfffff000w = 0xcec08000w ∧
              (if word_bit 10 w then feat.sm4 else feat.sha512) then
        SOME (CryptoTwo (w2w (w >>> 10)) d n)
      else if binary = 0x4e000000w then SOME (SimdTable F d n m)
      else if binary = 0x4e001000w then SOME (SimdTable T d n m)
      else if w && 0xffe08400w = 0x6e000000w then
        SOME (SimdExtract d n m (w2w (w >>> 11)))
      else if shift = simd_shift_base Shl ∧ simd_shift_imm_ok imm then
        SOME (SimdShift Shl d n imm)
      else if shift = simd_shift_base Ushr ∧ simd_shift_imm_ok imm then
        SOME (SimdShift Ushr d n imm)
      else if shift = simd_shift_base Sri ∧ simd_shift_imm_ok imm then
        SOME (SimdShift Sri d n imm)
      else if unary = simd_unary_base CmeqZero16B then SOME (SimdUnary CmeqZero16B d n)
      else if unary = simd_unary_base Uminv16B then SOME (SimdUnary Uminv16B d n)
      else if unary = simd_unary_base Addv4S then SOME (SimdUnary Addv4S d n)
      else if unary = simd_unary_base Addv8H then SOME (SimdUnary Addv8H d n)
      else if unary = simd_unary_base Uaddlp16B then SOME (SimdUnary Uaddlp16B d n)
      else if unary = simd_unary_base Uadalp16B then SOME (SimdUnary Uadalp16B d n)
      else if unary = simd_unary_base Cnt8B then SOME (SimdUnary Cnt8B d n)
      else if unary = simd_unary_base Addv8B then SOME (SimdUnary Addv8B d n)
      else if unary = simd_unary_base Rev16B then SOME (SimdUnary Rev16B d n)
      else if unary = simd_unary_base Rev32B then SOME (SimdUnary Rev32B d n)
      else if unary = simd_unary_base Rev32H then SOME (SimdUnary Rev32H d n)
      else if unary = simd_unary_base Rev64B then SOME (SimdUnary Rev64B d n)
      else if unary = simd_unary_base Rev64H then SOME (SimdUnary Rev64H d n)
      else if unary = simd_unary_base Rev64S then SOME (SimdUnary Rev64S d n)
      else if unary = simd_transfer_base FmovW then SOME (SimdTransfer FmovW d n)
      else if unary = simd_transfer_base FmovX then SOME (SimdTransfer FmovX d n)
      else if unary = simd_transfer_base UmovB0 then SOME (SimdTransfer UmovB0 d n)
      else if unary = simd_transfer_base UmovD1 then SOME (SimdTransfer UmovD1 d n)
      else if unary = simd_transfer_base Dup2D then SOME (SimdTransfer Dup2D d n)
      else if unary = simd_transfer_base FmovToD then SOME (SimdTransfer FmovToD d n)
      else NONE
End

Definition bit_op_base_def:
  bit_op_base (sf:bool) Clz = 0x5ac01000w ∧
  bit_op_base sf Cls = 0x5ac01400w ∧
  bit_op_base sf Rbit = 0x5ac00000w ∧
  bit_op_base sf Rev = (if sf then 0x5ac00c00w else 0x5ac00800w) ∧
  bit_op_base sf Rev16 = 0x5ac00400w ∧
  bit_op_base sf Rev32 = 0x5ac00800w
End

Definition encode_def:
  encode (BranchImm link imm) =
    SOME (0x14000000w || flag_field link 31 || insert_field 0 imm) ∧
  encode (BCond cond imm) =
    SOME (0x54000000w || insert_field 0 cond || insert_field 5 imm) ∧
  encode (CompareBranch sf nz t imm) =
    SOME (0x34000000w || flag_field sf 31 || flag_field nz 24 ||
          insert_field 0 t || insert_field 5 imm) ∧
  encode (TestBranch nz bit t imm) =
    SOME (0x36000000w || flag_field (word_bit 5 bit) 31 || flag_field nz 24 ||
          insert_field 19 (w2w bit : word5) || insert_field 0 t || insert_field 5 imm) ∧
  encode (Br n) = SOME (0xd61f0000w || insert_field 5 n) ∧
  encode (Blr n) = SOME (0xd63f0000w || insert_field 5 n) ∧
  encode (Ret n) = SOME (0xd65f0000w || insert_field 5 n) ∧
  encode (MoveWide sf opc hw d imm) =
    (if opc = 1w ∨ (¬sf ∧ word_bit 1 hw) then NONE
     else SOME (0x12800000w || flag_field sf 31 || insert_field 29 opc ||
                insert_field 21 hw || insert_field 0 d || insert_field 5 imm)) ∧
  encode (AddImm sf sub flags shift d n imm) =
    SOME (0x11000000w || flag_field sf 31 || flag_field sub 30 ||
          flag_field flags 29 || flag_field shift 22 ||
          reg_fields d n 0w || insert_field 10 imm) ∧
  encode (AddShift sf sub flags shift d n m amount) =
    (if shift = 3w ∨ (¬sf ∧ word_bit 5 amount) then NONE
     else SOME (0x0b000000w || flag_field sf 31 || flag_field sub 30 ||
                flag_field flags 29 || insert_field 22 shift ||
                reg_fields d n m || insert_field 10 amount)) ∧
  encode (AddExtend sf sub flags ext d n m amount) =
    (if 4 < w2n amount then NONE
     else SOME (0x0b200000w || flag_field sf 31 || flag_field sub 30 ||
                flag_field flags 29 || insert_field 13 ext ||
                reg_fields d n m || insert_field 10 amount)) ∧
  encode (AddCarry sf sub flags d n m) =
    SOME (0x1a000000w || flag_field sf 31 || flag_field sub 30 ||
          flag_field flags 29 || reg_fields d n m) ∧
  encode (CondCompare sf sub imm n y cond nzcv) =
    SOME (0x3a400000w || flag_field sf 31 || flag_field sub 30 ||
          flag_field imm 11 || insert_field 16 y || insert_field 5 n ||
          insert_field 12 cond || insert_field 0 nzcv) ∧
  encode (LogicalReg sf opc invert shift d n m amount) =
    (if ¬sf ∧ word_bit 5 amount then NONE
     else SOME (0x0a000000w || flag_field sf 31 || insert_field 29 opc ||
                flag_field invert 21 || insert_field 22 shift ||
                reg_fields d n m || insert_field 10 amount)) ∧
  encode (LogicalImm sf opc N immr imms d n) =
    (if (¬sf ∧ N) ∨ ¬bit_masks_ok N imms T then NONE
     else SOME (0x12000000w || flag_field sf 31 || insert_field 29 opc ||
                flag_field N 22 || insert_field 16 immr || insert_field 10 imms ||
                reg_fields d n 0w)) ∧
  encode (VariableShift sf shift d n m) =
    SOME (0x1ac02000w || flag_field sf 31 ||
          insert_field 10 shift || reg_fields d n m) ∧
  encode (Bitfield sf opc d n immr imms) =
    (if opc = 3w ∨ (¬sf ∧ (word_bit 5 immr ∨ word_bit 5 imms)) then NONE
     else SOME (0x13000000w || flag_field sf 31 || insert_field 29 opc ||
                flag_field sf 22 || reg_fields d n 0w ||
                insert_field 16 immr || insert_field 10 imms)) ∧
  encode (Extract sf d n m amount) =
    (if ¬sf ∧ word_bit 5 amount then NONE
     else SOME (0x13800000w || flag_field sf 31 || flag_field sf 22 ||
                reg_fields d n m || insert_field 10 amount)) ∧
  encode (Select sf opc d n m cond) =
    SOME (0x1a800000w || flag_field sf 31 || flag_field (word_bit 1 opc) 30 ||
          flag_field (word_bit 0 opc) 10 || reg_fields d n m ||
          insert_field 12 cond) ∧
  encode (MulAdd sf sub d n m a) =
    SOME (0x1b000000w || flag_field sf 31 || flag_field sub 15 ||
          insert_field 10 a || reg_fields d n m) ∧
  encode (MulLong unsigned sub d n m a) =
    SOME (0x9b200000w || flag_field unsigned 23 || flag_field sub 15 ||
          insert_field 10 a || reg_fields d n m) ∧
  encode (MulHigh signed d n m) =
    SOME (0x9b407c00w || flag_field (¬signed) 23 || reg_fields d n m) ∧
  encode (Divide sf signed d n m) =
    SOME (0x1ac00800w || flag_field sf 31 || flag_field signed 10 ||
          reg_fields d n m) ∧
  encode (BitOp sf op d n) =
    (if op = Rev32 ∧ ¬sf then NONE
     else SOME (bit_op_base sf op || flag_field sf 31 || reg_fields d n 0w)) ∧
  encode (PcAddress page d imm) =
    SOME (0x10000000w || flag_field page 31 ||
          insert_field 29 (w2w imm : word2) || insert_field 5 (imm >>> 2) ||
          insert_field 0 d) ∧
  encode (LoadLiteral vec opc t imm) =
    (if vec ∧ opc = 3w then NONE
     else SOME (0x18000000w || insert_field 30 opc || flag_field vec 26 ||
                insert_field 5 imm || insert_field 0 t)) ∧
  encode (MemImm vec opc size t n imm) =
    (if mem_opc_ok vec opc size then single_encoding vec opc size t n imm
     else NONE) ∧
  encode (MemReg vec opc size t n m ext scaled) =
    (if ¬mem_opc_ok vec opc size ∨ ¬word_bit 1 ext then NONE
     else SOME (mem_base vec opc size t n || 0x00200800w ||
                insert_field 16 m || insert_field 13 ext || flag_field scaled 12)) ∧
  encode (MemPair vec opc load mode t u n imm) =
    (if pair_ok vec opc load mode t u n then
       SOME (pair_encoding (0x28000000w || insert_field 30 opc || flag_field vec 26 ||
                            pair_mode_bits mode || flag_field load 22) t u n imm)
     else NONE) ∧
  encode (MemMulti q load post m opc size t n) =
    (if multi_ok q opc size ∧ (post ∨ m = 0w) then
       SOME (0x0c000000w || flag_field q 30 || flag_field post 23 ||
             flag_field load 22 || insert_field 16 m || insert_field 12 opc ||
             insert_field 10 size || reg_fields t n 0w)
     else NONE) ∧
  encode (MemLane q load post m r opc S size t n) =
    (if lane_ok load opc S size ∧ (post ∨ m = 0w) then
       SOME (0x0d000000w || flag_field q 30 || flag_field post 23 ||
             flag_field load 22 || flag_field r 21 || insert_field 16 m ||
             insert_field 13 opc || flag_field S 12 || insert_field 10 size ||
             reg_fields t n 0w)
     else NONE) ∧
  encode (SimdImm q op cmode imm d) =
    (if op ∧ cmode = 15w ∧ ¬q then NONE
     else SOME (0x0f000400w || flag_field q 30 || flag_field op 29 ||
                insert_field 16 (imm >>> 5) || insert_field 12 cmode ||
                insert_field 5 (imm && 31w) || insert_field 0 d)) ∧
  encode (SimdBinary op d n m) =
    SOME (simd_binary_base op || reg_fields d n m) ∧
  encode (SimdUnary op d n) =
    SOME (simd_unary_base op || reg_fields d n 0w) ∧
  encode (Crc32 castagnoli size d n m) =
    SOME (0x1ac04000w || flag_field (size = 3w) 31 || flag_field castagnoli 12 ||
          insert_field 10 size || reg_fields d n m) ∧
  encode (Pmull high d n m) =
    SOME (0x0ee0e000w || flag_field high 30 || reg_fields d n m) ∧
  encode (Aes op d n) = SOME (aes_base op || reg_fields d n 0w) ∧
  encode (ShaThree opc d n m) =
    (if w2n opc < 7 then SOME (0x5e000000w || insert_field 12 opc || reg_fields d n m)
     else NONE) ∧
  encode (ShaTwo opc d n) =
    (if w2n opc < 3 then SOME (0x5e280800w || insert_field 12 opc || reg_fields d n 0w)
     else NONE) ∧
  encode (CryptoFour op0 d n m a) =
    (if op0 = 3w then NONE
     else SOME (0xce000000w || insert_field 21 op0 || insert_field 10 a ||
                reg_fields d n m)) ∧
  encode (Sm3Tt opc imm2 d n m) =
    SOME (0xce408000w || insert_field 12 imm2 || insert_field 10 opc ||
          reg_fields d n m) ∧
  encode (CryptoThree sm opc d n m) =
    (if sm ∧ opc = 3w then NONE
     else SOME (0xce608000w || flag_field sm 14 || insert_field 10 opc ||
                reg_fields d n m)) ∧
  encode (Xar d n m imm) =
    SOME (0xce800000w || insert_field 10 imm || reg_fields d n m) ∧
  encode (CryptoTwo opc d n) =
    (if w2n opc < 2 then SOME (0xcec08000w || insert_field 10 opc || reg_fields d n 0w)
     else NONE) ∧
  encode (SimdTable extend d n m) =
    SOME (0x4e000000w || flag_field extend 12 || reg_fields d n m) ∧
  encode (SimdExtract d n m imm) =
    SOME (0x6e000000w || reg_fields d n m || insert_field 11 imm) ∧
  encode (SimdShift op d n imm) =
    (if simd_shift_imm_ok imm then
       SOME (simd_shift_base op || reg_fields d n 0w || insert_field 16 imm)
     else NONE) ∧
  encode (SimdTransfer op d n) =
    SOME (simd_transfer_base op || reg_fields d n 0w) ∧
  encode Nop = SOME 0xd503201fw
End

Definition classify_def:
  classify feat (w:word32) =
    let d : word5 = w2w w;
        n : word5 = w2w (w >>> 5);
        m : word5 = w2w (w >>> 16);
        u : word5 = w2w (w >>> 10);
        disp : word19 = w2w (w >>> 5);
        offset : word7 = w2w (w >>> 15);
        sf = word_bit 31 w;
        sub = word_bit 30 w;
        flags = word_bit 29 w;
        load = word_bit 22 w;
        size : word2 = w2w (w >>> 30);
        shift : word2 = w2w (w >>> 22);
        amount : word6 = w2w (w >>> 10);
        ext : word3 = w2w (w >>> 13);
        opc : word2 = w2w (w >>> 29);
        mem_opc : word2 = w2w (w >>> 22);
        immr : word6 = w2w (w >>> 16);
        imms : word6 = w2w (w >>> 10);
        vec = word_bit 26 w;
        unary = w && 0x7ffffc00w
    in
      if w && 0x7c000000w = 0x14000000w then SOME (BranchImm sf (w2w w))
      else if w && 0xff000010w = 0x54000000w then SOME (BCond (w2w w) disp)
      else if w && 0x7e000000w = 0x34000000w then
        SOME (CompareBranch sf (word_bit 24 w) d disp)
      else if w && 0x7e000000w = 0x36000000w then
        SOME (TestBranch (word_bit 24 w)
          ((if sf then 32w else 0w) || w2w (w2w (w >>> 19) : word5))
          d (w2w (w >>> 5)))
      else if w && 0xfffffc1fw = 0xd61f0000w then SOME (Br n)
      else if w && 0xfffffc1fw = 0xd63f0000w then SOME (Blr n)
      else if w && 0xfffffc1fw = 0xd65f0000w then SOME (Ret n)
      else if w && 0x1f800000w = 0x12800000w then
        SOME (MoveWide sf opc (w2w (w >>> 21)) d (w2w (w >>> 5)))
      else if w && 0x1f800000w = 0x12000000w then
        SOME (LogicalImm sf opc load immr imms d n)
      else if w && 0x1f800000w = 0x11000000w then
        SOME (AddImm sf sub flags load d n (w2w (w >>> 10)))
      else if w && 0x1f200000w = 0x0b000000w then
        SOME (AddShift sf sub flags shift d n m amount)
      else if w && 0x1fe00000w = 0x0b200000w then
        SOME (AddExtend sf sub flags ext d n m (w2w (w >>> 10)))
      else if w && 0x1fe0fc00w = 0x1a000000w then SOME (AddCarry sf sub flags d n m)
      else if w && 0x3fe00410w = 0x3a400000w then
        SOME (CondCompare sf sub (word_bit 11 w) n m (w2w (w >>> 12)) (w2w w))
      else if w && 0x1f000000w = 0x0a000000w then
        SOME (LogicalReg sf (w2w (w >>> 29)) (word_bit 21 w) shift d n m amount)
      else if w && 0x7fe0f000w = 0x1ac02000w then
        SOME (VariableShift sf (w2w (w >>> 10)) d n m)
      else if w && 0x1f800000w = 0x13000000w then SOME (Bitfield sf opc d n immr imms)
      else if w && 0x7fa00000w = 0x13800000w then SOME (Extract sf d n m amount)
      else if w && 0x3fe00800w = 0x1a800000w then
        SOME (Select sf ((if sub then 2w else 0w) || (w2w u && 1w))
          d n m (w2w (w >>> 12)))
      else if w && 0x7fe00000w = 0x1b000000w then
        SOME (MulAdd sf (word_bit 15 w) d n m u)
      else if w && 0xff600000w = 0x9b200000w then
        SOME (MulLong (word_bit 23 w) (word_bit 15 w) d n m u)
      else if w && 0xff60fc00w = 0x9b407c00w then
        SOME (MulHigh (¬word_bit 23 w) d n m)
      else if w && 0x7fe0f800w = 0x1ac00800w then
        SOME (Divide sf (word_bit 10 w) d n m)
      else if feat.crc32 ∧ w && 0x7fe0e000w = 0x1ac04000w then
        SOME (Crc32 (word_bit 12 w) (w2w (w >>> 10)) d n m)
      else if unary = bit_op_base sf Clz then SOME (BitOp sf Clz d n)
      else if unary = bit_op_base sf Cls then SOME (BitOp sf Cls d n)
      else if unary = bit_op_base sf Rbit then SOME (BitOp sf Rbit d n)
      else if unary = bit_op_base sf Rev then SOME (BitOp sf Rev d n)
      else if unary = bit_op_base sf Rev16 then SOME (BitOp sf Rev16 d n)
      else if unary = bit_op_base sf Rev32 then SOME (BitOp sf Rev32 d n)
      else if w && 0x1f000000w = 0x10000000w then
        SOME (PcAddress sf d ((w2w disp : word21) << 2 || w2w (w2w (w >>> 29) : word2)))
      else if vec ∧ ¬feat.asimd ∧ w && 0x0a000000w = 0x08000000w then NONE
      else if w && 0xbf200000w = 0x0c000000w then
        SOME (MemMulti sub load (word_bit 23 w) m (w2w (w >>> 12)) (w2w (w >>> 10)) d n)
      else if w && 0xbf000000w = 0x0d000000w then
        SOME (MemLane sub load (word_bit 23 w) m (word_bit 21 w) (w2w (w >>> 13))
                (word_bit 12 w) (w2w (w >>> 10)) d n)
      else if w && 0x3b000000w = 0x18000000w then
        SOME (LoadLiteral vec size d disp)
      else if w && 0x3b000000w = 0x39000000w then
        SOME (MemImm vec mem_opc size d n (Scaled (w2w (w >>> 10))))
      else if w && 0x3b200c00w = 0x38200800w then
        SOME (MemReg vec mem_opc size d n m ext (word_bit 12 w))
      else if w && 0x3b200000w = 0x38000000w then
        SOME (MemImm vec mem_opc size d n
          (Unscaled (if word_bit 11 w then
                       if word_bit 10 w then PreIndex else Unprivileged
                     else if word_bit 10 w then PostIndex else Offset) (w2w (w >>> 12))))
      else if w && 0x3a000000w = 0x28000000w then
        SOME (MemPair vec size load
          (if word_bit 24 w then if word_bit 23 w then PreIndex else Offset
           else if word_bit 23 w then PostIndex else NonTemporal)
          d u n offset)
      else if w = 0xd503201fw then SOME Nop
      else if feat.asimd then classify_simd feat w d n m
      else NONE
End

Definition decode_def:
  decode feat w =
    case classify feat w of
      NONE => NONE
    | SOME i => if encode i = SOME w then SOME i else NONE
End

Theorem encode_of_decode:
  ∀feat w i. decode feat w = SOME i ⇒ encode i = SOME w
Proof
  rw[decode_def] >> Cases_on `classify feat w` >> gvs[AllCaseEqs()]
QED

Definition gpr_def:
  gpr ops s r = if r = 31w then 0w else ops.get_reg s.regs r
End

Definition base_reg_def:
  base_reg ops s r = if r = 31w then s.sp else ops.get_reg s.regs r
End

Definition set_gpr_def:
  set_gpr ops r value s =
    if r = 31w then s else s with regs := ops.put_reg r value s.regs
End

Definition set_base_def:
  set_base ops r value s =
    if r = 31w then s with sp := value else set_gpr ops r value s
End

Definition read_bytes_def:
  read_bytes ops 0 s a = 0w ∧
  read_bytes ops (SUC n) s a =
    (w2w (ops.get_byte s.mem a) : word128) ||
    (read_bytes ops n s (a + 1w) << 8)
End

Definition write_bytes_def:
  write_bytes ops 0 a (v:word128) s = s ∧
  write_bytes ops (SUC n) a v s =
    write_bytes ops n (a + 1w) (v >>> 8)
      (s with mem := ops.put_byte a (w2w v) s.mem)
End

Datatype:
  access = Read | Write | Execute
End

Definition allowed_def:
  allowed Read p = p.read ∧
  allowed Write p = (p.read ∧ p.write ∧ ¬p.execute) ∧
  allowed Execute p = (p.read ∧ ¬p.write ∧ p.execute)
End

Definition access_ok_def:
  (access_ok ops access 0 s a ⇔ T) ∧
  (access_ok ops access (SUC n) s a ⇔
    allowed access (ops.get_perm s.perms a) ∧
    access_ok ops access n s (a + 1w))
End

Definition check_sp_def:
  check_sp r a ⇔ r ≠ 31w ∨ (a && 15w : word64) = 0w
End

Definition advance_def:
  advance s = s with pc := s.pc + 4w
End

Definition branch_def:
  branch (offset:word64) s = s with pc := s.pc + (offset << 2)
End

Definition condition_holds_def:
  condition_holds (cond:word4) (n,z,c,v) =
    let group = w2n cond DIV 2;
        holds = if group = 0 then z else if group = 1 then c
                else if group = 2 then n else if group = 3 then v
                else if group = 4 then c ∧ ¬z else if group = 5 then n = v
                else if group = 6 then ¬z ∧ n = v else T
    in if group = 7 then T else holds ≠ word_bit 0 cond
End

Definition lane_size_def:
  lane_size sf = if sf then 64 else 32
End

Definition lane_def:
  lane sf (v:word64) : word64 = if sf then v else w2w (w2w v : word32)
End

Definition signed_lane_def:
  signed_lane sf (v:word64) : word64 = if sf then v else sw2sw (w2w v : word32)
End

Definition extend_reg_def:
  extend_reg (ext:word3) (x:word64) : word64 =
    if ext = 0w then w2w (w2w x : word8)
    else if ext = 1w then w2w (w2w x : word16)
    else if ext = 2w then w2w (w2w x : word32)
    else if ext = 4w then sw2sw (w2w x : word8)
    else if ext = 5w then sw2sw (w2w x : word16)
    else if ext = 6w then sw2sw (w2w x : word32)
    else x
End

Definition shift_reg_def:
  shift_reg sf (shift:word2) (amount:num) (x:word64) =
    let x = lane sf x in
      lane sf (if shift = 0w then x << amount
               else if shift = 1w then x >>> amount
               else if shift = 2w then signed_lane sf x >> amount
               else (x >>> amount) || (x << (lane_size sf - amount)))
End

Definition result_flags_def:
  result_flags ((r:'a word),c,v) = (word_msb r, r = 0w, c, v)
End

Definition arm_add_with_carry_def:
  arm_add_with_carry sf (x:word64) (y:word64) carry =
    if sf then
      let sum = words$add_with_carry (x,y,carry) in (FST sum,result_flags sum)
    else
      let sum = words$add_with_carry (w2w x : word32,w2w y,carry)
      in (w2w (FST sum),result_flags sum)
End

Definition write_arith_def:
  write_arith (ops:('g,'m,'p,'v) arm64_storage) base sf sub flags carry d x y
      (s:('g,'m,'p,'v) arm64_machine) =
    let (v,nzcv) = arm_add_with_carry sf x (if sub then ¬y else y) carry;
        t = if flags then s with nzcv := nzcv else s
    in advance (if base ∧ ¬flags then set_base ops d v t else set_gpr ops d v t)
End

(* ROR within the 32- or 64-bit lane. *)
Definition rotate_lane_def:
  rotate_lane sf r (x:word64) : word64 =
    if sf then x #>> r else w2w ((w2w x : word32) #>> r)
End

(* SBFM (opc 0), BFM (opc 1) and UBFM (opc 2). *)
Definition bitfield_value_def:
  bitfield_value sf (opc:word2) (immr:word6) (imms:word6) (dst:word64) src =
    let (wmask,tmask) = bit_masks sf imms immr;
        dst = if opc = 1w then dst else 0w;
        bot = (dst && ¬wmask) || (rotate_lane sf (w2n immr) src && wmask);
        top = if opc = 0w then (if word_bit (w2n imms) src then ¬0w else 0w) else dst
    in lane sf ((top && ¬tmask) || (bot && tmask))
End

Definition logical_value_def:
  logical_value sf (opc:word2) (x:word64) y =
    lane sf (if opc = 1w then x || y else if opc = 2w then x ?? y else x && y)
End

(* ANDS and BICS (opc 3) set N and Z from the result and clear C and V. *)
Definition logical_flags_def:
  logical_flags sf (opc:word2) (v:word64) s =
    if opc = 3w then s with nzcv := (word_bit (lane_size sf - 1) v,v = 0w,F,F)
    else s
End

Definition indexed_addr_def:
  indexed_addr mode (base:word64) offset =
    if mode = PostIndex then base else base + offset
End

Definition finish_mem_def:
  finish_mem (ops:('g,'m,'p,'v) arm64_storage) mode n (base:word64) offset
      (s:('g,'m,'p,'v) arm64_machine) =
    advance (if writes_back mode then set_base ops n (base + offset) s else s)
End

(* opc 2 sign-extends to 64 bits; opc 3 sign-extends to 32 bits. *)
Definition load_extend_def:
  load_extend (opc:word2) bytes (v:word128) : word64 =
    let x : word64 = w2w v;
        sx = if word_bit (8 * bytes - 1) x then x || ¬low_mask (8 * bytes) else x
    in if opc = 2w then sx else if opc = 3w then w2w (w2w sx : word32) else x
End

Definition put_loaded_def:
  put_loaded (ops:('g,'m,'p,'v) arm64_storage) vec t (v:word128)
      (s:('g,'m,'p,'v) arm64_machine) =
    if vec then s with vregs := ops.put_vec t v s.vregs
    else set_gpr ops t (w2w v) s
End

Definition stored_value_def:
  stored_value (ops:('g,'m,'p,'v) arm64_storage) vec t
      (s:('g,'m,'p,'v) arm64_machine) : word128 =
    if vec then ops.get_vec s.vregs t else w2w (gpr ops s t)
End

Definition execute_mem_def:
  execute_mem (ops:('g,'m,'p,'v) arm64_storage) vec opc size mode t n offset
      (s:('g,'m,'p,'v) arm64_machine) =
    let base = base_reg ops s n;
        a = indexed_addr mode base offset;
        bytes = 2 ** transfer_scale vec opc size
    in
      if is_prefetch vec opc size then Next (advance s)
      else if ¬check_sp n base then Fault SPAlignment
      else if mem_load vec opc then
        if access_ok ops Read bytes s a then
          let v = read_bytes ops bytes s a in
          Next (finish_mem ops mode n base offset
            (put_loaded ops vec t (if vec then v else w2w (load_extend opc bytes v)) s))
        else Fault Load
      else if access_ok ops Write bytes s a then
        Next (finish_mem ops mode n base offset
          (write_bytes ops bytes a (stored_value ops vec t s) s))
      else Fault Store
End

(* LDPSW (general opc 1) sign-extends each word. *)
Definition pair_value_def:
  pair_value vec (opc:word2) (v:word128) =
    if ¬vec ∧ opc = 1w then w2w (load_extend 2w 4 v) else v
End

Definition execute_pair_def:
  execute_pair (ops:('g,'m,'p,'v) arm64_storage) vec (opc:word2) load mode t u n
      (imm:word7) (s:('g,'m,'p,'v) arm64_machine) =
    let base = base_reg ops s n;
        scale = if vec then 2 + w2n opc else if opc = 2w then 3 else 2;
        bytes = 2 ** scale;
        offset = (sw2sw imm : word64) << scale;
        a = indexed_addr mode base offset;
        b = a + n2w bytes
    in
      if ¬check_sp n base then Fault SPAlignment
      else if load then
        if access_ok ops Read (2 * bytes) s a then
          Next (finish_mem ops mode n base offset
            (put_loaded ops vec u (pair_value vec opc (read_bytes ops bytes s b))
              (put_loaded ops vec t (pair_value vec opc (read_bytes ops bytes s a)) s)))
        else Fault Load
      else if access_ok ops Write (2 * bytes) s a then
        Next (finish_mem ops mode n base offset
          (write_bytes ops bytes b (stored_value ops vec u s)
            (write_bytes ops bytes a (stored_value ops vec t s) s)))
      else Fault Store
End

(* elems elements of the given byte width, stride bytes apart from a; element 0
   occupies the least significant bits. A stride of zero replicates one
   element. *)
Definition gather_def:
  gather ops 0 bytes stride s (a:word64) = (0w:word128) ∧
  gather ops (SUC elems) bytes stride s a =
    read_bytes ops bytes s a ||
    (gather ops elems bytes stride s (a + n2w stride) << (8 * bytes))
End

Definition scatter_def:
  scatter ops 0 bytes stride (a:word64) (v:word128) s = s ∧
  scatter ops (SUC elems) bytes stride a v s =
    scatter ops elems bytes stride (a + n2w stride) (v >>> (8 * bytes))
      (write_bytes ops bytes a v s)
End

(* Load registers t, ..., t + k - 1, the j-th from elems elements starting
   j * gap bytes past a. Writing a 64-bit arrangement clears the upper half. *)
Definition load_vectors_def:
  load_vectors ops 0 t gap elems bytes stride (a:word64) s = s ∧
  load_vectors ops (SUC k) t gap elems bytes stride a s =
    load_vectors ops k t gap elems bytes stride a
      (s with vregs := ops.put_vec (t + n2w k)
         (gather ops elems bytes stride s (a + n2w (k * gap))) s.vregs)
End

Definition store_vectors_def:
  store_vectors ops 0 t gap elems bytes stride shift (a:word64) s = s ∧
  store_vectors ops (SUC k) t gap elems bytes stride shift a s =
    store_vectors ops k t gap elems bytes stride shift a
      (scatter ops elems bytes stride (a + n2w (k * gap))
         (ops.get_vec s.vregs (t + n2w k) >>> shift) s)
End

(* Replace lane index of registers t, ..., t + k - 1 with consecutive
   elements from a. *)
Definition load_lanes_def:
  load_lanes ops 0 t bytes index (a:word64) s = s ∧
  load_lanes ops (SUC k) t bytes index a s =
    let shift = 8 * bytes * index;
        mask : word128 = ((1w << (8 * bytes)) - 1w) << shift;
        r = t + n2w k
    in load_lanes ops k t bytes index a
         (s with vregs := ops.put_vec r
            ((ops.get_vec s.vregs r && ¬mask) ||
             (read_bytes ops bytes s (a + n2w (k * bytes)) << shift)) s.vregs)
End

(* Post-index register 31 adds the transfer size. *)
Definition structure_offset_def:
  structure_offset ops s (m:word5) total : word64 =
    if m = 31w then n2w total else gpr ops s m
End

Definition execute_multi_def:
  execute_multi (ops:('g,'m,'p,'v) arm64_storage) q load post m opc (size:word2) t n
      (s:('g,'m,'p,'v) arm64_machine) =
    let (rpt,selem) = multi_layout opc;
        bytes = 2 ** w2n size;
        elems = (if q then 16 else 8) DIV bytes;
        total = rpt * selem * elems * bytes;
        gap = if selem = 1 then elems * bytes else bytes;
        stride = selem * bytes;
        base = base_reg ops s n;
        mode = if post then PostIndex else Offset;
        offset = structure_offset ops s m total
    in
      if ¬check_sp n base then Fault SPAlignment
      else if load then
        if access_ok ops Read total s base then
          Next (finish_mem ops mode n base offset
            (load_vectors ops (rpt * selem) t gap elems bytes stride base s))
        else Fault Load
      else if access_ok ops Write total s base then
        Next (finish_mem ops mode n base offset
          (store_vectors ops (rpt * selem) t gap elems bytes stride 0 base s))
      else Fault Store
End

Definition execute_lane_def:
  execute_lane (ops:('g,'m,'p,'v) arm64_storage) q load post m r (opc:word3) S size t n
      (s:('g,'m,'p,'v) arm64_machine) =
    let (bytes,index) = lane_layout q opc S size;
        selem = 2 * (w2n opc MOD 2) + (if r then 2 else 1);
        total = selem * bytes;
        base = base_reg ops s n;
        mode = if post then PostIndex else Offset;
        offset = structure_offset ops s m total
    in
      if ¬check_sp n base then Fault SPAlignment
      else if load then
        if access_ok ops Read total s base then
          Next (finish_mem ops mode n base offset
            (if w2n opc DIV 2 = 3 then
               load_vectors ops selem t bytes ((if q then 16 else 8) DIV bytes) bytes 0 base s
             else load_lanes ops selem t bytes index base s))
        else Fault Load
      else if access_ok ops Write total s base then
        Next (finish_mem ops mode n base offset
          (store_vectors ops selem t bytes 1 bytes 0 (8 * bytes * index) base s))
      else Fault Store
End

(* AdvSIMDExpandImm in the Arm ARM. *)
Definition simd_expand_imm_def:
  simd_expand_imm op (cmode:word4) (imm8:word8) : word64 =
    let x : word64 = w2w imm8; c = w2n cmode DIV 2 in
      if c < 4 then replicate 32 2 (x << (8 * c))
      else if c < 6 then replicate 16 4 (x << (8 * (c - 4)))
      else if c = 6 then
        replicate 32 2 (if word_bit 0 cmode then (x << 16) || 0xffffw
                        else (x << 8) || 0xffw)
      else if ¬word_bit 0 cmode then
        if op then
          FOLDL (λacc i. if word_bit i imm8 then acc || (0xffw << (8 * i)) else acc)
            0w [0; 1; 2; 3; 4; 5; 6; 7]
        else replicate 8 8 x
      else
        let a = word_bit 7 imm8; b = word_bit 6 imm8; low : word64 = x && 63w in
        if op then
          (if a then 1w << 63 else 0w) || (if b then 0x3fc0w << 48 else 1w << 62) ||
          (low << 48)
        else
          replicate 32 2 ((if a then 1w << 31 else 0w) ||
                          (if b then 0x3e0w << 20 else 1w << 30) || (low << 19))
End

(* MOVI, MVNI, ORR, BIC and FMOV (vector, immediate). *)
Definition simd_imm_value_def:
  simd_imm_value q op (cmode:word4) imm8 (old:word128) : word128 =
    let imm = simd_expand_imm op cmode imm8;
        imm = (w2w imm : word128) || (if q then w2w imm << 64 else 0w);
        width : word128 = if q then ¬0w else w2w (¬0w : word64)
    in
      if 12 ≤ w2n cmode ∨ ¬word_bit 0 cmode then
        (if op ∧ w2n cmode < 14 then ¬imm else imm) && width
      else if op then old && ¬imm && width
      else (old || imm) && width
End

(* Lane zero occupies the least significant bits of a vector register. *)
Definition simd_add32_def:
  simd_add32 0 (x:word128) (y:word128) = (0w:word128) ∧
  simd_add32 (SUC n) x y =
    w2w ((w2w x : word32) + w2w y) ||
    (simd_add32 n (x >>> 32) (y >>> 32) << 32)
End

Definition simd_sum32_def:
  simd_sum32 0 (x:word128) = (0w:word32) ∧
  simd_sum32 (SUC n) x = w2w x + simd_sum32 n (x >>> 32)
End

Definition simd_sum16_def:
  simd_sum16 0 (x:word128) = (0w:word16) ∧
  simd_sum16 (SUC n) x = w2w x + simd_sum16 n (x >>> 16)
End

Definition simd_add64_def:
  simd_add64 (x:word128) (y:word128) =
    w2w ((w2w x : word64) + w2w y) ||
    (((x >>> 64) + (y >>> 64)) << 64)
End

Definition simd_cmeq8_def:
  simd_cmeq8 0 (x:word128) (y:word128) = (0w:word128) ∧
  simd_cmeq8 (SUC n) x y =
    (if (w2w x : word8) = w2w y then 255w else 0w) ||
    (simd_cmeq8 n (x >>> 8) (y >>> 8) << 8)
End

Definition simd_min8_def:
  simd_min8 0 (x:word128) = (255w:word8) ∧
  simd_min8 (SUC n) x =
    let lo : word8 = w2w x; hi = simd_min8 n (x >>> 8)
    in if lo <+ hi then lo else hi
End

Definition simd_pair_sum_def:
  simd_pair_sum 0 (x:word128) (acc:word128) = (0w:word128) ∧
  simd_pair_sum (SUC n) x acc =
    w2w ((w2w acc : word16) +
         w2w (w2w x : word8) + w2w (w2w (x >>> 8) : word8)) ||
    (simd_pair_sum n (x >>> 16) (acc >>> 16) << 16)
End

Definition simd_binary_value_def:
  simd_binary_value Add4S x y = simd_add32 4 x y ∧
  simd_binary_value Add2D x y = simd_add64 x y ∧
  simd_binary_value Cmeq16B x y = simd_cmeq8 16 x y ∧
  simd_binary_value Eor16B x y = x ?? y ∧
  simd_binary_value Orr16B x y = x || y
End

Definition reverse_bytes_def:
  reverse_bytes 0 x = (0w:word64) ∧
  reverse_bytes (SUC n) x =
    (reverse_bytes n (x >>> 8)) || ((x && 255w) << (8*n))
End

Definition leading_zeros_def:
  leading_zeros 0 (x:word64) = 0 ∧
  leading_zeros (SUC n) x = if word_bit n x then 0 else SUC (leading_zeros n x)
End

(* Reverse the bytes of each of the low k groups of the given byte width. *)
Definition reverse_groups_def:
  reverse_groups bytes 0 (x:word64) = 0w ∧
  reverse_groups bytes (SUC k) x =
    reverse_bytes bytes x || (reverse_groups bytes k (x >>> (8 * bytes)) << (8 * bytes))
End

(* CLS counts the bits below the sign bit that equal it. *)
Definition bit_op_value_def:
  bit_op_value sf Clz x = (n2w (leading_zeros (lane_size sf) x) : word64) ∧
  bit_op_value sf Cls x = n2w (leading_zeros (lane_size sf - 1) (x ?? (x >>> 1))) ∧
  bit_op_value sf Rbit x = n2w (BIT_REVERSE (lane_size sf) (w2n x)) ∧
  bit_op_value sf Rev x = reverse_bytes (if sf then 8 else 4) x ∧
  bit_op_value sf Rev16 x = reverse_groups 2 (if sf then 4 else 2) x ∧
  bit_op_value sf Rev32 x = reverse_groups 4 2 x
End

Definition simd_count_bytes_def:
  simd_count_bytes 0 (x:word128) = (0w:word128) ∧
  simd_count_bytes (SUC n) x =
    n2w (bit_count (w2w x : word8)) || (simd_count_bytes n (x >>> 8) << 8)
End

Definition simd_sum8_def:
  simd_sum8 0 (x:word128) = (0w:word8) ∧
  simd_sum8 (SUC n) x = w2w x + simd_sum8 n (x >>> 8)
End

Definition simd_table_def:
  simd_table 0 (table:word128) indices old = (0w:word128) ∧
  simd_table (SUC n) table indices old =
    (let index = w2n (w2w indices : word8);
         value = if index < 16 then table >>> (8 * index) else old
     in (value && 255w) ||
        (simd_table n table (indices >>> 8) (old >>> 8) << 8))
End

Definition simd_ext_def:
  simd_ext bytes (lo:word128) (hi:word128) =
    (lo >>> (8 * bytes)) || (hi << (128 - 8 * bytes))
End

Definition simd_lane_mask_def:
  simd_lane_mask bits : word128 = (1w << bits) - 1w
End

(* Reverse the order of elements within each group. *)
Definition simd_reverse_def:
  simd_reverse 0 group width (x:word128) = (0w:word128) ∧
  simd_reverse (SUC n) group width x =
    (let i = n DIV group * group + (group - 1 - n MOD group);
         v = (x >>> (width * i)) && simd_lane_mask width
     in simd_reverse n group width x || (v << (width * n)))
End

Definition simd_shift_lane_def:
  simd_shift_lane Shl width amount (x:word128) old =
    (x << amount) && simd_lane_mask width ∧
  simd_shift_lane Ushr width amount x old =
    (x && simd_lane_mask width) >>> amount ∧
  simd_shift_lane Sri width amount x old =
    (let mask = simd_lane_mask width in
       ((x && mask) >>> amount) || (old && (mask << (width - amount)) && mask))
End

Definition simd_shift_lanes_def:
  simd_shift_lanes 0 op width amount (x:word128) old = (0w:word128) ∧
  simd_shift_lanes (SUC n) op width amount x old =
    simd_shift_lane op width amount x old ||
    (simd_shift_lanes n op width amount (x >>> width) (old >>> width) << width)
End

Definition simd_shift_value_def:
  simd_shift_value op (imm:word7) x old =
    (let bits = w2n imm; width = if bits < 64 then 32 else 64;
         amount = if op = Shl then bits - width else 2 * width - bits
     in simd_shift_lanes (128 DIV width) op width amount x old)
End

Definition simd_unary_value_def:
  simd_unary_value CmeqZero16B x acc = simd_cmeq8 16 x 0w ∧
  simd_unary_value Uminv16B x acc = (w2w (simd_min8 16 x) : word128) ∧
  simd_unary_value Addv4S x acc = w2w (simd_sum32 4 x) ∧
  simd_unary_value Addv8H x acc = w2w (simd_sum16 8 x) ∧
  simd_unary_value Uaddlp16B x acc = simd_pair_sum 8 x 0w ∧
  simd_unary_value Uadalp16B x acc = simd_pair_sum 8 x acc ∧
  simd_unary_value Cnt8B x acc = simd_count_bytes 8 x ∧
  simd_unary_value Addv8B x acc = w2w (simd_sum8 8 x) ∧
  simd_unary_value Rev16B x acc = simd_reverse 16 2 8 x ∧
  simd_unary_value Rev32B x acc = simd_reverse 16 4 8 x ∧
  simd_unary_value Rev32H x acc = simd_reverse 8 2 16 x ∧
  simd_unary_value Rev64B x acc = simd_reverse 16 8 8 x ∧
  simd_unary_value Rev64H x acc = simd_reverse 8 4 16 x ∧
  simd_unary_value Rev64S x acc = simd_reverse 4 2 32 x
End

Definition simd_extract_def:
  simd_extract FmovW (v:word128) = (w2w (w2w v : word32) : word64) ∧
  simd_extract FmovX v = w2w v ∧
  simd_extract UmovB0 v = w2w (w2w v : word8) ∧
  simd_extract UmovD1 v = w2w (v >>> 64) ∧
  simd_extract Dup2D v = 0w ∧
  simd_extract FmovToD v = 0w
End

Definition execute_with_def:
  execute_with ops (BranchImm link imm) s =
    Next (branch (sw2sw imm) (if link then set_gpr ops 30w (s.pc + 4w) s else s)) ∧
  execute_with ops (BCond cond imm) s =
    Next (if condition_holds cond s.nzcv then branch (sw2sw imm) s else advance s) ∧
  execute_with ops (CompareBranch sf nz t imm) s =
    Next (if (lane sf (gpr ops s t) ≠ 0w) = nz then branch (sw2sw imm) s else advance s) ∧
  execute_with ops (TestBranch nz bit t imm) s =
    Next (if word_bit (w2n bit) (gpr ops s t) = nz then branch (sw2sw imm) s else advance s) ∧
  execute_with ops (Br n) s = Next (s with pc := gpr ops s n) ∧
  execute_with ops (Blr n) s =
    Next (set_gpr ops 30w (s.pc + 4w) (s with pc := gpr ops s n)) ∧
  execute_with ops (Ret n) s = Next (s with pc := gpr ops s n) ∧
  execute_with ops (MoveWide sf opc hw d imm) s =
    (let pos = 16 * w2n hw;
         old = if opc = 3w then gpr ops s d && ¬(0xffffw << pos) else 0w;
         v = old || (w2w imm << pos)
     in Next (advance (set_gpr ops d (lane sf (if opc = 0w then ¬v else v)) s))) ∧
  execute_with ops (AddImm sf sub flags shift d n imm) s =
    Next (write_arith ops T sf sub flags sub d (base_reg ops s n)
      (w2w imm << (if shift then 12 else 0)) s) ∧
  execute_with ops (AddShift sf sub flags shift d n m amount) s =
    Next (write_arith ops F sf sub flags sub d (gpr ops s n)
      (shift_reg sf shift (w2n amount) (gpr ops s m)) s) ∧
  execute_with ops (AddExtend sf sub flags ext d n m amount) s =
    Next (write_arith ops T sf sub flags sub d (base_reg ops s n)
      (extend_reg ext (gpr ops s m) << w2n amount) s) ∧
  execute_with ops (AddCarry sf sub flags d n m) s =
    Next (write_arith ops F sf sub flags (FST (SND (SND s.nzcv))) d
      (gpr ops s n) (gpr ops s m) s) ∧
  execute_with ops (CondCompare sf sub imm n y cond nzcv) s =
    Next (if condition_holds cond s.nzcv then
            write_arith ops F sf sub T sub 31w (gpr ops s n)
              (if imm then w2w y else gpr ops s y) s
          else
            advance (s with nzcv :=
              (word_bit 3 nzcv, word_bit 2 nzcv,
               word_bit 1 nzcv, word_bit 0 nzcv))) ∧
  execute_with ops (LogicalReg sf opc invert shift d n m amount) s =
    (let y = shift_reg sf shift (w2n amount) (gpr ops s m);
         v = logical_value sf opc (gpr ops s n) (if invert then ¬y else y)
     in Next (advance (set_gpr ops d v (logical_flags sf opc v s)))) ∧
  execute_with ops (LogicalImm sf opc N immr imms d n) s =
    (let v = logical_value sf opc (gpr ops s n) (FST (bit_masks N imms immr))
     in Next (advance (if opc = 3w then set_gpr ops d v (logical_flags sf opc v s)
                       else set_base ops d v s))) ∧
  execute_with ops (VariableShift sf shift d n m) s =
    Next (advance (set_gpr ops d
      (shift_reg sf shift (w2n (gpr ops s m) MOD lane_size sf) (gpr ops s n)) s)) ∧
  execute_with ops (Bitfield sf opc d n immr imms) s =
    Next (advance (set_gpr ops d
      (bitfield_value sf opc immr imms (gpr ops s d) (gpr ops s n)) s)) ∧
  execute_with ops (Extract sf d n m amount) s =
    Next (advance (set_gpr ops d
      (lane sf ((lane sf (gpr ops s m) >>> w2n amount) ||
                (gpr ops s n << (lane_size sf - w2n amount)))) s)) ∧
  execute_with ops (Select sf opc d n m cond) s =
    (let y = gpr ops s m;
         v = if condition_holds cond s.nzcv then gpr ops s n
             else if opc = 0w then y else if opc = 1w then y + 1w
             else if opc = 2w then ¬y else -y
     in Next (advance (set_gpr ops d (lane sf v) s))) ∧
  execute_with ops (MulLong unsigned sub d n m a) s =
    (let x = gpr ops s n; y = gpr ops s m;
         p = if unsigned then lane F x * lane F y else signed_lane F x * signed_lane F y;
         x = gpr ops s a in
     Next (advance (set_gpr ops d (if sub then x - p else x + p) s))) ∧
  execute_with ops (MulAdd sf sub d n m a) s =
    (let p = gpr ops s n * gpr ops s m; x = gpr ops s a in
     Next (advance (set_gpr ops d (lane sf (if sub then x - p else x + p)) s))) ∧
  execute_with ops (MulHigh signed d n m) s =
    (let x = gpr ops s n; y = gpr ops s m;
         p : word128 = if signed then sw2sw x * sw2sw y else w2w x * w2w y in
     Next (advance (set_gpr ops d (w2w (p >>> 64)) s))) ∧
  execute_with ops (Divide sf signed d n m) s =
    (let x = lane sf (gpr ops s n); y = lane sf (gpr ops s m);
         v = if y = 0w then 0w
             else if ¬signed then x // y
             else if sf then x / y else w2w ((w2w x : word32) / w2w y)
     in Next (advance (set_gpr ops d v s))) ∧
  execute_with ops (BitOp sf op d n) s =
    Next (advance (set_gpr ops d (bit_op_value sf op (gpr ops s n)) s)) ∧
  execute_with ops (PcAddress page d imm) s =
    (let off : word64 = sw2sw imm;
         addr = if page then (s.pc && ¬0xfffw) + (off << 12) else s.pc + off
     in Next (advance (set_gpr ops d addr s))) ∧
  execute_with ops (LoadLiteral vec opc t imm) s =
    (let a = s.pc + (sw2sw imm << 2);
         bytes = if vec then 2 ** (2 + w2n opc) else if opc = 1w then 8 else 4
     in
       if ¬vec ∧ opc = 3w then Next (advance s)
       else if access_ok ops Read bytes s a then
         let v = read_bytes ops bytes s a in
         Next (advance (put_loaded ops vec t
           (if vec then v else w2w (load_extend opc bytes v)) s))
       else Fault Load) ∧
  execute_with ops (MemImm vec opc size t n imm) s =
    (case imm of
       Scaled u =>
         execute_mem ops vec opc size Offset t n (w2w u << transfer_scale vec opc size) s
     | Unscaled mode i => execute_mem ops vec opc size mode t n (sw2sw i) s) ∧
  execute_with ops (MemReg vec opc size t n m ext scaled) s =
    execute_mem ops vec opc size Offset t n
      (extend_reg ext (gpr ops s m) << (if scaled then transfer_scale vec opc size else 0)) s ∧
  execute_with ops (MemPair vec opc load mode t u n imm) s =
    execute_pair ops vec opc load mode t u n imm s ∧
  execute_with ops (MemMulti q load post m opc size t n) s =
    execute_multi ops q load post m opc size t n s ∧
  execute_with ops (MemLane q load post m r opc S size t n) s =
    execute_lane ops q load post m r opc S size t n s ∧
  execute_with ops (SimdImm q op cmode imm d) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_imm_value q op cmode imm (ops.get_vec s.vregs d)) s.vregs)) ∧
  execute_with ops (SimdBinary op d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_binary_value op (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (SimdUnary op d n) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_unary_value op (ops.get_vec s.vregs n) (ops.get_vec s.vregs d)) s.vregs)) ∧
  execute_with ops (Crc32 castagnoli size d n m) s =
    Next (advance (set_gpr ops d
      (w2w (crc32_value castagnoli size (w2w (gpr ops s n)) (gpr ops s m))) s)) ∧
  execute_with ops (Pmull high d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (pmull_value high (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (Aes op d n) s =
    Next (advance (s with vregs := ops.put_vec d
      (aes_value op (ops.get_vec s.vregs d) (ops.get_vec s.vregs n)) s.vregs)) ∧
  execute_with ops (ShaThree opc d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (sha_three_value opc (ops.get_vec s.vregs d) (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (ShaTwo opc d n) s =
    Next (advance (s with vregs := ops.put_vec d
      (sha_two_value opc (ops.get_vec s.vregs d) (ops.get_vec s.vregs n)) s.vregs)) ∧
  execute_with ops (CryptoFour op0 d n m a) s =
    Next (advance (s with vregs := ops.put_vec d
      (crypto_four_value op0 (ops.get_vec s.vregs n) (ops.get_vec s.vregs m) (ops.get_vec s.vregs a)) s.vregs)) ∧
  execute_with ops (Sm3Tt opc imm d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (sm3_tt opc (w2n imm) (ops.get_vec s.vregs d) (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (CryptoThree sm opc d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (crypto_three_value sm opc (ops.get_vec s.vregs d) (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (Xar d n m imm) s =
    Next (advance (s with vregs := ops.put_vec d
      (xar_value (ops.get_vec s.vregs n) (ops.get_vec s.vregs m) (w2n imm)) s.vregs)) ∧
  execute_with ops (CryptoTwo opc d n) s =
    Next (advance (s with vregs := ops.put_vec d
      (crypto_two_value opc (ops.get_vec s.vregs d) (ops.get_vec s.vregs n)) s.vregs)) ∧
  execute_with ops (SimdTable extend d n m) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_table 16 (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)
        (if extend then ops.get_vec s.vregs d else 0w)) s.vregs)) ∧
  execute_with ops (SimdExtract d n m imm) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_ext (w2n imm) (ops.get_vec s.vregs n) (ops.get_vec s.vregs m)) s.vregs)) ∧
  execute_with ops (SimdShift op d n imm) s =
    Next (advance (s with vregs := ops.put_vec d
      (simd_shift_value op imm (ops.get_vec s.vregs n) (ops.get_vec s.vregs d)) s.vregs)) ∧
  execute_with ops (SimdTransfer op d n) s =
    (if op = Dup2D then
       let x : word128 = w2w (gpr ops s n) in
       Next (advance (s with vregs := ops.put_vec d (x || (x << 64)) s.vregs))
     else if op = FmovToD then
       Next (advance (s with vregs := ops.put_vec d (w2w (gpr ops s n)) s.vregs))
     else Next (advance (set_gpr ops d (simd_extract op (ops.get_vec s.vregs n)) s))) ∧
  execute_with ops Nop s = Next (advance s)
End

Definition fetch_def:
  fetch ops s = w2w (read_bytes ops 4 s s.pc) : word32
End

Definition step_with_def:
  step_with ops feat s =
    if s.pc && 3w ≠ 0w then Fault PCAlignment
    else if ¬access_ok ops Execute 4 s s.pc then Fault Fetch
    else case decode feat (fetch ops s) of
      NONE => Fault Unsupported
    | SOME i => execute_with ops i s
End

Definition step_def:
  step feat (s:arm64_state) : step_result = step_with functional_storage feat s
End
