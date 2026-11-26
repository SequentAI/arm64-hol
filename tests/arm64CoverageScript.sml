Theory arm64Coverage
Ancestors arm64Isa
Libs wordsLib

(* Fixture-free representative words for every implemented non-ADD row.  Each pair carries an expected HOL constructor tag. *)

Definition coverage_tag_def:
  coverage_tag (BranchImm _ _) = 1w ∧
  coverage_tag (BCond _ _) = 2w ∧
  coverage_tag (CompareBranch _ _ _ _) = 3w ∧
  coverage_tag (TestBranch _ _ _ _) = 4w ∧
  coverage_tag (Br _) = 5w ∧
  coverage_tag (Ret _) = 6w ∧
  coverage_tag (MoveZero _ _ _ _) = 7w ∧
  coverage_tag (CompareImm _ _ _ _ _) = 8w ∧
  coverage_tag (LogicalMask _ _ _) = 9w ∧
  coverage_tag (PcAddress _ _ _) = 10w ∧
  coverage_tag (AndByteMask _ _) = 11w ∧
  coverage_tag (AndTailMask _ _ _) = 12w ∧
  coverage_tag (TstLowMask _ _) = 13w ∧
  coverage_tag (Nop) = 14w ∧
  coverage_tag (MemImm _ _ _ _ _) = 15w ∧
  coverage_tag (MemReg _ _ _ _ _ _ _) = 16w ∧
  coverage_tag (MemPair _ _ _ _ _ _ _) = 17w ∧
  coverage_tag (LdpQ _ _ _ _) = 18w ∧
  coverage_tag (StpQ _ _ _ _) = 19w ∧
  coverage_tag (LdrQ _ _ _) = 20w ∧
  coverage_tag (StrQ _ _ _) = 21w ∧
  coverage_tag (LogicalReg _ _ _ _ _ _ _ _) = 22w ∧
  coverage_tag (VariableShift _ _ _ _ _) = 23w ∧
  coverage_tag (Bitfield _ _ _ _ _ _) = 24w ∧
  coverage_tag (Extract _ _ _ _ _) = 25w ∧
  coverage_tag (Select _ _ _ _ _ _) = 26w ∧
  coverage_tag (SignedMulLong _ _ _) = 27w ∧
  coverage_tag (MulAdd _ _ _ _ _ _) = 28w ∧
  coverage_tag (MulHigh _ _ _ _) = 29w ∧
  coverage_tag (Divide _ _ _ _ _) = 30w ∧
  coverage_tag (BitOp _ _ _ _) = 31w ∧
  coverage_tag (MoviZero _) = 32w ∧
  coverage_tag (MoviZero4S _) = 33w ∧
  coverage_tag (SimdBinary _ _ _ _) = 34w ∧
  coverage_tag (SimdUnary _ _ _) = 35w ∧
  coverage_tag (SimdTable _ _ _ _) = 36w ∧
  coverage_tag (SimdExtract _ _ _ _) = 37w ∧
  coverage_tag (SimdShift _ _ _ _) = 38w ∧
  coverage_tag (SimdTransfer _ _ _) = 39w ∧
  coverage_tag (Crc32 _ _ _ _ _) = 40w ∧
  coverage_tag (Pmull _ _ _ _) = 41w ∧
  coverage_tag (Aes _ _ _) = 42w
End

Definition a64_decode_coverage_probes_2_def:
  a64_decode_coverage_probes_2 = [
     (0x52800000w, 7w);
     (0xd2800000w, 7w);
     (0x7a400800w, 8w);
     (0x10000000w, 10w);
     (0x92400000w, 9w);
     (0x92400c00w, 9w);
     (0x12001400w, 9w);
     (0x12001800w, 9w);
     (0x92401800w, 9w);
     (0x321a6400w, 9w);
     (0x12001c00w, 11w);
     (0x12000400w, 12w);
     (0x121e7400w, 12w);
     (0x72001c1fw, 13w);
     (0x72003c1fw, 13w);
     (0x14000000w, 1w)]
End

Theorem a64_decode_coverage_probes_2_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2
Proof
  EVAL_TAC
QED

Definition a64_decode_coverage_probes_2_1_def:
  a64_decode_coverage_probes_2_1 = [
     (0x54000000w, 2w);
     (0x34000000w, 3w);
     (0x36000000w, 4w);
     (0xd61f0000w, 5w);
     (0xd65f0000w, 6w);
     (0xd503201fw, 14w);
     (0x39000000w, 15w);
     (0x38401441w, 15w);
     (0x38204800w, 16w);
     (0x28800440w, 17w);
     (0xad400440w, 18w);
     (0xad000000w, 19w);
     (0x3dc00000w, 20w);
     (0x3cc00400w, 20w);
     (0x3d800000w, 21w);
     (0x0a000000w, 22w)]
End

Theorem a64_decode_coverage_probes_2_1_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2_1
Proof
  EVAL_TAC
QED

Definition a64_decode_coverage_probes_2_2_def:
  a64_decode_coverage_probes_2_2 = [
     (0x1ac02000w, 23w);
     (0x13000000w, 24w);
     (0x13800000w, 25w);
     (0x1a800000w, 26w);
     (0x9b207c00w, 27w);
     (0x1b000000w, 28w);
     (0x9b407c00w, 29w);
     (0x9bc07c00w, 29w);
     (0x1ac00800w, 30w);
     (0x5ac01000w, 31w);
     (0xdac01000w, 31w);
     (0x5ac00000w, 31w);
     (0xdac00000w, 31w);
     (0x5ac00800w, 31w);
     (0xdac00c00w, 31w);
     (0x6f00e400w, 32w);
     (0x4f000400w, 33w)]
End

Theorem a64_decode_coverage_probes_2_2_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2_2
Proof
  EVAL_TAC
QED

Definition a64_decode_coverage_probes_2_3_def:
  a64_decode_coverage_probes_2_3 = [
     (0x4ea08400w, 34w);
     (0x4ee08400w, 34w);
     (0x6e208c00w, 34w);
     (0x6e201c00w, 34w);
     (0x4ea01c00w, 34w);
     (0x4e209800w, 35w);
     (0x6e31a800w, 35w);
     (0x4eb1b800w, 35w);
     (0x4e71b800w, 35w);
     (0x6e202800w, 35w);
     (0x6e206800w, 35w);
     (0x0e205800w, 35w);
     (0x0e31b800w, 35w);
     (0x4e201800w, 35w);
     (0x6e200800w, 35w);
     (0x6e600800w, 35w)]
End

Theorem a64_decode_coverage_probes_2_3_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2_3
Proof
  EVAL_TAC
QED

Definition a64_decode_coverage_probes_2_4_def:
  a64_decode_coverage_probes_2_4 = [
     (0x4e200800w, 35w);
     (0x4e600800w, 35w);
     (0x4ea00800w, 35w);
     (0x4e000000w, 36w);
     (0x4e001000w, 36w);
     (0x6e000000w, 37w);
     (0x4f205400w, 38w);
     (0x4f405400w, 38w);
     (0x6f200400w, 38w);
     (0x6f400400w, 38w);
     (0x6f204400w, 38w);
     (0x6f404400w, 38w);
     (0x1e260000w, 39w);
     (0x9e660000w, 39w);
     (0x0e013c00w, 39w);
     (0x4e183c00w, 39w);
     (0x4e080c00w, 39w);
     (0x9e670000w, 39w);
     (0x1ac04000w, 40w)]
End

Theorem a64_decode_coverage_probes_2_4_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2_4
Proof
  EVAL_TAC
QED

Definition a64_decode_coverage_probes_2_5_def:
  a64_decode_coverage_probes_2_5 = [
     (0x0ee0e000w, 41w);
     (0x4e284800w, 42w);
     (0x4e285800w, 42w);
     (0x4e286800w, 42w);
     (0x4e287800w, 42w)]
End

Theorem a64_decode_coverage_probes_2_5_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_2_5
Proof
  EVAL_TAC
QED

(* Fixture-free representative A64 words.  The probes cover each ADD architectural row through decode and encode in HOL. *)

Definition addImm_w_coverage_probes_1_def:
  addImm_w_coverage_probes_1 = [
     (0x11000000w, AddImm F F F F 0w 0w 0w);
     (0x11400000w, AddImm F F F T 0w 0w 0w);
     (0x31000000w, AddImm F F T F 0w 0w 0w);
     (0x31400000w, AddImm F F T T 0w 0w 0w);
     (0x51000000w, AddImm F T F F 0w 0w 0w);
     (0x51400000w, AddImm F T F T 0w 0w 0w);
     (0x71000000w, AddImm F T T F 0w 0w 0w);
     (0x71400000w, AddImm F T T T 0w 0w 0w)]
End

Theorem addImm_w_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addImm_w_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addImm_x_coverage_probes_1_def:
  addImm_x_coverage_probes_1 = [
     (0x91000000w, AddImm T F F F 0w 0w 0w);
     (0x91400000w, AddImm T F F T 0w 0w 0w);
     (0xb1000000w, AddImm T F T F 0w 0w 0w);
     (0xb1400000w, AddImm T F T T 0w 0w 0w);
     (0xd1000000w, AddImm T T F F 0w 0w 0w);
     (0xd1400000w, AddImm T T F T 0w 0w 0w);
     (0xf1000000w, AddImm T T T F 0w 0w 0w);
     (0xf1400000w, AddImm T T T T 0w 0w 0w)]
End

Theorem addImm_x_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addImm_x_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addShift_w_coverage_probes_1_def:
  addShift_w_coverage_probes_1 = [
     (0x0b000400w, AddShift F F F 0w 0w 0w 0w 1w);
     (0x0b400800w, AddShift F F F 1w 0w 0w 0w 2w);
     (0x0b800c00w, AddShift F F F 2w 0w 0w 0w 3w);
     (0x2b000400w, AddShift F F T 0w 0w 0w 0w 1w);
     (0x2b400800w, AddShift F F T 1w 0w 0w 0w 2w);
     (0x2b800c00w, AddShift F F T 2w 0w 0w 0w 3w);
     (0x4b000400w, AddShift F T F 0w 0w 0w 0w 1w);
     (0x4b400800w, AddShift F T F 1w 0w 0w 0w 2w);
     (0x4b800c00w, AddShift F T F 2w 0w 0w 0w 3w);
     (0x6b000400w, AddShift F T T 0w 0w 0w 0w 1w);
     (0x6b400800w, AddShift F T T 1w 0w 0w 0w 2w);
     (0x6b800c00w, AddShift F T T 2w 0w 0w 0w 3w)]
End

Theorem addShift_w_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addShift_w_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addShift_x_coverage_probes_1_def:
  addShift_x_coverage_probes_1 = [
     (0x8b000400w, AddShift T F F 0w 0w 0w 0w 1w);
     (0x8b400800w, AddShift T F F 1w 0w 0w 0w 2w);
     (0x8b800c00w, AddShift T F F 2w 0w 0w 0w 3w);
     (0xab000400w, AddShift T F T 0w 0w 0w 0w 1w);
     (0xab400800w, AddShift T F T 1w 0w 0w 0w 2w);
     (0xab800c00w, AddShift T F T 2w 0w 0w 0w 3w);
     (0xcb000400w, AddShift T T F 0w 0w 0w 0w 1w);
     (0xcb400800w, AddShift T T F 1w 0w 0w 0w 2w);
     (0xcb800c00w, AddShift T T F 2w 0w 0w 0w 3w);
     (0xeb000400w, AddShift T T T 0w 0w 0w 0w 1w);
     (0xeb400800w, AddShift T T T 1w 0w 0w 0w 2w);
     (0xeb800c00w, AddShift T T T 2w 0w 0w 0w 3w)]
End

Theorem addShift_x_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addShift_x_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_1_def:
  addExtend_w_coverage_probes_1 = [
     (0x0b200000w, AddExtend F F F 0w 0w 0w 0w 0w);
     (0x0b200400w, AddExtend F F F 0w 0w 0w 0w 1w);
     (0x0b200800w, AddExtend F F F 0w 0w 0w 0w 2w);
     (0x0b200c00w, AddExtend F F F 0w 0w 0w 0w 3w);
     (0x0b201000w, AddExtend F F F 0w 0w 0w 0w 4w);
     (0x0b202000w, AddExtend F F F 1w 0w 0w 0w 0w);
     (0x0b202400w, AddExtend F F F 1w 0w 0w 0w 1w);
     (0x0b202800w, AddExtend F F F 1w 0w 0w 0w 2w);
     (0x0b202c00w, AddExtend F F F 1w 0w 0w 0w 3w);
     (0x0b203000w, AddExtend F F F 1w 0w 0w 0w 4w);
     (0x0b204000w, AddExtend F F F 2w 0w 0w 0w 0w);
     (0x0b204400w, AddExtend F F F 2w 0w 0w 0w 1w);
     (0x0b204800w, AddExtend F F F 2w 0w 0w 0w 2w);
     (0x0b204c00w, AddExtend F F F 2w 0w 0w 0w 3w);
     (0x0b205000w, AddExtend F F F 2w 0w 0w 0w 4w);
     (0x0b206000w, AddExtend F F F 3w 0w 0w 0w 0w)]
End

Theorem addExtend_w_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_2_def:
  addExtend_w_coverage_probes_2 = [
     (0x0b206400w, AddExtend F F F 3w 0w 0w 0w 1w);
     (0x0b206800w, AddExtend F F F 3w 0w 0w 0w 2w);
     (0x0b206c00w, AddExtend F F F 3w 0w 0w 0w 3w);
     (0x0b207000w, AddExtend F F F 3w 0w 0w 0w 4w);
     (0x0b208000w, AddExtend F F F 4w 0w 0w 0w 0w);
     (0x0b208400w, AddExtend F F F 4w 0w 0w 0w 1w);
     (0x0b208800w, AddExtend F F F 4w 0w 0w 0w 2w);
     (0x0b208c00w, AddExtend F F F 4w 0w 0w 0w 3w);
     (0x0b209000w, AddExtend F F F 4w 0w 0w 0w 4w);
     (0x0b20a000w, AddExtend F F F 5w 0w 0w 0w 0w);
     (0x0b20a400w, AddExtend F F F 5w 0w 0w 0w 1w);
     (0x0b20a800w, AddExtend F F F 5w 0w 0w 0w 2w);
     (0x0b20ac00w, AddExtend F F F 5w 0w 0w 0w 3w);
     (0x0b20b000w, AddExtend F F F 5w 0w 0w 0w 4w);
     (0x0b20c000w, AddExtend F F F 6w 0w 0w 0w 0w);
     (0x0b20c400w, AddExtend F F F 6w 0w 0w 0w 1w)]
End

Theorem addExtend_w_coverage_probes_2_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_2
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_3_def:
  addExtend_w_coverage_probes_3 = [
     (0x0b20c800w, AddExtend F F F 6w 0w 0w 0w 2w);
     (0x0b20cc00w, AddExtend F F F 6w 0w 0w 0w 3w);
     (0x0b20d000w, AddExtend F F F 6w 0w 0w 0w 4w);
     (0x0b20e000w, AddExtend F F F 7w 0w 0w 0w 0w);
     (0x0b20e400w, AddExtend F F F 7w 0w 0w 0w 1w);
     (0x0b20e800w, AddExtend F F F 7w 0w 0w 0w 2w);
     (0x0b20ec00w, AddExtend F F F 7w 0w 0w 0w 3w);
     (0x0b20f000w, AddExtend F F F 7w 0w 0w 0w 4w);
     (0x2b200000w, AddExtend F F T 0w 0w 0w 0w 0w);
     (0x2b200400w, AddExtend F F T 0w 0w 0w 0w 1w);
     (0x2b200800w, AddExtend F F T 0w 0w 0w 0w 2w);
     (0x2b200c00w, AddExtend F F T 0w 0w 0w 0w 3w);
     (0x2b201000w, AddExtend F F T 0w 0w 0w 0w 4w);
     (0x2b202000w, AddExtend F F T 1w 0w 0w 0w 0w);
     (0x2b202400w, AddExtend F F T 1w 0w 0w 0w 1w);
     (0x2b202800w, AddExtend F F T 1w 0w 0w 0w 2w)]
End

Theorem addExtend_w_coverage_probes_3_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_3
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_4_def:
  addExtend_w_coverage_probes_4 = [
     (0x2b202c00w, AddExtend F F T 1w 0w 0w 0w 3w);
     (0x2b203000w, AddExtend F F T 1w 0w 0w 0w 4w);
     (0x2b204000w, AddExtend F F T 2w 0w 0w 0w 0w);
     (0x2b204400w, AddExtend F F T 2w 0w 0w 0w 1w);
     (0x2b204800w, AddExtend F F T 2w 0w 0w 0w 2w);
     (0x2b204c00w, AddExtend F F T 2w 0w 0w 0w 3w);
     (0x2b205000w, AddExtend F F T 2w 0w 0w 0w 4w);
     (0x2b206000w, AddExtend F F T 3w 0w 0w 0w 0w);
     (0x2b206400w, AddExtend F F T 3w 0w 0w 0w 1w);
     (0x2b206800w, AddExtend F F T 3w 0w 0w 0w 2w);
     (0x2b206c00w, AddExtend F F T 3w 0w 0w 0w 3w);
     (0x2b207000w, AddExtend F F T 3w 0w 0w 0w 4w);
     (0x2b208000w, AddExtend F F T 4w 0w 0w 0w 0w);
     (0x2b208400w, AddExtend F F T 4w 0w 0w 0w 1w);
     (0x2b208800w, AddExtend F F T 4w 0w 0w 0w 2w);
     (0x2b208c00w, AddExtend F F T 4w 0w 0w 0w 3w)]
End

Theorem addExtend_w_coverage_probes_4_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_4
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_5_def:
  addExtend_w_coverage_probes_5 = [
     (0x2b209000w, AddExtend F F T 4w 0w 0w 0w 4w);
     (0x2b20a000w, AddExtend F F T 5w 0w 0w 0w 0w);
     (0x2b20a400w, AddExtend F F T 5w 0w 0w 0w 1w);
     (0x2b20a800w, AddExtend F F T 5w 0w 0w 0w 2w);
     (0x2b20ac00w, AddExtend F F T 5w 0w 0w 0w 3w);
     (0x2b20b000w, AddExtend F F T 5w 0w 0w 0w 4w);
     (0x2b20c000w, AddExtend F F T 6w 0w 0w 0w 0w);
     (0x2b20c400w, AddExtend F F T 6w 0w 0w 0w 1w);
     (0x2b20c800w, AddExtend F F T 6w 0w 0w 0w 2w);
     (0x2b20cc00w, AddExtend F F T 6w 0w 0w 0w 3w);
     (0x2b20d000w, AddExtend F F T 6w 0w 0w 0w 4w);
     (0x2b20e000w, AddExtend F F T 7w 0w 0w 0w 0w);
     (0x2b20e400w, AddExtend F F T 7w 0w 0w 0w 1w);
     (0x2b20e800w, AddExtend F F T 7w 0w 0w 0w 2w);
     (0x2b20ec00w, AddExtend F F T 7w 0w 0w 0w 3w);
     (0x2b20f000w, AddExtend F F T 7w 0w 0w 0w 4w)]
End

Theorem addExtend_w_coverage_probes_5_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_5
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_6_def:
  addExtend_w_coverage_probes_6 = [
     (0x4b200000w, AddExtend F T F 0w 0w 0w 0w 0w);
     (0x4b200400w, AddExtend F T F 0w 0w 0w 0w 1w);
     (0x4b200800w, AddExtend F T F 0w 0w 0w 0w 2w);
     (0x4b200c00w, AddExtend F T F 0w 0w 0w 0w 3w);
     (0x4b201000w, AddExtend F T F 0w 0w 0w 0w 4w);
     (0x4b202000w, AddExtend F T F 1w 0w 0w 0w 0w);
     (0x4b202400w, AddExtend F T F 1w 0w 0w 0w 1w);
     (0x4b202800w, AddExtend F T F 1w 0w 0w 0w 2w);
     (0x4b202c00w, AddExtend F T F 1w 0w 0w 0w 3w);
     (0x4b203000w, AddExtend F T F 1w 0w 0w 0w 4w);
     (0x4b204000w, AddExtend F T F 2w 0w 0w 0w 0w);
     (0x4b204400w, AddExtend F T F 2w 0w 0w 0w 1w);
     (0x4b204800w, AddExtend F T F 2w 0w 0w 0w 2w);
     (0x4b204c00w, AddExtend F T F 2w 0w 0w 0w 3w);
     (0x4b205000w, AddExtend F T F 2w 0w 0w 0w 4w);
     (0x4b206000w, AddExtend F T F 3w 0w 0w 0w 0w)]
End

Theorem addExtend_w_coverage_probes_6_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_6
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_7_def:
  addExtend_w_coverage_probes_7 = [
     (0x4b206400w, AddExtend F T F 3w 0w 0w 0w 1w);
     (0x4b206800w, AddExtend F T F 3w 0w 0w 0w 2w);
     (0x4b206c00w, AddExtend F T F 3w 0w 0w 0w 3w);
     (0x4b207000w, AddExtend F T F 3w 0w 0w 0w 4w);
     (0x4b208000w, AddExtend F T F 4w 0w 0w 0w 0w);
     (0x4b208400w, AddExtend F T F 4w 0w 0w 0w 1w);
     (0x4b208800w, AddExtend F T F 4w 0w 0w 0w 2w);
     (0x4b208c00w, AddExtend F T F 4w 0w 0w 0w 3w);
     (0x4b209000w, AddExtend F T F 4w 0w 0w 0w 4w);
     (0x4b20a000w, AddExtend F T F 5w 0w 0w 0w 0w);
     (0x4b20a400w, AddExtend F T F 5w 0w 0w 0w 1w);
     (0x4b20a800w, AddExtend F T F 5w 0w 0w 0w 2w);
     (0x4b20ac00w, AddExtend F T F 5w 0w 0w 0w 3w);
     (0x4b20b000w, AddExtend F T F 5w 0w 0w 0w 4w);
     (0x4b20c000w, AddExtend F T F 6w 0w 0w 0w 0w);
     (0x4b20c400w, AddExtend F T F 6w 0w 0w 0w 1w)]
End

Theorem addExtend_w_coverage_probes_7_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_7
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_8_def:
  addExtend_w_coverage_probes_8 = [
     (0x4b20c800w, AddExtend F T F 6w 0w 0w 0w 2w);
     (0x4b20cc00w, AddExtend F T F 6w 0w 0w 0w 3w);
     (0x4b20d000w, AddExtend F T F 6w 0w 0w 0w 4w);
     (0x4b20e000w, AddExtend F T F 7w 0w 0w 0w 0w);
     (0x4b20e400w, AddExtend F T F 7w 0w 0w 0w 1w);
     (0x4b20e800w, AddExtend F T F 7w 0w 0w 0w 2w);
     (0x4b20ec00w, AddExtend F T F 7w 0w 0w 0w 3w);
     (0x4b20f000w, AddExtend F T F 7w 0w 0w 0w 4w);
     (0x6b200000w, AddExtend F T T 0w 0w 0w 0w 0w);
     (0x6b200400w, AddExtend F T T 0w 0w 0w 0w 1w);
     (0x6b200800w, AddExtend F T T 0w 0w 0w 0w 2w);
     (0x6b200c00w, AddExtend F T T 0w 0w 0w 0w 3w);
     (0x6b201000w, AddExtend F T T 0w 0w 0w 0w 4w);
     (0x6b202000w, AddExtend F T T 1w 0w 0w 0w 0w);
     (0x6b202400w, AddExtend F T T 1w 0w 0w 0w 1w);
     (0x6b202800w, AddExtend F T T 1w 0w 0w 0w 2w)]
End

Theorem addExtend_w_coverage_probes_8_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_8
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_9_def:
  addExtend_w_coverage_probes_9 = [
     (0x6b202c00w, AddExtend F T T 1w 0w 0w 0w 3w);
     (0x6b203000w, AddExtend F T T 1w 0w 0w 0w 4w);
     (0x6b204000w, AddExtend F T T 2w 0w 0w 0w 0w);
     (0x6b204400w, AddExtend F T T 2w 0w 0w 0w 1w);
     (0x6b204800w, AddExtend F T T 2w 0w 0w 0w 2w);
     (0x6b204c00w, AddExtend F T T 2w 0w 0w 0w 3w);
     (0x6b205000w, AddExtend F T T 2w 0w 0w 0w 4w);
     (0x6b206000w, AddExtend F T T 3w 0w 0w 0w 0w);
     (0x6b206400w, AddExtend F T T 3w 0w 0w 0w 1w);
     (0x6b206800w, AddExtend F T T 3w 0w 0w 0w 2w);
     (0x6b206c00w, AddExtend F T T 3w 0w 0w 0w 3w);
     (0x6b207000w, AddExtend F T T 3w 0w 0w 0w 4w);
     (0x6b208000w, AddExtend F T T 4w 0w 0w 0w 0w);
     (0x6b208400w, AddExtend F T T 4w 0w 0w 0w 1w);
     (0x6b208800w, AddExtend F T T 4w 0w 0w 0w 2w);
     (0x6b208c00w, AddExtend F T T 4w 0w 0w 0w 3w)]
End

Theorem addExtend_w_coverage_probes_9_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_9
Proof
  EVAL_TAC
QED

Definition addExtend_w_coverage_probes_10_def:
  addExtend_w_coverage_probes_10 = [
     (0x6b209000w, AddExtend F T T 4w 0w 0w 0w 4w);
     (0x6b20a000w, AddExtend F T T 5w 0w 0w 0w 0w);
     (0x6b20a400w, AddExtend F T T 5w 0w 0w 0w 1w);
     (0x6b20a800w, AddExtend F T T 5w 0w 0w 0w 2w);
     (0x6b20ac00w, AddExtend F T T 5w 0w 0w 0w 3w);
     (0x6b20b000w, AddExtend F T T 5w 0w 0w 0w 4w);
     (0x6b20c000w, AddExtend F T T 6w 0w 0w 0w 0w);
     (0x6b20c400w, AddExtend F T T 6w 0w 0w 0w 1w);
     (0x6b20c800w, AddExtend F T T 6w 0w 0w 0w 2w);
     (0x6b20cc00w, AddExtend F T T 6w 0w 0w 0w 3w);
     (0x6b20d000w, AddExtend F T T 6w 0w 0w 0w 4w);
     (0x6b20e000w, AddExtend F T T 7w 0w 0w 0w 0w);
     (0x6b20e400w, AddExtend F T T 7w 0w 0w 0w 1w);
     (0x6b20e800w, AddExtend F T T 7w 0w 0w 0w 2w);
     (0x6b20ec00w, AddExtend F T T 7w 0w 0w 0w 3w);
     (0x6b20f000w, AddExtend F T T 7w 0w 0w 0w 4w)]
End

Theorem addExtend_w_coverage_probes_10_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_w_coverage_probes_10
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_1_def:
  addExtend_x_coverage_probes_1 = [
     (0x8b200000w, AddExtend T F F 0w 0w 0w 0w 0w);
     (0x8b200400w, AddExtend T F F 0w 0w 0w 0w 1w);
     (0x8b200800w, AddExtend T F F 0w 0w 0w 0w 2w);
     (0x8b200c00w, AddExtend T F F 0w 0w 0w 0w 3w);
     (0x8b201000w, AddExtend T F F 0w 0w 0w 0w 4w);
     (0x8b202000w, AddExtend T F F 1w 0w 0w 0w 0w);
     (0x8b202400w, AddExtend T F F 1w 0w 0w 0w 1w);
     (0x8b202800w, AddExtend T F F 1w 0w 0w 0w 2w);
     (0x8b202c00w, AddExtend T F F 1w 0w 0w 0w 3w);
     (0x8b203000w, AddExtend T F F 1w 0w 0w 0w 4w);
     (0x8b204000w, AddExtend T F F 2w 0w 0w 0w 0w);
     (0x8b204400w, AddExtend T F F 2w 0w 0w 0w 1w);
     (0x8b204800w, AddExtend T F F 2w 0w 0w 0w 2w);
     (0x8b204c00w, AddExtend T F F 2w 0w 0w 0w 3w);
     (0x8b205000w, AddExtend T F F 2w 0w 0w 0w 4w);
     (0x8b206000w, AddExtend T F F 3w 0w 0w 0w 0w)]
End

Theorem addExtend_x_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_2_def:
  addExtend_x_coverage_probes_2 = [
     (0x8b206400w, AddExtend T F F 3w 0w 0w 0w 1w);
     (0x8b206800w, AddExtend T F F 3w 0w 0w 0w 2w);
     (0x8b206c00w, AddExtend T F F 3w 0w 0w 0w 3w);
     (0x8b207000w, AddExtend T F F 3w 0w 0w 0w 4w);
     (0x8b208000w, AddExtend T F F 4w 0w 0w 0w 0w);
     (0x8b208400w, AddExtend T F F 4w 0w 0w 0w 1w);
     (0x8b208800w, AddExtend T F F 4w 0w 0w 0w 2w);
     (0x8b208c00w, AddExtend T F F 4w 0w 0w 0w 3w);
     (0x8b209000w, AddExtend T F F 4w 0w 0w 0w 4w);
     (0x8b20a000w, AddExtend T F F 5w 0w 0w 0w 0w);
     (0x8b20a400w, AddExtend T F F 5w 0w 0w 0w 1w);
     (0x8b20a800w, AddExtend T F F 5w 0w 0w 0w 2w);
     (0x8b20ac00w, AddExtend T F F 5w 0w 0w 0w 3w);
     (0x8b20b000w, AddExtend T F F 5w 0w 0w 0w 4w);
     (0x8b20c000w, AddExtend T F F 6w 0w 0w 0w 0w);
     (0x8b20c400w, AddExtend T F F 6w 0w 0w 0w 1w)]
End

Theorem addExtend_x_coverage_probes_2_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_2
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_3_def:
  addExtend_x_coverage_probes_3 = [
     (0x8b20c800w, AddExtend T F F 6w 0w 0w 0w 2w);
     (0x8b20cc00w, AddExtend T F F 6w 0w 0w 0w 3w);
     (0x8b20d000w, AddExtend T F F 6w 0w 0w 0w 4w);
     (0x8b20e000w, AddExtend T F F 7w 0w 0w 0w 0w);
     (0x8b20e400w, AddExtend T F F 7w 0w 0w 0w 1w);
     (0x8b20e800w, AddExtend T F F 7w 0w 0w 0w 2w);
     (0x8b20ec00w, AddExtend T F F 7w 0w 0w 0w 3w);
     (0x8b20f000w, AddExtend T F F 7w 0w 0w 0w 4w);
     (0xab200000w, AddExtend T F T 0w 0w 0w 0w 0w);
     (0xab200400w, AddExtend T F T 0w 0w 0w 0w 1w);
     (0xab200800w, AddExtend T F T 0w 0w 0w 0w 2w);
     (0xab200c00w, AddExtend T F T 0w 0w 0w 0w 3w);
     (0xab201000w, AddExtend T F T 0w 0w 0w 0w 4w);
     (0xab202000w, AddExtend T F T 1w 0w 0w 0w 0w);
     (0xab202400w, AddExtend T F T 1w 0w 0w 0w 1w);
     (0xab202800w, AddExtend T F T 1w 0w 0w 0w 2w)]
End

Theorem addExtend_x_coverage_probes_3_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_3
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_4_def:
  addExtend_x_coverage_probes_4 = [
     (0xab202c00w, AddExtend T F T 1w 0w 0w 0w 3w);
     (0xab203000w, AddExtend T F T 1w 0w 0w 0w 4w);
     (0xab204000w, AddExtend T F T 2w 0w 0w 0w 0w);
     (0xab204400w, AddExtend T F T 2w 0w 0w 0w 1w);
     (0xab204800w, AddExtend T F T 2w 0w 0w 0w 2w);
     (0xab204c00w, AddExtend T F T 2w 0w 0w 0w 3w);
     (0xab205000w, AddExtend T F T 2w 0w 0w 0w 4w);
     (0xab206000w, AddExtend T F T 3w 0w 0w 0w 0w);
     (0xab206400w, AddExtend T F T 3w 0w 0w 0w 1w);
     (0xab206800w, AddExtend T F T 3w 0w 0w 0w 2w);
     (0xab206c00w, AddExtend T F T 3w 0w 0w 0w 3w);
     (0xab207000w, AddExtend T F T 3w 0w 0w 0w 4w);
     (0xab208000w, AddExtend T F T 4w 0w 0w 0w 0w);
     (0xab208400w, AddExtend T F T 4w 0w 0w 0w 1w);
     (0xab208800w, AddExtend T F T 4w 0w 0w 0w 2w);
     (0xab208c00w, AddExtend T F T 4w 0w 0w 0w 3w)]
End

Theorem addExtend_x_coverage_probes_4_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_4
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_5_def:
  addExtend_x_coverage_probes_5 = [
     (0xab209000w, AddExtend T F T 4w 0w 0w 0w 4w);
     (0xab20a000w, AddExtend T F T 5w 0w 0w 0w 0w);
     (0xab20a400w, AddExtend T F T 5w 0w 0w 0w 1w);
     (0xab20a800w, AddExtend T F T 5w 0w 0w 0w 2w);
     (0xab20ac00w, AddExtend T F T 5w 0w 0w 0w 3w);
     (0xab20b000w, AddExtend T F T 5w 0w 0w 0w 4w);
     (0xab20c000w, AddExtend T F T 6w 0w 0w 0w 0w);
     (0xab20c400w, AddExtend T F T 6w 0w 0w 0w 1w);
     (0xab20c800w, AddExtend T F T 6w 0w 0w 0w 2w);
     (0xab20cc00w, AddExtend T F T 6w 0w 0w 0w 3w);
     (0xab20d000w, AddExtend T F T 6w 0w 0w 0w 4w);
     (0xab20e000w, AddExtend T F T 7w 0w 0w 0w 0w);
     (0xab20e400w, AddExtend T F T 7w 0w 0w 0w 1w);
     (0xab20e800w, AddExtend T F T 7w 0w 0w 0w 2w);
     (0xab20ec00w, AddExtend T F T 7w 0w 0w 0w 3w);
     (0xab20f000w, AddExtend T F T 7w 0w 0w 0w 4w)]
End

Theorem addExtend_x_coverage_probes_5_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_5
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_6_def:
  addExtend_x_coverage_probes_6 = [
     (0xcb200000w, AddExtend T T F 0w 0w 0w 0w 0w);
     (0xcb200400w, AddExtend T T F 0w 0w 0w 0w 1w);
     (0xcb200800w, AddExtend T T F 0w 0w 0w 0w 2w);
     (0xcb200c00w, AddExtend T T F 0w 0w 0w 0w 3w);
     (0xcb201000w, AddExtend T T F 0w 0w 0w 0w 4w);
     (0xcb202000w, AddExtend T T F 1w 0w 0w 0w 0w);
     (0xcb202400w, AddExtend T T F 1w 0w 0w 0w 1w);
     (0xcb202800w, AddExtend T T F 1w 0w 0w 0w 2w);
     (0xcb202c00w, AddExtend T T F 1w 0w 0w 0w 3w);
     (0xcb203000w, AddExtend T T F 1w 0w 0w 0w 4w);
     (0xcb204000w, AddExtend T T F 2w 0w 0w 0w 0w);
     (0xcb204400w, AddExtend T T F 2w 0w 0w 0w 1w);
     (0xcb204800w, AddExtend T T F 2w 0w 0w 0w 2w);
     (0xcb204c00w, AddExtend T T F 2w 0w 0w 0w 3w);
     (0xcb205000w, AddExtend T T F 2w 0w 0w 0w 4w);
     (0xcb206000w, AddExtend T T F 3w 0w 0w 0w 0w)]
End

Theorem addExtend_x_coverage_probes_6_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_6
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_7_def:
  addExtend_x_coverage_probes_7 = [
     (0xcb206400w, AddExtend T T F 3w 0w 0w 0w 1w);
     (0xcb206800w, AddExtend T T F 3w 0w 0w 0w 2w);
     (0xcb206c00w, AddExtend T T F 3w 0w 0w 0w 3w);
     (0xcb207000w, AddExtend T T F 3w 0w 0w 0w 4w);
     (0xcb208000w, AddExtend T T F 4w 0w 0w 0w 0w);
     (0xcb208400w, AddExtend T T F 4w 0w 0w 0w 1w);
     (0xcb208800w, AddExtend T T F 4w 0w 0w 0w 2w);
     (0xcb208c00w, AddExtend T T F 4w 0w 0w 0w 3w);
     (0xcb209000w, AddExtend T T F 4w 0w 0w 0w 4w);
     (0xcb20a000w, AddExtend T T F 5w 0w 0w 0w 0w);
     (0xcb20a400w, AddExtend T T F 5w 0w 0w 0w 1w);
     (0xcb20a800w, AddExtend T T F 5w 0w 0w 0w 2w);
     (0xcb20ac00w, AddExtend T T F 5w 0w 0w 0w 3w);
     (0xcb20b000w, AddExtend T T F 5w 0w 0w 0w 4w);
     (0xcb20c000w, AddExtend T T F 6w 0w 0w 0w 0w);
     (0xcb20c400w, AddExtend T T F 6w 0w 0w 0w 1w)]
End

Theorem addExtend_x_coverage_probes_7_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_7
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_8_def:
  addExtend_x_coverage_probes_8 = [
     (0xcb20c800w, AddExtend T T F 6w 0w 0w 0w 2w);
     (0xcb20cc00w, AddExtend T T F 6w 0w 0w 0w 3w);
     (0xcb20d000w, AddExtend T T F 6w 0w 0w 0w 4w);
     (0xcb20e000w, AddExtend T T F 7w 0w 0w 0w 0w);
     (0xcb20e400w, AddExtend T T F 7w 0w 0w 0w 1w);
     (0xcb20e800w, AddExtend T T F 7w 0w 0w 0w 2w);
     (0xcb20ec00w, AddExtend T T F 7w 0w 0w 0w 3w);
     (0xcb20f000w, AddExtend T T F 7w 0w 0w 0w 4w);
     (0xeb200000w, AddExtend T T T 0w 0w 0w 0w 0w);
     (0xeb200400w, AddExtend T T T 0w 0w 0w 0w 1w);
     (0xeb200800w, AddExtend T T T 0w 0w 0w 0w 2w);
     (0xeb200c00w, AddExtend T T T 0w 0w 0w 0w 3w);
     (0xeb201000w, AddExtend T T T 0w 0w 0w 0w 4w);
     (0xeb202000w, AddExtend T T T 1w 0w 0w 0w 0w);
     (0xeb202400w, AddExtend T T T 1w 0w 0w 0w 1w);
     (0xeb202800w, AddExtend T T T 1w 0w 0w 0w 2w)]
End

Theorem addExtend_x_coverage_probes_8_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_8
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_9_def:
  addExtend_x_coverage_probes_9 = [
     (0xeb202c00w, AddExtend T T T 1w 0w 0w 0w 3w);
     (0xeb203000w, AddExtend T T T 1w 0w 0w 0w 4w);
     (0xeb204000w, AddExtend T T T 2w 0w 0w 0w 0w);
     (0xeb204400w, AddExtend T T T 2w 0w 0w 0w 1w);
     (0xeb204800w, AddExtend T T T 2w 0w 0w 0w 2w);
     (0xeb204c00w, AddExtend T T T 2w 0w 0w 0w 3w);
     (0xeb205000w, AddExtend T T T 2w 0w 0w 0w 4w);
     (0xeb206000w, AddExtend T T T 3w 0w 0w 0w 0w);
     (0xeb206400w, AddExtend T T T 3w 0w 0w 0w 1w);
     (0xeb206800w, AddExtend T T T 3w 0w 0w 0w 2w);
     (0xeb206c00w, AddExtend T T T 3w 0w 0w 0w 3w);
     (0xeb207000w, AddExtend T T T 3w 0w 0w 0w 4w);
     (0xeb208000w, AddExtend T T T 4w 0w 0w 0w 0w);
     (0xeb208400w, AddExtend T T T 4w 0w 0w 0w 1w);
     (0xeb208800w, AddExtend T T T 4w 0w 0w 0w 2w);
     (0xeb208c00w, AddExtend T T T 4w 0w 0w 0w 3w)]
End

Theorem addExtend_x_coverage_probes_9_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_9
Proof
  EVAL_TAC
QED

Definition addExtend_x_coverage_probes_10_def:
  addExtend_x_coverage_probes_10 = [
     (0xeb209000w, AddExtend T T T 4w 0w 0w 0w 4w);
     (0xeb20a000w, AddExtend T T T 5w 0w 0w 0w 0w);
     (0xeb20a400w, AddExtend T T T 5w 0w 0w 0w 1w);
     (0xeb20a800w, AddExtend T T T 5w 0w 0w 0w 2w);
     (0xeb20ac00w, AddExtend T T T 5w 0w 0w 0w 3w);
     (0xeb20b000w, AddExtend T T T 5w 0w 0w 0w 4w);
     (0xeb20c000w, AddExtend T T T 6w 0w 0w 0w 0w);
     (0xeb20c400w, AddExtend T T T 6w 0w 0w 0w 1w);
     (0xeb20c800w, AddExtend T T T 6w 0w 0w 0w 2w);
     (0xeb20cc00w, AddExtend T T T 6w 0w 0w 0w 3w);
     (0xeb20d000w, AddExtend T T T 6w 0w 0w 0w 4w);
     (0xeb20e000w, AddExtend T T T 7w 0w 0w 0w 0w);
     (0xeb20e400w, AddExtend T T T 7w 0w 0w 0w 1w);
     (0xeb20e800w, AddExtend T T T 7w 0w 0w 0w 2w);
     (0xeb20ec00w, AddExtend T T T 7w 0w 0w 0w 3w);
     (0xeb20f000w, AddExtend T T T 7w 0w 0w 0w 4w)]
End

Theorem addExtend_x_coverage_probes_10_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addExtend_x_coverage_probes_10
Proof
  EVAL_TAC
QED

Definition addCarry_w_coverage_probes_1_def:
  addCarry_w_coverage_probes_1 = [
     (0x1a000000w, AddCarry F F F 0w 0w 0w);
     (0x3a000000w, AddCarry F F T 0w 0w 0w);
     (0x5a000000w, AddCarry F T F 0w 0w 0w);
     (0x7a000000w, AddCarry F T T 0w 0w 0w)]
End

Theorem addCarry_w_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addCarry_w_coverage_probes_1
Proof
  EVAL_TAC
QED

Definition addCarry_x_coverage_probes_1_def:
  addCarry_x_coverage_probes_1 = [
     (0x9a000000w, AddCarry T F F 0w 0w 0w);
     (0xba000000w, AddCarry T F T 0w 0w 0w);
     (0xda000000w, AddCarry T T F 0w 0w 0w);
     (0xfa000000w, AddCarry T T T 0w 0w 0w)]
End

Theorem addCarry_x_coverage_probes_1_decode_encode:
  EVERY (λ(w,i). decode armv9_4 w = SOME i ∧ encode i = SOME w)
    addCarry_x_coverage_probes_1
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_1_def:
  a64_decode_unimplemented_probes_1 = [
     (0x12800000w);
     (0x72800000w);
     (0x52000000w);
     (0xd63f0000w)]
End

Theorem a64_decode_unimplemented_probes_1_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_1
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_2_def:
  a64_decode_unimplemented_probes_2 = [
     (0xd4000001w);
     (0xd503203fw);
     (0xd503205fw);
     (0xd503207fw)]
End

Theorem a64_decode_unimplemented_probes_2_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_2
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_3_def:
  a64_decode_unimplemented_probes_3 = [
     (0xd503209fw);
     (0xd50330bfw);
     (0xd503309fw);
     (0xd50330dfw)]
End

Theorem a64_decode_unimplemented_probes_3_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_3
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_4_def:
  a64_decode_unimplemented_probes_4 = [
     (0x3cc00c00w);
     (0x18000000w);
     (0x58000000w);
     (0x98000000w);
     (0x1c000000w);
     (0x5c000000w);
     (0x9c000000w);
     (0x08007c00w);
     (0x0800fc00w)]
End

Theorem a64_decode_unimplemented_probes_4_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_4
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_5_def:
  a64_decode_unimplemented_probes_5 = [
     (0x33000000w);
     (0x7a400000w);
     (0x4f105400w);
     (0x4f085400w)]
End

Theorem a64_decode_unimplemented_probes_5_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_5
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_6_def:
  a64_decode_unimplemented_probes_6 = [
     (0x6f100400w);
     (0x6f080400w);
     (0x6f104400w);
     (0x6f084400w)]
End

Theorem a64_decode_unimplemented_probes_6_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_6
Proof
  EVAL_TAC
QED


(* Valid architectural encodings intentionally unimplemented by arm64Isa. *)
Definition a64_decode_unimplemented_probes_7_def:
  a64_decode_unimplemented_probes_7 = [
     (0x5e000000w);
     (0x5e004000w);
     (0x72000000w);
     (0x38000820w);
     (0xa8000440w);
     (0x5ac01400w);
     (0xdac01400w);
     (0xd50320bfw);
     (0x5ac00400w);
     (0xdac00400w);
     (0xd4200000w);
     (0x4e228420w);
     (0x4e628420w);
     (0x6e228420w)]
End

Theorem a64_decode_unimplemented_probes_7_none:
  EVERY (λw. decode armv9_4 w = NONE) a64_decode_unimplemented_probes_7
Proof
  EVAL_TAC
QED

(* These equations keep execution evidence tied to the HOL transition theorem,
   including arithmetic and flag-setting state updates for every ADD form. *)
Theorem add_execute_with_forms:
  (execute_with ops (AddImm sf sub flags imm_shift d n imm) s =
     Next (write_arith ops T sf sub flags sub d (base_reg ops s n)
       (w2w imm << (if imm_shift then 12 else 0)) s)) ∧
  (execute_with ops (AddShift sf sub flags reg_shift d n m amount) s =
     Next (write_arith ops F sf sub flags sub d (gpr ops s n)
       (shift_reg sf reg_shift (w2n amount) (gpr ops s m)) s)) ∧
  (execute_with ops (AddExtend sf sub flags ext d n m ext_amount) s =
     Next (write_arith ops T sf sub flags sub d (base_reg ops s n)
       (extend_reg ext (gpr ops s m) << w2n ext_amount) s)) ∧
  (execute_with ops (AddCarry sf sub flags d n m) s =
     Next (write_arith ops F sf sub flags (FST (SND (SND s.nzcv))) d
       (gpr ops s n) (gpr ops s m) s))
Proof
  simp[execute_with_def]
QED

Theorem write_arith_flagged_outcome:
  (write_arith ops base sf sub T carry d x y s).nzcv =
    SND (arm_add_with_carry sf x (if sub then ¬y else y) carry)
Proof
  Cases_on `d = 31w` >>
    simp[write_arith_def, advance_def, set_gpr_def, set_base_def, pairTheory.UNCURRY]
QED

Theorem write_arith_gpr_result:
  d ≠ 31w ⇒
  (write_arith ops base sf sub flags carry d x y s).regs =
    ops.put_reg d (FST (arm_add_with_carry sf x (if sub then ¬y else y) carry)) s.regs
Proof
  strip_tac >>
  Cases_on `base` >> Cases_on `flags` >>
    simp[write_arith_def, advance_def, set_gpr_def, set_base_def, pairTheory.UNCURRY]
QED

Theorem write_arith_sp_result:
  (write_arith ops T sf sub F carry 31w x y s).sp =
    FST (arm_add_with_carry sf x (if sub then ¬y else y) carry)
Proof
  simp[write_arith_def, advance_def, set_gpr_def, set_base_def, pairTheory.UNCURRY]
QED

Theorem write_arith_unflagged_nzcv:
  (write_arith ops base sf sub F carry d x y s).nzcv = s.nzcv
Proof
  Cases_on `base` >> Cases_on `d = 31w` >>
    simp[write_arith_def, advance_def, set_gpr_def, set_base_def, pairTheory.UNCURRY]
QED

Definition a64_decode_coverage_probes_crc32_variants_def:
  a64_decode_coverage_probes_crc32_variants = [
     (0x1ac04000w, 40w);
     (0x1ac04400w, 40w);
     (0x1ac04800w, 40w);
     (0x9ac04c00w, 40w);
     (0x1ac05000w, 40w);
     (0x1ac05400w, 40w);
     (0x1ac05800w, 40w);
     (0x9ac05c00w, 40w)]
End

Theorem a64_decode_coverage_probes_crc32_variants_decode_encode:
  EVERY (λ(w,t). case decode armv9_4 w of NONE => F | SOME i => coverage_tag i = t ∧ encode i = SOME w)
    a64_decode_coverage_probes_crc32_variants
Proof
  EVAL_TAC
QED
