(* A64 crypto operations use the least significant vector byte as byte 0. *)
Theory arm64Crypto
Ancestors RoundOp words
Libs blastLib wordsLib

Definition crc32_bit_def:
  crc32_bit (poly:word32) (crc:word32) bit =
    (crc >>> 1) ?? (if word_bit 0 crc ≠ bit then poly else 0w)
End

Definition crc32_bits_def:
  crc32_bits poly 0 crc (src:word64) = crc ∧
  crc32_bits poly (SUC n) crc src =
    crc32_bits poly n (crc32_bit poly crc (word_bit 0 src)) (src >>> 1)
End

Definition crc32_value_def:
  crc32_value castagnoli (size:word2) crc src =
    crc32_bits (if castagnoli then 0x82f63b78w else 0xedb88320w)
      (8 * 2 ** w2n size) crc src
End

(* XOR the shifted multiplicand for each set bit of the multiplier. *)
Definition clmul_def:
  clmul 0 (a:word64) (b:word64) = 0w : word128 ∧
  clmul (SUC n) a b =
    clmul n a b ?? (if word_bit n b then w2w a << n else 0w)
End

Definition pmull_value_def:
  pmull_value high (x:word128) (y:word128) =
    let shift = if high then 64 else 0 in
      clmul 64 (w2w (x >>> shift)) (w2w (y >>> shift))
End

Datatype:
  aes_op = Aese | Aesd | Aesmc | Aesimc
End

Definition vector_to_aes_def:
  vector_to_aes (x:word128) =
    to_state ((7 >< 0) x, (15 >< 8) x, (23 >< 16) x, (31 >< 24) x,
              (39 >< 32) x, (47 >< 40) x, (55 >< 48) x, (63 >< 56) x,
              (71 >< 64) x, (79 >< 72) x, (87 >< 80) x, (95 >< 88) x,
              (103 >< 96) x, (111 >< 104) x, (119 >< 112) x, (127 >< 120) x)
End

Definition aes_pack_column_def:
  aes_pack_column (a:word8) (b:word8) (c:word8) (d:word8) : word32 =
    d @@ ((c @@ ((b @@ a) : word16)) : word24)
End

Definition aes_to_vector_def:
  aes_to_vector s : word128 =
    let (b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15) =
      from_state s in
    let c0 = aes_pack_column b0 b1 b2 b3;
        c1 = aes_pack_column b4 b5 b6 b7;
        c2 = aes_pack_column b8 b9 b10 b11;
        c3 = aes_pack_column b12 b13 b14 b15 in
      ((c3 @@ c2) : word64) @@ ((c1 @@ c0) : word64)
End

(* The two conversions are inverse at the HOL word/state boundary.  Keep the
   cancellation laws in the ISA theory so clients do not repeat the bit-vector
   proof in each crypto contract. *)
Theorem aes_word_to_state[simp]:
  ∀s. vector_to_aes (aes_to_vector s) = s
Proof
  simp[FORALL_BLOCK, vector_to_aes_def, aes_to_vector_def, from_state_def,
       to_state_def, aes_pack_column_def] >> BBLAST_TAC
QED

Theorem aes_state_to_word[simp]:
  ∀x. aes_to_vector (vector_to_aes x) = x
Proof
  simp[vector_to_aes_def, aes_to_vector_def, to_state_Inversion,
       aes_pack_column_def] >> BBLAST_TAC
QED

(* AESE and AESD XOR their operands before the FIPS 197 round transforms.
   The MixColumns forms use only the source register. *)
Definition aes_value_def:
  aes_value Aese x k = aes_to_vector (SubBytes (ShiftRows (vector_to_aes (x ?? k)))) ∧
  aes_value Aesd x k = aes_to_vector (InvSubBytes (InvShiftRows (vector_to_aes (x ?? k)))) ∧
  aes_value Aesmc x k = aes_to_vector (MixColumns (vector_to_aes k)) ∧
  aes_value Aesimc x k = aes_to_vector (InvMixColumns (vector_to_aes k))
End
