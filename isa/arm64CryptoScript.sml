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

Theorem vector_to_aes_aes_to_vector[simp]:
  ∀s. vector_to_aes (aes_to_vector s) = s
Proof
  simp[FORALL_BLOCK, vector_to_aes_def, aes_to_vector_def, from_state_def,
       to_state_def, aes_pack_column_def] >> BBLAST_TAC
QED

Theorem aes_to_vector_vector_to_aes[simp]:
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
(* 32-bit lane i of a vector, lane 0 in the least significant bits. *)
Definition lane32_def:
  lane32 i (x:word128) : word32 = w2w (x >>> (32 * i))
End

Definition lane64_def:
  lane64 i (x:word128) : word64 = w2w (x >>> (64 * i))
End

Definition lanes32_def:
  lanes32 (a:word32) (b:word32) (c:word32) (d:word32) : word128 =
    w2w a || (w2w b << 32) || (w2w c << 64) || (w2w d << 96)
End

Definition lanes64_def:
  lanes64 (lo:word64) (hi:word64) : word128 = w2w lo || (w2w hi << 64)
End

(* ROL (x, n) of the Arm pseudocode, for 0 < n < 32 and 0 < n < 64. *)
Definition rol32_def:
  rol32 (x:word32) n = x #>> (32 - n)
End

Definition rol64_def:
  rol64 (x:word64) n = x #>> (64 - n)
End

(* SHAchoose, SHAparity and SHAmajority, selected by SHA1C, SHA1P and SHA1M's
   opcode 0, 1 and 2. *)
Definition sha1_function_def:
  sha1_function (opc:word3) (x:word32) y z =
    if opc = 0w then ((y ?? z) && x) ?? z
    else if opc = 1w then x ?? y ?? z
    else (x && y) || ((x || y) && z)
End

(* One SHA-1 hash update per element of w. Each round rotates the 160-bit
   value y:x left by 32 bits. *)
Definition sha1_hash_def:
  sha1_hash opc 0 (x:word128) (y:word32) (w:word128) = x ∧
  sha1_hash opc (SUC n) x y w =
    let y' = y + rol32 (lane32 0 x) 5 +
             sha1_function opc (lane32 1 x) (lane32 2 x) (lane32 3 x) + lane32 0 w
    in sha1_hash opc n
         (lanes32 y' (lane32 0 x) (rol32 (lane32 1 x) 30) (lane32 2 x))
         (lane32 3 x) (w >>> 32)
End

Definition sha256_sigma0_def:
  sha256_sigma0 (x:word32) = (x #>> 2) ?? (x #>> 13) ?? (x #>> 22)
End

Definition sha256_sigma1_def:
  sha256_sigma1 (x:word32) = (x #>> 6) ?? (x #>> 11) ?? (x #>> 25)
End

(* SHA256hash of the Arm pseudocode: four rounds over the 256-bit value y:x,
   returning x for SHA256H and y for SHA256H2. *)
Definition sha256_hash_def:
  sha256_hash part1 0 (x:word128) (y:word128) (w:word128) = (if part1 then x else y) ∧
  sha256_hash part1 (SUC n) x y w =
    let chs = sha1_function 0w (lane32 0 y) (lane32 1 y) (lane32 2 y);
        maj = sha1_function 2w (lane32 0 x) (lane32 1 x) (lane32 2 x);
        t = lane32 3 y + sha256_sigma1 (lane32 0 y) + chs + lane32 0 w;
        x3 = t + lane32 3 x;
        y3 = t + sha256_sigma0 (lane32 0 x) + maj
    in sha256_hash part1 n
         (lanes32 y3 (lane32 0 x) (lane32 1 x) (lane32 2 x))
         (lanes32 x3 (lane32 0 y) (lane32 1 y) (lane32 2 y)) (w >>> 32)
End

Definition sha256_sigma_schedule0_def:
  sha256_sigma_schedule0 (e:word32) = (e #>> 7) ?? (e #>> 18) ?? (e >>> 3)
End

Definition sha256_schedule0_def:
  sha256_schedule0 (d:word128) (n:word128) =
    let t = (n << 96) || (d >>> 32) in
      lanes32 (sha256_sigma_schedule0 (lane32 0 t) + lane32 0 d)
              (sha256_sigma_schedule0 (lane32 1 t) + lane32 1 d)
              (sha256_sigma_schedule0 (lane32 2 t) + lane32 2 d)
              (sha256_sigma_schedule0 (lane32 3 t) + lane32 3 d)
End

Definition sha256_sigma_schedule1_def:
  sha256_sigma_schedule1 (e:word32) = (e #>> 17) ?? (e #>> 19) ?? (e >>> 10)
End

Definition sha256_schedule1_def:
  sha256_schedule1 (d:word128) (n:word128) (m:word128) =
    let t0 = (m << 96) || (n >>> 32);
        r0 = sha256_sigma_schedule1 (lane32 2 m) + lane32 0 d + lane32 0 t0;
        r1 = sha256_sigma_schedule1 (lane32 3 m) + lane32 1 d + lane32 1 t0;
        r2 = sha256_sigma_schedule1 r0 + lane32 2 d + lane32 2 t0;
        r3 = sha256_sigma_schedule1 r1 + lane32 3 d + lane32 3 t0
    in lanes32 r0 r1 r2 r3
End

(* SHA1C, SHA1P, SHA1M, SHA1SU0, SHA256H, SHA256H2, SHA256SU1 by opcode. *)
Definition sha_three_value_def:
  sha_three_value (opc:word3) (d:word128) (n:word128) (m:word128) =
    if w2n opc < 3 then sha1_hash opc 4 d (lane32 0 n) m
    else if opc = 3w then ((n << 64) || (d >>> 64)) ?? d ?? m
    else if opc = 4w then sha256_hash T 4 d n m
    else if opc = 5w then sha256_hash F 4 n d m
    else sha256_schedule1 d n m
End

(* SHA1H, SHA1SU1, SHA256SU0 by opcode. *)
Definition sha_two_value_def:
  sha_two_value (opc:word5) (d:word128) (n:word128) =
    if opc = 0w then w2w (rol32 (lane32 0 n) 30)
    else if opc = 1w then
      let t = d ?? (n >>> 32) in
        lanes32 (rol32 (lane32 0 t) 1) (rol32 (lane32 1 t) 1) (rol32 (lane32 2 t) 1)
                (rol32 (lane32 3 t) 1 ?? rol32 (lane32 0 t) 2)
    else sha256_schedule0 d n
End

Definition sha512_sum1_def:
  sha512_sum1 (x:word64) = (x #>> 14) ?? (x #>> 18) ?? (x #>> 41)
End

Definition sha512_sum0_def:
  sha512_sum0 (x:word64) = (x #>> 28) ?? (x #>> 34) ?? (x #>> 39)
End

Definition sha512_hash_def:
  sha512_hash (w:word128) (x:word128) (y:word128) =
    let hi = ((lane64 1 y && lane64 0 x) ?? (¬lane64 1 y && lane64 1 x)) +
             sha512_sum1 (lane64 1 y) + lane64 1 w;
        tmp = hi + lane64 0 y;
        lo = ((tmp && lane64 1 y) ?? (¬tmp && lane64 0 x)) + sha512_sum1 tmp + lane64 0 w
    in lanes64 lo hi
End

Definition sha512_hash2_def:
  sha512_hash2 (w:word128) (x:word128) (y:word128) =
    let y0 = lane64 0 y; y1 = lane64 1 y;
        hi = ((lane64 0 x && y1) ?? (lane64 0 x && y0) ?? (y1 && y0)) +
             sha512_sum0 y0 + lane64 1 w;
        lo = ((hi && y0) ?? (hi && y1) ?? (y1 && y0)) + sha512_sum0 hi + lane64 0 w
    in lanes64 lo hi
End

Definition sha512_sigma0_def:
  sha512_sigma0 (v:word64) = (v #>> 1) ?? (v #>> 8) ?? (v >>> 7)
End

Definition sha512_sigma1_def:
  sha512_sigma1 (v:word64) = (v #>> 19) ?? (v #>> 61) ?? (v >>> 6)
End

Definition sha512_schedule0_def:
  sha512_schedule0 (w:word128) (x:word128) =
    lanes64 (lane64 0 w + sha512_sigma0 (lane64 1 w))
            (lane64 1 w + sha512_sigma0 (lane64 0 x))
End

Definition sha512_schedule1_def:
  sha512_schedule1 (w:word128) (x:word128) (y:word128) =
    lanes64 (lane64 0 w + sha512_sigma1 (lane64 0 x) + lane64 0 y)
            (lane64 1 w + sha512_sigma1 (lane64 1 x) + lane64 1 y)
End

(* The SM4 S-box of GB/T 32907-2016; byte i is the i-th byte from the most
   significant end. *)
Definition sm4_sbox_table_def:
  sm4_sbox_table : num =
    0xd690e9fecce13db716b614c228fb2c052b679a762abe04c3aa441326498606999c4250f491ef987a33540b43edcfac62e4b31ca9c908e89580df94fa758f3fa64707a7fcf37317ba83593c19e6854fa8686b81b27164da8bf8eb0f4b70569d351e240e5e6358d1a225227c3b01217887d40046579fd327524c3602e7a0c4c89eeabf8ad240c738b5a3f7f2cef96115a1e0ae5da49b341a55ad933230f58cb1e31df6e22e8266ca60c02923ab0d534e6fd5db3745defd8e2f03ff6a726d6c5b518d1baf92bbddbc7f11d95c411f105ad80ac13188a5cd7bbd2d74d012b8e5b4b08969974a0c96777e65b9f109c56ec68418f07dec3adc4d2079ee5f3ed7cb3948
End

Definition sm4_sbox_def:
  sm4_sbox (b:word8) : word8 = n2w (sm4_sbox_table DIV 256 ** (255 - w2n b))
End

Definition sm4_sub_def:
  sm4_sub (x:word32) : word32 =
    w2w (sm4_sbox (w2w x)) || (w2w (sm4_sbox (w2w (x >>> 8))) << 8) ||
    (w2w (sm4_sbox (w2w (x >>> 16))) << 16) || (w2w (sm4_sbox (w2w (x >>> 24))) << 24)
End

(* Four SM4 rounds (SM4E with key, or SM4EKEY with constants), one per 32-bit
   element of the key vector. *)
Definition sm4_rounds_def:
  sm4_rounds key 0 (r:word128) (k:word128) = r ∧
  sm4_rounds key (SUC n) r k =
    let t = sm4_sub (lane32 3 r ?? lane32 2 r ?? lane32 1 r ?? lane32 0 k);
        t = if key then t ?? rol32 t 13 ?? rol32 t 23
            else t ?? rol32 t 2 ?? rol32 t 10 ?? rol32 t 18 ?? rol32 t 24
    in sm4_rounds key n (lanes32 (lane32 1 r) (lane32 2 r) (lane32 3 r) (t ?? lane32 0 r))
         (k >>> 32)
End

(* The SM3 permutation P1. *)
Definition sm3_p1_def:
  sm3_p1 (v:word32) = v ?? rol32 v 15 ?? rol32 v 23
End

Definition sm3_partw1_def:
  sm3_partw1 (d:word128) (n:word128) (m:word128) =
    let x = d ?? n;
        r0 = sm3_p1 (lane32 0 x ?? rol32 (lane32 1 m) 15);
        r1 = sm3_p1 (lane32 1 x ?? rol32 (lane32 2 m) 15);
        r2 = sm3_p1 (lane32 2 x ?? rol32 (lane32 3 m) 15);
        r3 = sm3_p1 (lane32 3 x ?? rol32 r0 15)
    in lanes32 r0 r1 r2 r3
End

Definition sm3_partw2_def:
  sm3_partw2 (d:word128) (n:word128) (m:word128) =
    let t = n ?? lanes32 (rol32 (lane32 0 m) 7) (rol32 (lane32 1 m) 7)
                         (rol32 (lane32 2 m) 7) (rol32 (lane32 3 m) 7);
        r = d ?? t;
        t2 = sm3_p1 (rol32 (lane32 0 t) 15)
    in lanes32 (lane32 0 r) (lane32 1 r) (lane32 2 r) (lane32 3 r ?? t2)
End

(* SM3TT1A, SM3TT1B, SM3TT2A and SM3TT2B by opcode, using element i of m. *)
Definition sm3_tt_def:
  sm3_tt (opc:word2) i (d:word128) (n:word128) (m:word128) =
    let a = lane32 3 d; b = lane32 2 d; c = lane32 1 d; e = lane32 0 d;
        w = lane32 i m
    in
      if opc = 0w ∨ opc = 1w then
        let ss2 = lane32 3 n ?? rol32 a 12;
            f = if opc = 0w then c ?? a ?? b else (a && c) || (a && b) || (c && b)
        in lanes32 c (rol32 b 9) a (f + e + ss2 + w)
      else
        let g = if opc = 2w then c ?? a ?? b else (a && b) || (¬a && c);
            tt = g + e + lane32 3 n + w
        in lanes32 c (rol32 b 19) a (tt ?? rol32 tt 9 ?? rol32 tt 17)
End

(* EOR3, BCAX and SM3SS1 by op0. *)
Definition crypto_four_value_def:
  crypto_four_value (op0:word2) (n:word128) (m:word128) (a:word128) =
    if op0 = 0w then n ?? m ?? a
    else if op0 = 1w then n ?? (m && ¬a)
    else (w2w (rol32 (rol32 (lane32 3 n) 12 + lane32 3 m + lane32 3 a) 7) : word128) << 96
End

(* SHA512H, SHA512H2, SHA512SU1, RAX1 (sm = F) and SM3PARTW1, SM3PARTW2,
   SM4EKEY (sm = T) by opcode. *)
Definition crypto_three_value_def:
  crypto_three_value sm (opc:word2) (d:word128) (n:word128) (m:word128) =
    if ¬sm then
      if opc = 0w then sha512_hash d n m
      else if opc = 1w then sha512_hash2 d n m
      else if opc = 2w then sha512_schedule1 d n m
      else n ?? lanes64 (rol64 (lane64 0 m) 1) (rol64 (lane64 1 m) 1)
    else if opc = 0w then sm3_partw1 d n m
    else if opc = 1w then sm3_partw2 d n m
    else sm4_rounds T 4 n m
End

Definition xar_value_def:
  xar_value (n:word128) (m:word128) imm =
    let t = n ?? m in lanes64 (lane64 0 t #>> imm) (lane64 1 t #>> imm)
End

(* SHA512SU0 and SM4E. *)
Definition crypto_two_value_def:
  crypto_two_value (opc:word2) (d:word128) (n:word128) =
    if opc = 0w then sha512_schedule0 d n else sm4_rounds F 4 d n
End
