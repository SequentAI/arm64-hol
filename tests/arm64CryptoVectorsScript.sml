(* SM4 and SM3 standard examples computed with the SM4EKEY, SM4E, SM3SS1,
   SM3TT*, SM3PARTW1, SM3PARTW2 and EXT semantics. Hosts without FEAT_SM3 and
   FEAT_SM4 cannot run native probes for these instructions. Each vector holds
   32-bit word i of a block in lane i. *)
Theory arm64CryptoVectors
Ancestors arm64Isa arm64IsaCv arm64Crypto
Libs cv_transLib wordsLib

(* CK_j has bytes (4j + k) * 7 mod 256, most significant first. *)
Definition sm4_ck_word_def:
  sm4_ck_word j : word32 =
    n2w ((28 * j MOD 256) * 2 ** 24 + ((28 * j + 7) MOD 256) * 2 ** 16 +
         ((28 * j + 14) MOD 256) * 2 ** 8 + (28 * j + 21) MOD 256)
End

Definition sm4_ck_def:
  sm4_ck i =
    lanes32 (sm4_ck_word (4 * i)) (sm4_ck_word (4 * i + 1))
            (sm4_ck_word (4 * i + 2)) (sm4_ck_word (4 * i + 3))
End

(* Each step derives four round keys with SM4EKEY, then runs four rounds with
   SM4E. *)
Definition sm4_run_def:
  sm4_run 0 k x = x ∧
  sm4_run (SUC n) k x =
    let k' = crypto_three_value T 2w 0w k (sm4_ck (7 - n)) in
      sm4_run n k' (crypto_two_value 1w x k')
End

val () = app cv_auto_trans [sm4_ck_word_def, sm4_ck_def, sm4_run_def];

(* GB/T 32907-2016 Example 1: the key and the plaintext are both
   0123456789abcdeffedcba9876543210; SM4E leaves the output words reversed. *)
Theorem sm4_standard_example = EQT_ELIM (cv_eval ``
  sm4_run 8
    (lanes32 0x01234567w 0x89abcdefw 0xfedcba98w 0x76543210w ??
     lanes32 0xa3b1bac6w 0x56aa3350w 0x677d9197w 0xb27022dcw)
    (lanes32 0x01234567w 0x89abcdefw 0xfedcba98w 0x76543210w) =
  lanes32 0x536e4246w 0x86b3e94fw 0xd206965ew 0x681edf34w``);

(* Round j's constant T_j <<< (j mod 32), in the top lane for SM3SS1. *)
Definition sm3_t_def:
  sm3_t j : word128 =
    w2w (rol32 (if j < 16 then 0x79cc4519w else 0x7a879d8aw) (j MOD 32)) << 96
End

(* abcd holds A, B, C, D in lanes 3, 2, 1, 0; efgh holds E, F, G, H likewise. *)
Definition sm3_round_def:
  sm3_round j i (abcd, efgh) w w' =
    let ss1 = crypto_four_value 2w abcd (sm3_t j) efgh in
      (sm3_tt (if j < 16 then 0w else 1w) i abcd ss1 w',
       sm3_tt (if j < 16 then 2w else 3w) i efgh ss1 w)
End

Definition sm3_quad_def:
  sm3_quad k st w0 w1 =
    let w' = w0 ?? w1 in
      sm3_round (4 * k + 3) 3 (sm3_round (4 * k + 2) 2
        (sm3_round (4 * k + 1) 1 (sm3_round (4 * k) 0 st w0 w') w0 w') w0 w') w0 w'
End

(* Message words 4k + 16 to 4k + 19 from words 4k to 4k + 15. *)
Definition sm3_expand_def:
  sm3_expand g0 g1 g2 g3 =
    sm3_partw2 (sm3_partw1 (simd_ext 12 g1 g2) g0 g3) (simd_ext 8 g2 g3) (simd_ext 12 g0 g1)
End

Definition sm3_quads_def:
  sm3_quads 0 k st g0 g1 g2 g3 = st ∧
  sm3_quads (SUC n) k st g0 g1 g2 g3 =
    sm3_quads n (k + 1) (sm3_quad k st g0 g1) g1 g2 g3 (sm3_expand g0 g1 g2 g3)
End

Definition sm3_compress_def:
  sm3_compress (abcd, efgh) g0 g1 g2 g3 =
    let (abcd', efgh') = sm3_quads 16 0 (abcd, efgh) g0 g1 g2 g3 in
      (abcd ?? abcd', efgh ?? efgh')
End

val () = app cv_auto_trans [sm3_t_def, sm3_round_def, sm3_quad_def, sm3_expand_def,
                            sm3_quads_def, sm3_compress_def];

(* GB/T 32905-2016 Example 1: SM3("abc") is one padded block. *)
Theorem sm3_standard_example = EQT_ELIM (cv_eval ``
  sm3_compress
    (lanes32 0xda8a0600w 0x172442d7w 0x4914b2b9w 0x7380166fw,
     lanes32 0xb0fb0e4ew 0xe38dee4dw 0x163138aaw 0xa96f30bcw)
    (lanes32 0x61626380w 0w 0w 0w) 0w 0w (lanes32 0w 0w 0w 0x18w) =
  (lanes32 0xdc10e4e2w 0xd1f2d46bw 0x62eeedd9w 0x66c7f0f4w,
   lanes32 0x8f4ba8e0w 0x297da02bw 0x5cf2f7a2w 0x4167c487w)``);
