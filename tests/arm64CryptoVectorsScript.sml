(* SM4 and SM3 standard examples computed by stepping assembled SM4EKEY, SM4E,
   SM3SS1, SM3TT*, SM3PARTW1 and SM3PARTW2 instructions. Hosts without FEAT_SM3
   and FEAT_SM4 cannot run native probes for these instructions. Each vector
   holds 32-bit word i of a block in lane i. *)
Theory arm64CryptoVectors
Ancestors arm64Isa arm64IsaCv arm64Crypto
Libs cv_transLib wordsLib

Definition put_vregs_def:
  put_vregs [] tree = tree ∧
  put_vregs (rv::rest) tree = put_vregs rest (insert (FST rv) (SND rv) tree)
End

(* The instruction word at 4096, executable, with the given vector registers. *)
Definition word_state_def:
  word_state (w:word32) regs : finite_state =
    arm64_machine LN 0w 4096w (F,F,F,F) (put_vregs regs LN)
      (insert 4096 (w2w w) (insert 4097 (w2w (w >>> 8))
        (insert 4098 (w2w (w >>> 16)) (insert 4099 (w2w (w >>> 24)) LN))))
      (insert 4096 (perm T F T) (insert 4097 (perm T F T)
        (insert 4098 (perm T F T) (insert 4099 (perm T F T) LN))))
End

(* Vector register d after one step; zero if the step faults. *)
Definition run_word_def:
  run_word w regs d =
    case step_cv armv9_4 (word_state w regs) of
      Next s => (case lookup d s.vregs of NONE => 0w | SOME v => v)
    | Fault reason => 0w
End

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

(* Each step derives four round keys with SM4EKEY V3.4S, V1.4S, V2.4S, then
   runs four rounds with SM4E V0.4S, V1.4S. *)
Definition sm4_run_def:
  sm4_run 0 k x = x ∧
  sm4_run (SUC n) k x =
    let k' = run_word 0xce62c823w [(1,k); (2,sm4_ck (7 - n))] 3 in
      sm4_run n k' (run_word 0xcec08420w [(0,x); (1,k')] 0)
End

val () = app cv_auto_trans [put_vregs_def, word_state_def, run_word_def,
                            sm4_ck_word_def, sm4_ck_def, sm4_run_def];

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

(* SM3TT1A V8.4S, V5.4S, V10.S[i]; SM3TT1B likewise; SM3TT2A V9.4S, V5.4S,
   V0.S[i]; SM3TT2B likewise. *)
Definition sm3_tt_word_def:
  sm3_tt_word (opc:num) (i:num) : word32 =
    if opc = 0 then
      (if i = 0 then 0xce4a80a8w else if i = 1 then 0xce4a90a8w
       else if i = 2 then 0xce4aa0a8w else 0xce4ab0a8w)
    else if opc = 1 then
      (if i = 0 then 0xce4a84a8w else if i = 1 then 0xce4a94a8w
       else if i = 2 then 0xce4aa4a8w else 0xce4ab4a8w)
    else if opc = 2 then
      (if i = 0 then 0xce4088a9w else if i = 1 then 0xce4098a9w
       else if i = 2 then 0xce40a8a9w else 0xce40b8a9w)
    else if i = 0 then 0xce408ca9w else if i = 1 then 0xce409ca9w
    else if i = 2 then 0xce40aca9w else 0xce40bca9w
End

(* abcd holds A, B, C, D in lanes 3, 2, 1, 0; efgh holds E, F, G, H likewise.
   SS1 comes from SM3SS1 V5.4S, V8.4S, V11.4S, V9.4S. *)
Definition sm3_round_def:
  sm3_round j i (abcd, efgh) w w' =
    let ss1 = run_word 0xce4b2505w [(8,abcd); (11,sm3_t j); (9,efgh)] 5 in
      (run_word (sm3_tt_word (if j < 16 then 0 else 1) i) [(8,abcd); (5,ss1); (10,w')] 8,
       run_word (sm3_tt_word (if j < 16 then 2 else 3) i) [(9,efgh); (5,ss1); (0,w)] 9)
End

Definition sm3_quad_def:
  sm3_quad k st w0 w1 =
    let w' = w0 ?? w1 in
      sm3_round (4 * k + 3) 3 (sm3_round (4 * k + 2) 2
        (sm3_round (4 * k + 1) 1 (sm3_round (4 * k) 0 st w0 w') w0 w') w0 w') w0 w'
End

(* Message words 4k + 16 to 4k + 19 from words 4k to 4k + 15, with
   SM3PARTW1 V4.4S, V0.4S, V3.4S and SM3PARTW2 V4.4S, V7.4S, V6.4S. *)
Definition sm3_expand_def:
  sm3_expand g0 g1 g2 g3 =
    let w1 = run_word 0xce63c004w [(4,simd_ext 12 g1 g2); (0,g0); (3,g3)] 4 in
      run_word 0xce66c4e4w [(4,w1); (7,simd_ext 8 g2 g3); (6,simd_ext 12 g0 g1)] 4
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

val () = app cv_auto_trans [sm3_t_def, sm3_tt_word_def, sm3_round_def, sm3_quad_def, sm3_expand_def,
                            sm3_quads_def, sm3_compress_def];

(* GB/T 32905-2016 Example 1: SM3("abc") is one padded block. *)
Theorem sm3_standard_example = EQT_ELIM (cv_eval ``
  sm3_compress
    (lanes32 0xda8a0600w 0x172442d7w 0x4914b2b9w 0x7380166fw,
     lanes32 0xb0fb0e4ew 0xe38dee4dw 0x163138aaw 0xa96f30bcw)
    (lanes32 0x61626380w 0w 0w 0w) 0w 0w (lanes32 0w 0w 0w 0x18w) =
  (lanes32 0xdc10e4e2w 0xd1f2d46bw 0x62eeedd9w 0x66c7f0f4w,
   lanes32 0x8f4ba8e0w 0x297da02bw 0x5cf2f7a2w 0x4167c487w)``);
