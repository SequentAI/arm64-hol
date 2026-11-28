(* Word-level equations for the specification's integer and bit-list
   arithmetic, used in place of their definitions in evaluation. *)
Theory aslLemmas
Ancestors arm64Asl integer_word bitstring bit list arithmetic
Libs wordsLib intLib

Theorem bools_of_nat_aux_genlist:
  ∀k x acc.
    bools_of_nat_aux (&k) x acc = GENLIST (λi. BIT (k - 1 - i) x) k ++ acc
Proof
  Induct >> simp[Once sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw] >>
  rpt gen_tac >>
  `¬(&SUC k ≤ 0 : int) ∧ &SUC k - 1 = &k : int` by intLib.ARITH_TAC >>
  simp[GENLIST, SNOC_APPEND, GENLIST_FUN_EQ, BIT_DEF] >> rw[] >>
  `k - i = SUC (k - (i + 1))` by decide_tac >>
  simp[EXP, DIV_DIV_DIV_MULT]
QED

Theorem bools_of_nat_w2v:
  bools_of_nat (&dimindex(:α)) x = w2v (n2w x : α word)
Proof
  simp[sail2_valuesTheory.bools_of_nat_def, bools_of_nat_aux_genlist, w2v_def,
       GENLIST_FUN_EQ, wordsTheory.word_index]
QED

Theorem integer_subrange_nat:
  integer_subrange (&n) (&dimindex(:α) - 1) 0 : α word = n2w n
Proof
  `&dimindex(:α) - 1 - 0 + 1 = &dimindex(:α) : int ∧
   0 + &dimindex(:α) - 1 = &dimindex(:α) - 1 : int ∧
   &dimindex(:α) - 1 + 1 = &dimindex(:α) : int ∧
   &dimindex(:α) - 1 - (&dimindex(:α) - 1) = 0 : int`
    by intLib.ARITH_TAC >>
  simp[armv9_p1Theory.integer_subrange_def, sail2_operators_mwordsTheory.get_slice_int_def,
       sail2_operatorsTheory.get_slice_int_bv_def,
       sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
       sail2_valuesTheory.bools_of_int_def, sail2_valuesTheory.subrange_list_def,
       sail2_valuesTheory.subrange_list_dec_def, sail2_valuesTheory.subrange_list_inc_def,
       bools_of_nat_w2v, length_w2v, v2w_w2v, integerTheory.int_ge,
       sail2_valuesTheory.nat_of_int_def] >>
  simp[TAKE_LENGTH_TOO_LONG, length_w2v, v2w_w2v]
QED

Theorem add_with_carry_overflow:
  ∀x y b. SND (SND (add_with_carry (x:α word, y, b))) ⇔
  w2i (FST (add_with_carry (x, y, b))) ≠ w2i x + w2i y + (if b then 1 else 0)
Proof
  rpt gen_tac >>
  qspec_then `x` (qx_choose_then `a` strip_assume_tac) wordsTheory.ranged_word_nchotomy >>
  qspec_then `y` (qx_choose_then `c` strip_assume_tac) wordsTheory.ranged_word_nchotomy >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `dimword(:α) = 2 * INT_MIN(:α) ∧ 0 < INT_MIN(:α)`
    by simp[wordsTheory.dimword_IS_TWICE_INT_MIN] >>
  qabbrev_tac `u = a + c + if b then 1 else 0` >>
  `u MOD dimword(:α) = if u < dimword(:α) then u else u - dimword(:α)`
    by (rw[LESS_MOD] >> irule MOD_UNIQUE >> qexists_tac `1` >>
        unabbrev_all_tac >> Cases_on `b` >> gs[]) >>
  simp[wordsTheory.add_with_carry_def, w2i_eq_w2n, wordsTheory.word_msb_n2w_numeric] >>
  unabbrev_all_tac >> Cases_on `b` >> gs[] >> rw[] >>
  qpat_x_assum `_ MOD _ = _` kall_tac >> intLib.ARITH_TAC
QED

Definition flags_word_def:
  flags_word (n, z, c, v) = v2w [n; z; c; v] : 4 word
End

Theorem word1_cases[local]:
  ∀w:1 word. w = 0w ∨ w = 1w
Proof
  blastLib.BBLAST_TAC
QED

Theorem vec_of_bits_msb:
  vec_of_bits [access_vec_dec (w:α word) (&dimindex(:α) - 1)] : 1 word =
  v2w [word_msb w]
Proof
  `&dimindex(:α) - 1 - (&dimindex(:α) - 1) = 0 : int` by intLib.ARITH_TAC >>
  `w2v w ≠ [] ∧ HD (w2v w) = w ' (dimindex(:α) - 1)`
    by simp[w2v_def, HD_GENLIST_COR, GENLIST_EQ_NIL] >>
  simp[rich_listTheory.MAP_HD, sail2_operators_mwordsTheory.vec_of_bits_def,
       sail2_operators_mwordsTheory.access_vec_dec_def,
       sail2_valuesTheory.access_bv_dec_def, sail2_valuesTheory.access_list_def,
       sail2_valuesTheory.access_list_dec_def, sail2_valuesTheory.access_list_inc_def,
       sail2_valuesTheory.of_bits_failwith_def, sail2_valuesTheory.maybe_failwith_def,
       sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
       sail2_valuesTheory.nat_of_int_def, length_w2v, EL_MAP, el_w2v, wordsTheory.word_msb_def] >>
  Cases_on `w ' (dimindex(:α) - 1)` >>
  simp[sail2_valuesTheory.bitU_of_bool_def, sail2_valuesTheory.bool_of_bitU_def,
       sail2_valuesTheory.just_list_def]
QED

Theorem concat_flags[local]:
  concat_vec (concat_vec (concat_vec (v2w [a] : 1 word) (b : 1 word) : 2 word)
                (c : 1 word) : 3 word) (d : 1 word) : 4 word =
  v2w [a; b = 1w; c = 1w; d = 1w]
Proof
  simp[sail2_operators_mwordsTheory.concat_vec_def] >>
  Cases_on `a` >>
  qspec_then `b` strip_assume_tac word1_cases >>
  qspec_then `c` strip_assume_tac word1_cases >>
  qspec_then `d` strip_assume_tac word1_cases >>
  rw[] >> EVAL_TAC
QED

Theorem AddWithCarry_add_with_carry:
  AddWithCarry (x:α word) y (c:1 word) =
    (FST (add_with_carry (x, y, c = 1w)),
     flags_word (result_flags (add_with_carry (x, y, c = 1w))))
Proof
  qspecl_then [`x`, `y`, `c = 1w`] mp_tac add_with_carry_overflow >>
  qspec_then `c` strip_assume_tac word1_cases >> gvs[] >>
  simp[armv9_p3Theory.AddWithCarry_def, lemTheory.w2ui_def, wordsTheory.word_len_def,
       integerTheory.INT_ADD, integer_subrange_nat, vec_of_bits_msb,
       armv9_p1Theory.IsZero_def, sail2_operators_mwordsTheory.zeros_def, concat_flags,
       wordsTheory.add_with_carry_def, arm64IsaTheory.result_flags_def, flags_word_def] >>
  rw[]
QED

(* The specification reads and writes general-purpose registers through a
   choice among the 31 of them; these state that choice for an arbitrary
   register number. *)

(* Proves ∀k. k < c ⇒ P k by proving each instance with c. *)
fun bounded_forall_conv c t =
  (numLib.BOUNDED_FORALL_CONV c THENC
   TRY_CONV (RAND_CONV (bounded_forall_conv c))) t

val register_conv = SIMP_CONV bool_ss [FUN_EQ_THM] THENC EVAL

Theorem read_gpr_num[local]:
  ∀k. k < 31 ⇒
      read_gpr (&k) =
        (λs. {(Value (s.regstate.bitvector_64_reg ("R" ++ num_to_dec_string k)), s)})
Proof
  CONV_TAC (bounded_forall_conv register_conv) >> simp[]
QED

Theorem read_gpr_eq:
  read_gpr n =
    if 0 ≤ n ∧ n < 31 then
      (λs. {(Value (s.regstate.bitvector_64_reg ("R" ++ num_to_dec_string (Num n))), s)})
    else read_regS R30_ref
Proof
  IF_CASES_TAC
  >- (`∃k. n = &k ∧ k < 31` by (qexists_tac `Num n` >> intLib.ARITH_TAC) >>
      gvs[read_gpr_num]) >>
  simp[armv9_p1Theory.read_gpr_def] >>
  rpt (IF_CASES_TAC >- gvs[]) >> rw[]
QED

Theorem write_gpr_num[local]:
  ∀k. k < 31 ⇒
      write_gpr (&k) v =
        (λs. {(Value (),
               s with regstate :=
                 s.regstate with bitvector_64_reg :=
                   (λreg. if reg = "R" ++ num_to_dec_string k then v
                          else s.regstate.bitvector_64_reg reg))})
Proof
  CONV_TAC (bounded_forall_conv register_conv) >> simp[]
QED

Theorem write_gpr_eq:
  write_gpr n v =
    if 0 ≤ n ∧ n < 31 then
      (λs. {(Value (),
             s with regstate :=
               s.regstate with bitvector_64_reg :=
                 (λreg. if reg = "R" ++ num_to_dec_string (Num n) then v
                        else s.regstate.bitvector_64_reg reg))})
    else write_regS R30_ref v
Proof
  IF_CASES_TAC
  >- (`∃k. n = &k ∧ k < 31` by (qexists_tac `Num n` >> intLib.ARITH_TAC) >>
      gvs[write_gpr_num]) >>
  simp[armv9_p1Theory.write_gpr_def] >>
  rpt (IF_CASES_TAC >- gvs[]) >> rw[]
QED

(* Register numbers are words' unsigned values; these state comparisons of
   them as comparisons of words, which bit-blasting decides. *)

Theorem w2n_lt_word_lo:
  k < dimword(:α) ⇒ (w2n (w:α word) < k ⇔ w <+ n2w k)
Proof
  simp[wordsTheory.WORD_LO]
QED

Theorem word_lo_w2n:
  k < dimword(:α) ⇒ (k < w2n (w:α word) ⇔ n2w k <+ w)
Proof
  simp[wordsTheory.WORD_LO]
QED

(* Bounds checks on list indices compare differences with 0. *)
Theorem int_sub_lt_0:
  &a − &b < 0 : int ⇔ a < b
Proof
  intLib.ARITH_TAC
QED

Theorem w2n_eq_n2w:
  k < dimword(:α) ⇒ (w2n (w:α word) = k ⇔ w = n2w k)
Proof
  Cases_on `w` >> simp[]
QED

Theorem w2n_le_word_ls:
  k < dimword(:α) ⇒ (w2n (w:α word) ≤ k ⇔ w <=+ n2w k)
Proof
  simp[wordsTheory.WORD_LS]
QED

(* A lookup in the specification's memory is a bounds check. *)
Theorem FLOOKUP_asl_mem:
  FLOOKUP (asl_mem m) k =
    if k < 18446744073709551616 then SOME (MAP bitU_of_bool (w2v (m (n2w k))))
    else NONE
Proof
  simp[asl_mem_def, finite_mapTheory.FLOOKUP_FUN_FMAP]
QED

(* Alignment, which the specification computes with integer division, as
   shifts of words. *)
Theorem n2w_align[local]:
  ∀k. n2w (2 ** k * (w2n (x:α word) DIV 2 ** k)) : α word = x >>> k << k
Proof
  gen_tac >>
  `x >>> k = n2w (w2n x DIV 2 ** k)`
    by (`w2n (x >>> k) = w2n x DIV 2 ** k` by simp[wordsTheory.w2n_lsr] >>
        pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  simp[wordsTheory.WORD_MUL_LSL, wordsTheory.word_mul_n2w]
QED

Theorem align_bits_word:
  align_bits instance_Sail2_values_Bitvector_Machine_word_mword_dict (x:α word) y =
    if y = 1 then x else if y = 2 then x >>> 1 << 1
    else if y = 4 then x >>> 2 << 2 else if y = 8 then x >>> 3 << 3
    else if y = 16 then x >>> 4 << 4
    else i2w (&w2n x / y * y)
Proof
  simp[sail2_valuesTheory.align_bits_def, sail2_valuesTheory.align_int_def,
       sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
       lemTheory.w2ui_def] >>
  rw[] >> simp[integer_wordTheory.i2w_pos] >>
  simp (map (fn k => SIMP_RULE (srw_ss()) [] (Q.SPEC k n2w_align))
            [`1`, `2`, `3`, `4`])
QED

(* Register numbers below 31 name general-purpose registers. *)
Theorem w2n_lt_31:
  w2n (w:word5) < 31 ⇔ w ≠ 31w
Proof
  Cases_on `w` >> fs[]
QED

Theorem word5_eq_n2w:
  k < 32 ⇒ ((w:word5) = n2w k ⇔ w2n w = k)
Proof
  Cases_on `w` >> fs[]
QED

(* Memory reads check that each byte address, w2n a + k, is in range. *)
Theorem w2n_lt_64:
  w2n (w:word64) < 18446744073709551616
Proof
  mp_tac (INST_TYPE [alpha |-> ``:64``] wordsTheory.w2n_lt) >> simp[]
QED

Theorem w2n_add_lt_64:
  0 < k ∧ k < 18446744073709551616 ⇒
  (w2n (w:word64) + k < 18446744073709551616 ⇔
   w <+ n2w (18446744073709551616 - k))
Proof
  strip_tac >> simp[wordsTheory.WORD_LO]
QED

(* Memory reads address byte k of an access as n2w (w2n a + k). *)
Theorem n2w_w2n_add:
  n2w (w2n (w:α word) + k) = w + n2w k
Proof
  simp[GSYM wordsTheory.word_add_n2w]
QED

(* Addresses are sums computed through integers; as words, bit-blasting can
   decide the guards on them (alignment, say). *)
Theorem add_vec_word:
  add_vec (l:α word) r = l + r
Proof
  rw[sail2_operators_mwordsTheory.add_vec_def, sail2_valuesTheory.int_of_mword_def,
     lemTheory.w2ui_def, integerTheory.INT_ADD, integer_wordTheory.i2w_def,
     wordsTheory.word_add_def]
QED

Theorem add_vec_int_word:
  add_vec_int (l:α word) r = l + i2w r
Proof
  rw[sail2_operators_mwordsTheory.add_vec_int_def, sail2_operatorsTheory.arith_op_bv_int_def,
     sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def,
     sail2_valuesTheory.int_of_mword_def, lemTheory.w2ui_def, integerTheory.INT_ADD,
     integer_wordTheory.i2w_def, wordsTheory.word_add_def]
QED

(* Loops of the specification (over the bytes of an unaligned access, say)
   by their recursion equation. *)
Theorem foreachM_rw =
  fst (Defn.tprove_no_defn
    ((sail2_monadic_combinatorsTheory.foreachM_def,
      sail2_monadic_combinatorsTheory.foreachM_ind),
     WF_REL_TAC `measure (LENGTH o FST)` >> rw[]))

(* Bits of memory are bitU_of_bool of the bits of bytes; reading them back
   gives the bits. *)
Theorem bool_of_bitU_eq:
  bool_of_bitU B0 = SOME F ∧ bool_of_bitU B1 = SOME T ∧ bool_of_bitU BU = NONE ∧
  bool_of_bitU (if b then B1 else B0) = SOME b
Proof
  simp[sail2_valuesTheory.bool_of_bitU_def] >> Cases_on `b` >> simp[]
QED

(* The feature register as a list of literals, for evaluation. *)
Theorem asl_features_eq = EVAL ``asl_features``

(* The instruction the specification fetches, as bits of memory. *)
Theorem fetch_bits:
    v2w [s.mem (s.pc + 3w) ' 7; s.mem (s.pc + 3w) ' 6; s.mem (s.pc + 3w) ' 5;
         s.mem (s.pc + 3w) ' 4; s.mem (s.pc + 3w) ' 3; s.mem (s.pc + 3w) ' 2;
         s.mem (s.pc + 3w) ' 1; s.mem (s.pc + 3w) ' 0; s.mem (s.pc + 2w) ' 7;
         s.mem (s.pc + 2w) ' 6; s.mem (s.pc + 2w) ' 5; s.mem (s.pc + 2w) ' 4;
         s.mem (s.pc + 2w) ' 3; s.mem (s.pc + 2w) ' 2; s.mem (s.pc + 2w) ' 1;
         s.mem (s.pc + 2w) ' 0; s.mem (s.pc + 1w) ' 7; s.mem (s.pc + 1w) ' 6;
         s.mem (s.pc + 1w) ' 5; s.mem (s.pc + 1w) ' 4; s.mem (s.pc + 1w) ' 3;
         s.mem (s.pc + 1w) ' 2; s.mem (s.pc + 1w) ' 1; s.mem (s.pc + 1w) ' 0;
         s.mem s.pc ' 7; s.mem s.pc ' 6; s.mem s.pc ' 5; s.mem s.pc ' 4;
         s.mem s.pc ' 3; s.mem s.pc ' 2; s.mem s.pc ' 1; s.mem s.pc ' 0] : word32 =
    fetch functional_storage s
Proof
  simp[arm64IsaTheory.fetch_def, numLib.SUC_RULE arm64IsaTheory.read_bytes_def,
       arm64IsaTheory.functional_storage_def] >>
  blastLib.BBLAST_TAC
QED

(* A doubleword the specification loads from memory, as arm64-hol reads it. *)
Theorem load_bits:
    v2w [s.mem (a + 7w) ' 7; s.mem (a + 7w) ' 6; s.mem (a + 7w) ' 5;
         s.mem (a + 7w) ' 4; s.mem (a + 7w) ' 3; s.mem (a + 7w) ' 2;
         s.mem (a + 7w) ' 1; s.mem (a + 7w) ' 0; s.mem (a + 6w) ' 7;
         s.mem (a + 6w) ' 6; s.mem (a + 6w) ' 5; s.mem (a + 6w) ' 4;
         s.mem (a + 6w) ' 3; s.mem (a + 6w) ' 2; s.mem (a + 6w) ' 1;
         s.mem (a + 6w) ' 0; s.mem (a + 5w) ' 7; s.mem (a + 5w) ' 6;
         s.mem (a + 5w) ' 5; s.mem (a + 5w) ' 4; s.mem (a + 5w) ' 3;
         s.mem (a + 5w) ' 2; s.mem (a + 5w) ' 1; s.mem (a + 5w) ' 0;
         s.mem (a + 4w) ' 7; s.mem (a + 4w) ' 6; s.mem (a + 4w) ' 5;
         s.mem (a + 4w) ' 4; s.mem (a + 4w) ' 3; s.mem (a + 4w) ' 2;
         s.mem (a + 4w) ' 1; s.mem (a + 4w) ' 0; s.mem (a + 3w) ' 7;
         s.mem (a + 3w) ' 6; s.mem (a + 3w) ' 5; s.mem (a + 3w) ' 4;
         s.mem (a + 3w) ' 3; s.mem (a + 3w) ' 2; s.mem (a + 3w) ' 1;
         s.mem (a + 3w) ' 0; s.mem (a + 2w) ' 7; s.mem (a + 2w) ' 6;
         s.mem (a + 2w) ' 5; s.mem (a + 2w) ' 4; s.mem (a + 2w) ' 3;
         s.mem (a + 2w) ' 2; s.mem (a + 2w) ' 1; s.mem (a + 2w) ' 0;
         s.mem (a + 1w) ' 7; s.mem (a + 1w) ' 6; s.mem (a + 1w) ' 5;
         s.mem (a + 1w) ' 4; s.mem (a + 1w) ' 3; s.mem (a + 1w) ' 2;
         s.mem (a + 1w) ' 1; s.mem (a + 1w) ' 0; s.mem a ' 7; s.mem a ' 6; s.mem a ' 5;
         s.mem a ' 4; s.mem a ' 3; s.mem a ' 2; s.mem a ' 1; s.mem a ' 0] : word64 =
    w2w (read_bytes functional_storage 8 s a)
Proof
  simp[numLib.SUC_RULE arm64IsaTheory.read_bytes_def,
       arm64IsaTheory.functional_storage_def] >>
  blastLib.BBLAST_TAC
QED

(* The specification's register named for a general-purpose register
   number, as arm64-hol's register. *)
Theorem state_rel_gpr:
  state_rel s asl ⇒ n ≠ 31w ⇒
  asl.regstate.bitvector_64_reg (STRING #"R" (toString (w2n n))) = s.regs n
Proof
  rw[state_rel_def, gpr_rel_def] >>
  first_x_assum (qspec_then `w2n n` mp_tac) >> simp[w2n_lt_31]
QED

(* The specification computes 32-bit results on the low halves of 64-bit
   values, as arm64-hol's w2w does. *)
Theorem low_word32:
  (31 >< 0) (w:word64) : word32 = w2w w ∧
  w2w (¬w : word64) : word32 = ¬w2w w ∧
  w2w (w2w (x:word12) : word64) : word32 = w2w x ∧
  w2w ((w2w (x:word12) : word64) << k) : word32 = w2w x << k
Proof
  rpt conj_tac >- blastLib.BBLAST_TAC >- blastLib.BBLAST_TAC >- blastLib.BBLAST_TAC >>
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [] >> eq_tac >> rw[]
QED

(* The flags the specification writes to PSTATE, as arm64-hol's. *)
Theorem flags_word_bits:
  (3 >< 3) (flags_word f) = v2w [FST f] : 1 word ∧
  (2 >< 2) (flags_word f) = v2w [FST (SND f)] : 1 word ∧
  (1 >< 1) (flags_word f) = v2w [FST (SND (SND f))] : 1 word ∧
  (0 >< 0) (flags_word f) = v2w [SND (SND (SND f))] : 1 word
Proof
  PairCases_on `f` >> Cases_on `f0` >> Cases_on `f1` >> Cases_on `f2` >> Cases_on `f3` >>
  EVAL_TAC
QED

Theorem extract_63_0_2048[local]:
  (63 >< 0) (x : 2048 word) : word64 = w2w (w2w x : word128)
Proof
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
QED

(* The low 64 bits of the specification's Z register for a SIMD&FP register
   number, as evaluation leaves them, as arm64-hol's. *)
Theorem state_rel_vreg64:
  state_rel s asl ⇒
  (63 >< 0) (EL (Num (ABS (31 − &w2n n)))
               (asl.regstate.vector_32_bitvector_2048_reg "_Z")) : word64 =
  w2w (s.vregs n)
Proof
  rw[state_rel_def, vreg_rel_def, armv9_typesTheory.Z_ref_def] >>
  `w2n n < 32` by (Cases_on `n` >> fs[]) >>
  first_x_assum (qspec_then `w2n n` mp_tac) >>
  simp[sail2_valuesTheory.access_list_dec_def, sail2_valuesTheory.access_list_inc_def,
       sail2_valuesTheory.nat_of_int_def, integerTheory.INT_SUB, extract_63_0_2048]
QED
