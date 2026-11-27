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
