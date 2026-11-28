(* Every instruction arm64-hol decodes steps without a fault from some state
   that fetches it, so the hypotheses of the simulation theorems hold for
   each of them. *)
Theory aslDecodeNonVacuity
Ancestors arm64Isa
Libs wordsLib blastLib

(* Code is the quarter of the address space from 2^62; data is the rest. *)
Definition witness_perms_def:
  witness_perms (a:word64) =
    if (63 >< 62) a = (1w:word2) then <| read := T; write := F; execute := T |>
    else <| read := T; write := T; execute := F |>
End

(* A state that fetches w from 2^62, with every register zero. *)
Definition decode_witness_def:
  decode_witness (w:word32) : arm64_state =
    <| regs := K 0w; sp := 0w; pc := 0x4000000000000000w; nzcv := (F,F,F,F);
       vregs := K 0w; perms := witness_perms;
       mem := λa. if a = 0x4000000000000000w then (7 >< 0) w
                  else if a = 0x4000000000000001w then (15 >< 8) w
                  else if a = 0x4000000000000002w then (23 >< 16) w
                  else if a = 0x4000000000000003w then (31 >< 24) w
                  else 0w |>
End

(* Addresses within 2^20 of zero, either side. *)
Definition near0_def:
  near0 (a:word64) ⇔ a + 0x100000w <₊ 0x200000w
End

Theorem decode_witness_fetch[local]:
  fetch functional_storage (decode_witness w) = w
Proof
  EVAL_TAC >> BBLAST_TAC
QED

Theorem decode_witness_step[local]:
  (decode_witness w).pc && 3w = 0w ∧
  access_ok functional_storage Execute 4 (decode_witness w) (decode_witness w).pc
Proof
  EVAL_TAC
QED

Theorem witness_regs[local]:
  gpr functional_storage (decode_witness w) r = 0w ∧
  base_reg functional_storage (decode_witness w) r = 0w
Proof
  rw[gpr_def, base_reg_def, decode_witness_def, functional_storage_def]
QED

Theorem access_ok_read[local]:
  ∀n a. access_ok functional_storage Read n (decode_witness w) a
Proof
  Induct >>
  simp[access_ok_def, allowed_def, functional_storage_def, decode_witness_def,
       witness_perms_def] >>
  rw[]
QED

Theorem access_ok_write_range[local]:
  ∀n a. (∀k. k < n ⇒ (63 >< 62) (a + n2w k) ≠ (1w:word2)) ⇒
        access_ok functional_storage Write n (decode_witness w) a
Proof
  Induct >> simp[access_ok_def] >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >>
      simp[allowed_def, functional_storage_def, decode_witness_def,
           witness_perms_def]) >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  simp[wordsTheory.n2w_SUC, wordsTheory.WORD_ADD_ASSOC] >>
  metis_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM]
QED

Theorem near0_add[local]:
  near0 a ⇒ (63 >< 62) (a + w2w (y:10 word)) ≠ (1w:word2)
Proof
  rewrite_tac[near0_def] >> BBLAST_TAC
QED

Theorem access_ok_write[local]:
  near0 a ∧ n ≤ 1024 ⇒ access_ok functional_storage Write n (decode_witness w) a
Proof
  rw[] >> irule access_ok_write_range >> rw[] >>
  drule near0_add >> disch_then (qspec_then `n2w k` mp_tac) >>
  simp[wordsTheory.w2w_n2w, bitTheory.BITS_ZERO3]
QED

Theorem near0_indexed[local]:
  near0 off ⇒ near0 (indexed_addr mode 0w off)
Proof
  rw[indexed_addr_def] >> EVAL_TAC
QED

Theorem execute_mem_witness[local]:
  near0 off ⇒
  ∃s'. execute_mem functional_storage vec opc size mode t n off (decode_witness w) =
       Next s'
Proof
  strip_tac >> drule near0_indexed >> disch_then (qspec_then `mode` assume_tac) >>
  `2 ** transfer_scale vec opc size ≤ 1024`
    by (Cases_on_word_value `size` >> rw[transfer_scale_def]) >>
  rw[execute_mem_def, witness_regs, check_sp_def, access_ok_read] >>
  gvs[access_ok_write]
QED


Theorem near0_scaled[local]:
  k ≤ 7 ⇒ near0 (w2w (u:word12) << k)
Proof
  strip_tac >>
  `k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7` by decide_tac >>
  gvs[near0_def] >- BBLAST_TAC >- BBLAST_TAC >- BBLAST_TAC >- BBLAST_TAC
  >- BBLAST_TAC >- BBLAST_TAC >- BBLAST_TAC >> BBLAST_TAC
QED

Theorem near0_unscaled[local]:
  near0 (sw2sw (i:word9))
Proof
  rw[near0_def] >> BBLAST_TAC
QED

Theorem near0_pair[local]:
  k ≤ 5 ⇒ near0 (sw2sw (i:word7) << k)
Proof
  strip_tac >>
  `k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5` by decide_tac >>
  gvs[near0_def] >- BBLAST_TAC >- BBLAST_TAC >- BBLAST_TAC >- BBLAST_TAC
  >- BBLAST_TAC >> BBLAST_TAC
QED

Theorem execute_pair_witness[local]:
  ∃s'. execute_pair functional_storage vec opc load mode t u n imm (decode_witness w) =
       Next s'
Proof
  Cases_on_word_value `opc` >> Cases_on `vec` >>
  rw[execute_pair_def, witness_regs, check_sp_def, access_ok_read] >>
  gvs[access_ok_write, near0_indexed, near0_pair]
QED

Theorem transfer_scale_le[local]:
  transfer_scale vec opc size ≤ 7
Proof
  Cases_on_word_value `size` >> rw[transfer_scale_def]
QED

Theorem extend_reg_0[local]:
  extend_reg ext 0w = 0w
Proof
  rw[extend_reg_def] >> EVAL_TAC
QED

Theorem near0_0[local]:
  near0 0w
Proof
  EVAL_TAC
QED

Theorem access_ok_write_0[local]:
  n ≤ 1024 ⇒ access_ok functional_storage Write n (decode_witness w) 0w
Proof
  strip_tac >> irule access_ok_write >> simp[near0_0]
QED

Theorem multi_total_le[local]:
  x ≤ 4 ⇒
  x * ((if q then 16 else 8) DIV 2 ** w2n (size:word2)) * 2 ** w2n size ≤ 1024
Proof
  strip_tac >> Cases_on `q` >> Cases_on_word_value `size` >> simp[]
QED

Theorem execute_multi_witness[local]:
  ∃s'. execute_multi functional_storage q load post m opc size t n
         (decode_witness w) = Next s'
Proof
  `FST (multi_layout opc) * SND (multi_layout opc) ≤ 4`
    by rw[multi_layout_def] >>
  Cases_on `multi_layout opc` >> gvs[] >>
  rw[execute_multi_def, witness_regs, check_sp_def, access_ok_read] >>
  gvs[access_ok_write_0, multi_total_le]
QED

Theorem lane_total_le[local]:
  (2 * (w2n (opc:word3) MOD 2) + (if r then 2 else 1)) *
  FST (lane_layout q opc sb size) ≤ 1024
Proof
  `FST (lane_layout q opc sb size) ≤ 8`
    by (rw[lane_layout_def] >> Cases_on_word_value `size` >> simp[]) >>
  `2 * (w2n opc MOD 2) + (if r then 2 else 1) ≤ 4`
    by (`w2n opc MOD 2 < 2` by simp[] >> rw[]) >>
  `(2 * (w2n opc MOD 2) + (if r then 2 else 1)) *
   FST (lane_layout q opc sb size) ≤ 4 * 8` suffices_by simp[] >>
  irule arithmeticTheory.LESS_MONO_MULT2 >> simp[]
QED

Theorem execute_lane_witness[local]:
  ∃s'. execute_lane functional_storage q load post m r opc sb size t n
         (decode_witness w) = Next s'
Proof
  assume_tac lane_total_le >>
  Cases_on `lane_layout q opc sb size` >> gvs[] >>
  rw[execute_lane_def, witness_regs, check_sp_def, access_ok_read] >>
  gvs[access_ok_write_0]
QED

Theorem execute_witness[local]:
  ∃s'. execute_with functional_storage i (decode_witness w) = Next s'
Proof
  Cases_on `i` >>
  rw[execute_with_def, access_ok_read, execute_pair_witness,
     execute_multi_witness, execute_lane_witness, witness_regs,
     extend_reg_0, wordsTheory.ZERO_SHIFT] >>~-
  ([`execute_mem`],
   BasicProvers.every_case_tac >> irule execute_mem_witness >>
   simp[near0_0, near0_scaled, near0_unscaled, transfer_scale_le])
QED

Theorem decode_nonvacuity:
  ∀feat w. IS_SOME (decode feat w) ⇒
           ∃s s'. fetch functional_storage s = w ∧ step feat s = Next s'
Proof
  rw[optionTheory.IS_SOME_EXISTS] >>
  qexists_tac `decode_witness w` >>
  simp[step_def, step_with_def, decode_witness_fetch, decode_witness_step,
       execute_witness]
QED
