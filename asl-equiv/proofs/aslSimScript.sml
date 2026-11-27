(* The simulation of arm64-hol's step by the Armv9.4-A specification's. *)
Theory aslSim
Ancestors aslLemmas arm64Isa
Libs aslEvalLib

(* Fetching from PC reads the instruction arm64-hol fetches. *)
Theorem asl_fetch:
  arm64_asl_ok asl ∧ s.pc && 3w = 0w ⇒
  bindS (CreateAccDescIFetch ()) (λacc. AArch64_MemSingle_read s.pc 4 acc T)
    (asl with memstate := asl_mem s.mem) =
  {(Value (fetch functional_storage s), asl with memstate := asl_mem s.mem)}
Proof
  strip_tac >> aslEvalLib.EXEC_TAC >> simp[]
QED

(* The specification's step up to the execution of the instruction fetched,
   which is arm64-hol's. *)
Theorem asl_next_fetch:
  state_rel s asl ∧ arm64_asl_ok asl ∧ s.pc && 3w = 0w ⇒
  arm64_asl_next asl =
  seqS (ExecuteA64 (fetch functional_storage s))
    (bindS (read_regS BranchTaken_ref)
       (λtaken. if taken then returnS () else write_regS PC_ref (s.pc + 4w)))
    (asl with regstate :=
       asl.regstate with <|
         bool_reg := asl.regstate.bool_reg⦇"__BranchTaken" ↦ F⦈;
         int_reg := asl.regstate.int_reg⦇"SEE" ↦ -1⦈|>)
Proof
  strip_tac >> aslEvalLib.EXEC_TAC >> aslEvalLib.EXEC_RHS_TAC
QED

(* After the evaluation of an instruction: the definitions relating the two
   states, and arm64-hol's for the instruction's effect. *)
val rel_simps = [
  state_rel_def, arm64_asl_ok_def, gpr_rel_def, vreg_rel_def, flag_rel_def,
  armv9_typesTheory.PC_ref_def, armv9_typesTheory.SP_EL0_ref_def,
  armv9_typesTheory.PSTATE_ref_def, armv9_typesTheory.Z_ref_def,
  armv9_typesTheory.FeatureImpl_ref_def, armv9_typesTheory.SCTLR_EL1_ref_def,
  armv9_typesTheory.TCR_EL1_ref_def, armv9_typesTheory.EDSCR_ref_def,
  armv9_typesTheory.SCR_EL3_ref_def, armv9_typesTheory.MPAM3_EL3_ref_def,
  armv9_typesTheory.MPAM2_EL2_ref_def, armv9_typesTheory.SPESampleInFlight_ref_def,
  arm64IsaTheory.set_gpr_def, arm64IsaTheory.set_base_def,
  arm64IsaTheory.base_reg_def, arm64IsaTheory.advance_def,
  arm64IsaTheory.functional_storage_def, combinTheory.APPLY_UPDATE_THM,
  word5_eq_n2w, wordsTheory.EXTRACT_ALL_BITS, low_word32, flags_word_bits]

Theorem asl_sim_add_imm:
  asl_sim (AddImm sf sub flags shift d n imm)
Proof
  rewrite_tac[asl_sim_def] >> rpt strip_tac >>
  drule_all asl_next_fetch >> disch_then SUBST1_TAC >>
  imp_res_tac state_rel_gpr >>
  Cases_on `sf` >> Cases_on `sub` >> Cases_on `flags` >> Cases_on `shift` >>
  Cases_on `d = 31w` >> Cases_on `n = 31w` >>~-
  ([`ExecuteA64 _`],
   gvs[arm64IsaTheory.encode_def, arm64IsaTheory.flag_field_def,
       arm64IsaTheory.reg_fields_def, arm64IsaTheory.insert_field_def,
       arm64IsaTheory.execute_with_def] >>
   qpat_x_assum `_ = fetch _ _` (assume_tac o SYM) >>
   aslEvalLib.EXEC_AT_TAC ``seqS (ExecuteA64 _) _ _`` [] >>
   CONV_TAC aslEvalLib.FIELDS_CONV >>
   irule_at (Pos hd) EQ_REFL >>
   gvs (arm64IsaTheory.write_arith_def :: arm64IsaTheory.arm_add_with_carry_def :: rel_simps))
QED
