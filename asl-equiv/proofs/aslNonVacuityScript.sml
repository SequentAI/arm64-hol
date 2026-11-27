(* The hypotheses of the simulation theorems can hold: every arm64-hol state
   has a related specification state in the configuration arm64_asl_ok
   describes. *)
Theory aslNonVacuity
Ancestors arm64Asl
Libs wordsLib

(* The 64-bit registers of a specification state related to s: arm64-hol's
   general-purpose registers, PC and SP, and the configuration
   arm64_asl_ok requires; every other one is zero. *)
Definition witness_x64_def:
  witness_x64 (s:arm64_state) r : word64 =
    if r = "_PC" then s.pc
    else if r = "SP_EL0" then s.sp
    else if r = "CPACR_EL1" then 0x300000w
    else if r = "SCR_EL3" then 1w
    else if HD r = #"R" then s.regs (n2w (toNum (TL r)))
    else 0w
End

Definition witness_pstate_def:
  witness_pstate (s:arm64_state) =
    (ARB:ProcState) with
      <| ProcState_EL := 0w; ProcState_nRW := 0w; ProcState_SP := 0w;
         ProcState_N := v2w [FST s.nzcv];
         ProcState_Z := v2w [FST (SND s.nzcv)];
         ProcState_C := v2w [FST (SND (SND s.nzcv))];
         ProcState_V := v2w [SND (SND (SND s.nzcv))] |>
End

(* The SIMD&FP registers, last first as the specification lists them. *)
Definition witness_z_def:
  witness_z (s:arm64_state) : 2048 word list =
    REVERSE (GENLIST (λn. w2w (s.vregs (n2w n))) 32)
End

(* A specification state related to s; registers not named are
   unspecified. *)
Definition asl_witness_def:
  asl_witness (s:arm64_state) : regstate sequential_state =
    <| regstate :=
         (ARB:regstate) with
           <| bitvector_64_reg := witness_x64 s;
              bitvector_32_reg := K 0w;
              bool_reg := K F;
              vector_259_bool_reg := K asl_features;
              vector_32_bitvector_2048_reg := K (witness_z s);
              ProcState_reg := K (witness_pstate s) |>;
       memstate := asl_mem s.mem;
       tagstate := ARB |>
End

Theorem asl_witness_fields[local]:
  (asl_witness s).memstate = asl_mem s.mem ∧
  (asl_witness s).regstate.bitvector_64_reg = witness_x64 s ∧
  (asl_witness s).regstate.bitvector_32_reg = K 0w ∧
  (asl_witness s).regstate.bool_reg = K F ∧
  (asl_witness s).regstate.vector_259_bool_reg = K asl_features ∧
  (asl_witness s).regstate.vector_32_bitvector_2048_reg = K (witness_z s) ∧
  (asl_witness s).regstate.ProcState_reg = K (witness_pstate s)
Proof
  simp[asl_witness_def]
QED

Theorem witness_pstate_fields[local]:
  (witness_pstate s).ProcState_EL = 0w ∧ (witness_pstate s).ProcState_nRW = 0w ∧
  (witness_pstate s).ProcState_SP = 0w ∧
  (witness_pstate s).ProcState_N = v2w [FST s.nzcv] ∧
  (witness_pstate s).ProcState_Z = v2w [FST (SND s.nzcv)] ∧
  (witness_pstate s).ProcState_C = v2w [FST (SND (SND s.nzcv))] ∧
  (witness_pstate s).ProcState_V = v2w [SND (SND (SND s.nzcv))]
Proof
  simp[witness_pstate_def]
QED

Theorem witness_x64_gpr[local]:
  n < 31 ⇒ witness_x64 s ("R" ++ toString n) = s.regs (n2w n)
Proof
  simp[witness_x64_def]
QED

Theorem access_list_dec_genlist[local]:
  n < m ⇒ access_list_dec (REVERSE (GENLIST f m)) (&n) = f n
Proof
  rw[sail2_valuesTheory.access_list_dec_def, sail2_valuesTheory.access_list_inc_def,
     sail2_valuesTheory.nat_of_int_def] >- (`F` suffices_by simp[] >> intLib.ARITH_TAC) >>
  `&m − 1 − &n = &(m − 1 − n) : int` by intLib.ARITH_TAC >>
  simp[listTheory.EL_REVERSE, arithmeticTheory.PRE_SUC_EQ, GSYM arithmeticTheory.ADD1]
QED

Theorem witness_z_rel[local]:
  LENGTH (witness_z s) = 32 ∧
  (n < 32 ⇒ s.vregs (n2w n) = w2w (access_list_dec (witness_z s) (&n)))
Proof
  rewrite_tac[witness_z_def, listTheory.LENGTH_REVERSE, listTheory.LENGTH_GENLIST] >>
  strip_tac >> simp[access_list_dec_genlist, wordsTheory.w2w_w2w, wordsTheory.WORD_ALL_BITS]
QED

Theorem asl_witness_ok:
  state_rel s (asl_witness s) ∧ arm64_asl_ok (asl_witness s)
Proof
  rewrite_tac[state_rel_def, arm64_asl_ok_def, gpr_rel_def, vreg_rel_def, flag_rel_def,
       armv9_typesTheory.PC_ref_def, armv9_typesTheory.SP_EL0_ref_def,
       armv9_typesTheory.PSTATE_ref_def, armv9_typesTheory.Z_ref_def,
       armv9_typesTheory.FeatureImpl_ref_def, armv9_typesTheory.SCTLR_EL1_ref_def,
       armv9_typesTheory.CPACR_EL1_ref_def, armv9_typesTheory.CPTR_EL2_ref_def,
       armv9_typesTheory.CPTR_EL3_ref_def, armv9_typesTheory.TCR_EL1_ref_def,
       armv9_typesTheory.EDSCR_ref_def, armv9_typesTheory.SCR_EL3_ref_def,
       armv9_typesTheory.MPAM3_EL3_ref_def, armv9_typesTheory.MPAM2_EL2_ref_def,
       armv9_typesTheory.SPESampleInFlight_ref_def] >>
  simp_tac (srw_ss()) [] >> rewrite_tac[asl_witness_fields, combinTheory.K_THM] >>
  simp[witness_pstate_fields, witness_x64_gpr, witness_z_rel] >>
  simp[witness_x64_def]
QED

Theorem state_rel_exists:
  ∀s. ∃asl. state_rel s asl ∧ arm64_asl_ok asl
Proof
  metis_tac[asl_witness_ok]
QED
