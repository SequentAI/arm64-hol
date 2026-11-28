(* The relation between arm64-hol states and states of Arm's Armv9.4-A
   specification (asl-equiv/model), and the specification's step. *)
Theory arm64Asl
Ancestors arm64Isa armv9_p32 ASCIInumbers
Libs wordsLib

(* General-purpose registers X0-X30 are the specification's R0-R30. *)
Definition gpr_rel_def:
  gpr_rel (s:arm64_state) (r:regstate) ⇔
    ∀n. n < 31 ⇒ r.bitvector_64_reg ("R" ++ num_to_dec_string n) = s.regs (n2w n)
End

(* SIMD&FP registers V0-V31 are the low 128 bits of the specification's
   (scalable) Z0-Z31. *)
Definition vreg_rel_def:
  vreg_rel (s:arm64_state) (r:regstate) ⇔
    LENGTH (Z_ref.read_from r) = 32 ∧
    ∀n. n < 32 ⇒ s.vregs (n2w n) = w2w (access_list_dec (Z_ref.read_from r) (&n))
End

(* The specification's memory holding arm64-hol's: every byte of the 64-bit
   address space is mapped, as a list of bits, most significant first. *)
Definition asl_mem_def:
  asl_mem (m:word64 -> word8) : memstate =
    FUN_FMAP (λa. MAP bitU_of_bool (w2v (m (n2w a)))) (count (dimword(:64)))
End

Definition flag_rel_def:
  flag_rel b (w:1 word) ⇔ w = v2w [b]
End

Definition state_rel_def:
  state_rel (s:arm64_state) (asl:regstate sequential_state) ⇔
    gpr_rel s asl.regstate ∧
    vreg_rel s asl.regstate ∧
    asl.memstate = asl_mem s.mem ∧
    PC_ref.read_from asl.regstate = s.pc ∧
    SP_EL0_ref.read_from asl.regstate = s.sp ∧
    (let p = PSTATE_ref.read_from asl.regstate in
     flag_rel (FST s.nzcv) p.ProcState_N ∧
     flag_rel (FST (SND s.nzcv)) p.ProcState_Z ∧
     flag_rel (FST (SND (SND s.nzcv))) p.ProcState_C ∧
     flag_rel (SND (SND (SND s.nzcv))) p.ProcState_V)
End

(* The Armv9.4-A features the pilot's simulation theorems assume. arm64-hol
   does not model the SHA and SM instructions yet. Every other feature is
   not implemented. *)
Definition asl_profile_def:
  asl_profile =
    [FEAT_AA64EL0; FEAT_AA64EL1; FEAT_AA64EL2; FEAT_AA64EL3; FEAT_FP; FEAT_AdvSIMD; FEAT_CRC32; FEAT_AES; FEAT_PMULL; FEAT_SHA1;
     FEAT_SHA256; FEAT_SHA512; FEAT_SHA3; FEAT_SM3; FEAT_SM4]
End

(* The features Armv9.4-A requires, which profile completeness assumes so
   that no A64 instruction arm64-hol lacks hides behind a feature turned
   off: those LLVM's AArch64 target implies or enables by default for
   v9.4-a (llvm/lib/Target/AArch64/AArch64Features.td), without SVE and
   SME, which the model leaves out, and RME and MEC, which concern address
   translation. *)
Definition asl_profile_v94_def:
  asl_profile_v94 = asl_profile ++
    [FEAT_LSE; FEAT_RDM; FEAT_PAN; FEAT_LOR; FEAT_VHE;
     FEAT_UAO; FEAT_PAN2; FEAT_RAS; FEAT_DPB;
     FEAT_LRCPC; FEAT_PAuth; FEAT_JSCVT; FEAT_FCMA; FEAT_CCIDX;
     FEAT_DotProd; FEAT_NV; FEAT_MPAM; FEAT_DIT; FEAT_TRF; FEAT_AMUv1;
     FEAT_SEL2; FEAT_TLBIOS; FEAT_TLBIRANGE; FEAT_FlagM; FEAT_LRCPC2; FEAT_LSE2;
     FEAT_FlagM2; FEAT_FRINTTS; FEAT_CSV2; FEAT_CSV3; FEAT_SB; FEAT_SPECRES;
     FEAT_DPB2; FEAT_BTI; FEAT_SSBS;
     FEAT_AMUv1p1; FEAT_BF16; FEAT_FGT; FEAT_ECV; FEAT_I8MM;
     FEAT_XS; FEAT_WFxT; FEAT_HBC; FEAT_MOPS; FEAT_NMI;
     FEAT_CLRBHB; FEAT_PRFMSLC; FEAT_SPECRES2; FEAT_CSSC; FEAT_RASv2; FEAT_CHK;
     FEAT_FP16]
End

(* The specification's feature register for a profile, indexed from its
   end. *)
Definition features_of_def:
  features_of prof =
    REVERSE (GENLIST (λi. MEM (&i) (MAP num_of_Feature prof)) 259)
End

Definition asl_features_def:
  asl_features = features_of asl_profile
End

(* The system configuration arm64-hol assumes: Non-secure state, MPAM
   disabled, AArch64 at EL0 on SP_EL0 with no illegal execution state, SIMD and floating-point instructions
   enabled at EL0, no alignment checking of ordinary accesses, little-endian
   data, no top-byte ignore, not in Debug state (EDSCR.STATUS is
   Non-debug), and no statistical profiling sample in flight. *)
Definition arm64_asl_config_def:
  arm64_asl_config (asl:regstate sequential_state) ⇔
    (let p = PSTATE_ref.read_from asl.regstate in
     p.ProcState_EL = 0w ∧ p.ProcState_nRW = 0w ∧ p.ProcState_SP = 0w ∧
     p.ProcState_IL = 0w) ∧
    (let sctlr = (SCTLR_EL1_ref.read_from asl.regstate).SCTLR_EL1_Type_bits in
     ¬word_bit 1 sctlr ∧ ¬word_bit 24 sctlr) ∧
    (let cpacr = (CPACR_EL1_ref.read_from asl.regstate).CPACR_EL1_Type_bits in
     word_bit 20 cpacr ∧ word_bit 21 cpacr) ∧
    ¬word_bit 10 (CPTR_EL2_ref.read_from asl.regstate).CPTR_EL2_Type_bits ∧
    ¬word_bit 10 (CPTR_EL3_ref.read_from asl.regstate).CPTR_EL3_Type_bits ∧
    (let tcr = (TCR_EL1_ref.read_from asl.regstate).TCR_EL1_Type_bits in
     ¬word_bit 37 tcr ∧ ¬word_bit 38 tcr) ∧
    (5 >< 0) (EDSCR_ref.read_from asl.regstate).EDSCR_Type_bits = (0b000010w :6 word) ∧
    word_bit 0 (SCR_EL3_ref.read_from asl.regstate).SCR_EL3_Type_bits ∧
    ¬word_bit 63 (MPAM3_EL3_ref.read_from asl.regstate).MPAM3_EL3_Type_bits ∧
    ¬word_bit 63 (MPAM2_EL2_ref.read_from asl.regstate).MPAM2_EL2_Type_bits ∧
    ¬SPESampleInFlight_ref.read_from asl.regstate
End

(* The configuration with the pilot's features. *)
Definition arm64_asl_ok_def:
  arm64_asl_ok asl ⇔
    arm64_asl_config asl ∧ FeatureImpl_ref.read_from asl.regstate = asl_features
End

(* The configuration with the features Armv9.4-A requires. *)
Definition arm64_asl_full_def:
  arm64_asl_full asl ⇔
    arm64_asl_config asl ∧
    FeatureImpl_ref.read_from asl.regstate = features_of asl_profile_v94
End

(* One step of the specification: fetch the instruction at PC, execute it,
   and advance PC unless it branched. *)
Definition arm64_asl_next_def:
  arm64_asl_next : (regstate, unit, exception) monadS =
    seqS (write_regS BranchTaken_ref F)
    (seqS (write_regS SEE_ref (-1))
    (bindS (PC_read ()) (λpc.
     bindS (CreateAccDescIFetch ()) (λacc.
     bindS (AArch64_MemSingle_read pc 4 acc T) (λinstr : word32.
     seqS (ExecuteA64 instr)
     (bindS (read_regS BranchTaken_ref) (λtaken.
      if taken then returnS () else write_regS PC_ref (pc + 4w))))))))
End

(* The specification simulates an instruction when, from any state related
   to one arm64-hol executes it in, the specification's step has exactly one
   outcome, which is related to arm64-hol's next state. *)
Definition asl_sim_def:
  asl_sim i ⇔
    ∀s s' asl.
      state_rel s asl ∧ arm64_asl_ok asl ∧ s.pc && 3w = 0w ∧
      encode i = SOME (fetch functional_storage s) ∧
      execute_with functional_storage i s = Next s' ⇒
      ∃asl'. arm64_asl_next asl = {(Value (), asl')} ∧
             state_rel s' asl' ∧ arm64_asl_ok asl'
End

(* Profile completeness, the converse of simulation, for the features
   Armv9.4-A requires: whenever the specification steps successfully from a
   state related to one arm64-hol can fetch from, arm64-hol decodes the
   instruction, and its step, unless it faults (on a permission, say, which
   the specification does not model), reaches a related state. Stated here;
   not yet proved. *)
Definition asl_complete_def:
  asl_complete ⇔
    ∀s asl asl'.
      state_rel s asl ∧ arm64_asl_full asl ∧ s.pc && 3w = 0w ∧
      access_ok functional_storage Execute 4 s s.pc ∧
      (Value (), asl') ∈ arm64_asl_next asl ⇒
      IS_SOME (decode armv9_4 (fetch functional_storage s)) ∧
      ∀s'. step armv9_4 s = Next s' ⇒ state_rel s' asl'
End

(* The specification writes a register by updating a function from register
   names; this states such an update as an update of a function, which
   evaluation can reduce without going under a binder. *)
Theorem update_lambda:
  (λx. if x = a then b else f x) = (a =+ b) f
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> Cases_on `x = a` >> gvs[]
QED
