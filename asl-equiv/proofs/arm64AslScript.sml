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

(* The Armv9.4-A features implemented: those whose instructions arm64-hol
   models. Every other feature is not implemented. *)
Definition asl_profile_def:
  asl_profile =
    [FEAT_FP; FEAT_AdvSIMD; FEAT_CRC32; FEAT_AES; FEAT_PMULL; FEAT_SHA1;
     FEAT_SHA256; FEAT_SHA512; FEAT_SHA3; FEAT_SM3; FEAT_SM4]
End

(* The specification's feature register, indexed from its end. *)
Definition asl_features_def:
  asl_features =
    REVERSE (GENLIST (λi. MEM (&i) (MAP num_of_Feature asl_profile)) 259)
End

(* The system configuration arm64-hol assumes: Non-secure state, MPAM
   disabled, the features above, AArch64 at EL0 on SP_EL0, no alignment
   checking of ordinary accesses, little-endian data, no top-byte ignore,
   not halted in debug state, and no statistical profiling sample in
   flight. *)
Definition arm64_asl_ok_def:
  arm64_asl_ok (asl:regstate sequential_state) ⇔
    (let p = PSTATE_ref.read_from asl.regstate in
     p.ProcState_EL = 0w ∧ p.ProcState_nRW = 0w ∧ p.ProcState_SP = 0w) ∧
    (let sctlr = (SCTLR_EL1_ref.read_from asl.regstate).SCTLR_EL1_Type_bits in
     ¬word_bit 1 sctlr ∧ ¬word_bit 24 sctlr) ∧
    (let tcr = (TCR_EL1_ref.read_from asl.regstate).TCR_EL1_Type_bits in
     ¬word_bit 37 tcr ∧ ¬word_bit 38 tcr) ∧
    (let status = (5 >< 0) (EDSCR_ref.read_from asl.regstate).EDSCR_Type_bits : 6 word in
     status ≠ 0b000001w ∧ status ≠ 0b000010w) ∧
    FeatureImpl_ref.read_from asl.regstate = asl_features ∧
    word_bit 0 (SCR_EL3_ref.read_from asl.regstate).SCR_EL3_Type_bits ∧
    ¬word_bit 63 (MPAM3_EL3_ref.read_from asl.regstate).MPAM3_EL3_Type_bits ∧
    ¬word_bit 63 (MPAM2_EL2_ref.read_from asl.regstate).MPAM2_EL2_Type_bits ∧
    ¬SPESampleInFlight_ref.read_from asl.regstate
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

(* The specification writes a register by updating a function from register
   names; this states such an update as an update of a function, which
   evaluation can reduce without going under a binder. *)
Theorem update_lambda:
  (λx. if x = a then b else f x) = (a =+ b) f
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> Cases_on `x = a` >> gvs[]
QED
