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

(* Every byte of the 64-bit address space is mapped. *)
Definition mem_rel_def:
  mem_rel (s:arm64_state) (m:memstate) ⇔
    ∀a. FLOOKUP m (w2n a) = SOME (MAP bitU_of_bool (w2v (s.mem a)))
End

Definition flag_rel_def:
  flag_rel b (w:1 word) ⇔ w = v2w [b]
End

Definition state_rel_def:
  state_rel (s:arm64_state) (asl:regstate sequential_state) ⇔
    gpr_rel s asl.regstate ∧
    vreg_rel s asl.regstate ∧
    mem_rel s asl.memstate ∧
    PC_ref.read_from asl.regstate = s.pc ∧
    SP_EL0_ref.read_from asl.regstate = s.sp ∧
    (let p = PSTATE_ref.read_from asl.regstate in
     flag_rel (FST s.nzcv) p.ProcState_N ∧
     flag_rel (FST (SND s.nzcv)) p.ProcState_Z ∧
     flag_rel (FST (SND (SND s.nzcv))) p.ProcState_C ∧
     flag_rel (SND (SND (SND s.nzcv))) p.ProcState_V)
End

(* The system configuration arm64-hol assumes: AArch64 at EL0, no alignment
   checking of ordinary accesses, little-endian data, no top-byte ignore,
   and not halted in debug state. *)
Definition arm64_asl_ok_def:
  arm64_asl_ok (asl:regstate sequential_state) ⇔
    (let p = PSTATE_ref.read_from asl.regstate in
     p.ProcState_EL = 0w ∧ p.ProcState_nRW = 0w) ∧
    (let sctlr = (SCTLR_EL1_ref.read_from asl.regstate).SCTLR_EL1_Type_bits in
     ¬word_bit 1 sctlr ∧ ¬word_bit 24 sctlr) ∧
    (let tcr = (TCR_EL1_ref.read_from asl.regstate).TCR_EL1_Type_bits in
     ¬word_bit 37 tcr ∧ ¬word_bit 38 tcr) ∧
    (let status = (5 >< 0) (EDSCR_ref.read_from asl.regstate).EDSCR_Type_bits : 6 word in
     status ≠ 0b000001w ∧ status ≠ 0b000010w)
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

(* The specification writes a register by updating a function from register
   names; this states such an update as an update of a function, which
   evaluation can reduce without going under a binder. *)
Theorem update_lambda:
  (λx. if x = a then b else f x) = (a =+ b) f
Proof
  rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> Cases_on `x = a` >> gvs[]
QED
