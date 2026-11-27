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
