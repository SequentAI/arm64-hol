(* The simulation of arm64-hol's step by the Armv9.4-A specification's. *)
Theory aslSim
Ancestors aslLemmas arm64Isa
Libs aslEvalLib blastLib

(* Fetching from PC reads the instruction arm64-hol fetches. *)
Theorem asl_fetch:
  arm64_asl_ok asl ∧ s.pc && 3w = 0w ⇒
  bindS (CreateAccDescIFetch ()) (λacc. AArch64_MemSingle_read s.pc 4 acc T)
    (asl with memstate := asl_mem s.mem) =
  {(Value (fetch functional_storage s), asl with memstate := asl_mem s.mem)}
Proof
  strip_tac >> aslEvalLib.EXEC_TAC >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[fetch_def, numLib.SUC_RULE read_bytes_def, functional_storage_def] >>
  BBLAST_TAC
QED
