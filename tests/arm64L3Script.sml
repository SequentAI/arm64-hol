Theory arm64L3
Ancestors arm64Native arm8_step
Libs wordsLib utilsLib Import intReduce

Definition l3_state_def:
  l3_state (s:arm64_state) =
    (ARB : arm8_state) with <|
      PC := s.pc;
      REG := s.regs;
      MEM := s.mem;
      SP_EL0 := s.sp;
      PSTATE := <| EL := 0w; SPS := F; N := FST s.nzcv;
                   Z := FST (SND s.nzcv); C := FST (SND (SND s.nzcv));
                   V := SND (SND (SND s.nzcv)) |>;
      SCTLR_EL1 := <| A := F; E0E := F; EE := F; SA := F; SA0 := F;
                       sctlrtype'rst := 0w |>;
      TCR_EL1 := <| TBI0 := F; TBI1 := F; tcr_el1'rst := 0w |>;
      branch_hint := NONE;
      exception := NoException |>
End

Definition l3_agrees_def:
  l3_agrees ((w,instr,before,(pc,sp,nzcv_bits,link,regs,vectors,data)) : native_case) ⇔
    case NextStateARM8 (l3_state (abstract_state (test_state w before))) of
      NONE => F
    | SOME s =>
      s.PC = pc ∧ s.SP_EL0 = sp ∧ s.REG 30w = link ∧
      bits_of_nzcv (s.PSTATE.N,s.PSTATE.Z,s.PSTATE.C,s.PSTATE.V) = nzcv_bits ∧
      GENLIST (λi. s.REG (n2w i : word5)) 4 = regs ∧
      GENLIST (λi. s.MEM (n2w (4096 + i) : word64)) 64 = data
End

(* At the pinned L3 revision, v8-iset.spec passes opcode bit 10 as
   count_clz. CLZ has that bit clear and is executed as CLS. These zero
   inputs distinguish the two instructions at both register widths. *)
Definition l3_clz_is_cls_def:
  l3_clz_is_cls ((w,instr,before,after) : native_case) ⇔
    case instr of
      BitOp sf Clz d n => d = 0w ∧ n = 1w ∧
        EL 1 (FST (SND (SND (SND (SND before))))) = 0w ∧
        EL 0 (FST (SND (SND (SND (SND after))))) = (if sf then (64w:word64) else (32w:word64)) ∧
        (case NextStateARM8 (l3_state (abstract_state (test_state w before))) of
           NONE => F
         | SOME s => s.PC = 260w ∧ s.REG 0w = if sf then 63w else 31w)
    | _ => F
End

(* Register the recursive equation before importing rules that call it. *)
val {Thy, T = types, C = constants, N} = Import.gen_inventory {thyname = "arm8"};
fun is_crc_primitive name = name = "Poly32Mod2_loop_def_primitive";
val l3_compset = computeLib.copy (computeLib.the_compset ())
  |> (fn cs => computeLib.scrub_const cs ``Poly32Mod2_loop``)
  |> utilsLib.add_theory ([arm8Theory.Poly32Mod2_loop_def],
       {Thy = Thy, T = types, C = List.filter (not o is_crc_primitive) constants, N = N})
  |> computeLib.add_thms
    (map snd (List.filter (not o is_crc_primitive o fst) (DB.definitions "arm8")) @
     [arm64IsaCvTheory.lookup_word_def, arm64IsaCvTheory.lookup_default_def]);

val l3_eval = REWRITE_CONV [l3_agrees_def, l3_clz_is_cls_def, arm8_stepTheory.NextStateARM8_def, arm8Theory.Next_def]
  THENC computeLib.CBV_CONV l3_compset;

fun compare predicate name_prefix false_message i =
  let
    val name = "native_case_" ^ Int.toString i
    val def = DB.fetch "arm64NativeCases" (name ^ "_def")
    val statement = mk_comb (predicate, rhs (concl def))
    val observed =
      (l3_eval statement
       handle HOL_ERR _ =>
         raise Fail (name ^ ": incomplete l3_eval compset evaluation"))
    val value = rhs (concl observed)
    val result =
      if aconv value T then EQT_ELIM observed
      else if aconv value F then
        raise Fail (name ^ ": " ^ false_message)
      else
        raise Fail (name ^ ": incomplete l3_eval compset evaluation")
  in
    ignore (save_thm (name_prefix ^ name, PURE_REWRITE_RULE [GSYM def] result))
  end;

fun cases def = map numSyntax.int_of_term (fst (listSyntax.dest_list (rhs (concl def))));

val () = List.app (compare ``l3_clz_is_cls`` "l3_clz_is_cls_"
  "L3 discrepancy witness no longer holds")
  (cases arm64NativeCasesTheory.native_l3_clz_zero_def);
(* CRCExt is independent of the reflected recurrence in arm64Crypto. *)
val () = List.app (compare ``l3_agrees`` "l3_crc_agrees_"
  "L3 hardware value mismatch") (cases arm64NativeCasesTheory.native_crc_cases_def);
val () = List.app (compare ``l3_agrees`` "l3_agrees_"
  "L3 hardware value mismatch") (cases arm64NativeCasesTheory.native_l3_cases_def);
