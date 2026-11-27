(* Symbolic evaluation of the Armv9.4-A specification (asl-equiv/model).

   CEVAL evaluates with every definition of the Sail and Lem libraries and of
   the model's types theory, plus the instruction-set entry points, so an
   instruction's decode runs down to the call of its execute function. Adapted
   from HOL's examples/l3-machine-code/arm8/asl-equiv/l3_equivalenceLib. *)
structure aslEvalLib =
struct

open HolKernel boolLib bossLib
open armv9_p32Theory arm64AslTheory aslLemmasTheory

local
  val tyvars = [alpha, beta, gamma, delta, etyvar, ftyvar]
  fun add_type (ty, cmp) =
    computeLib.add_datatype_info cmp (Option.valOf (TypeBase.fetch ty))
    handle _ => cmp
  fun add_types thy cmp =
    List.foldl add_type cmp
      (map (fn (name, arity) =>
              mk_thy_type {Args = List.take (tyvars, arity), Thy = thy, Tyop = name})
           (types thy))
  fun unpack (DefnBase.STDEQNS t) = t
    | unpack (DefnBase.OTHER t) = t
  (* Equations used in place of definitions: word-level arithmetic
     (aslLemmas), and recursion equations in place of the WFREC forms. A
     compset rule refers to the entries of the constants on its right-hand
     side as they are when it is added, so the definitions these replace are
     never added, rather than removed afterwards. *)
  val overrides = [
    aslLemmasTheory.AddWithCarry_add_with_carry,
    sail2_valuesAuxiliaryTheory.bools_of_nat_aux_rw]
  fun head th =
    th |> CONJUNCTS |> hd |> SPEC_ALL |> concl |> lhs |> strip_comb |> fst
  val overridden = map head overrides
  fun overrides_def th =
    List.exists (same_const (head th)) overridden handle HOL_ERR _ => false
  fun add_def (th, cmp) =
    if overrides_def th then cmp
    else computeLib.add_thms [th] cmp handle HOL_ERR _ => cmp
  (* Register writes are added as function updates (update_lambda), which
     evaluation reduces without going under a binder. *)
  fun add_defs thy cmp =
    List.foldl add_def cmp
      (map (PURE_REWRITE_RULE [arm64AslTheory.update_lambda] o unpack o #thm)
           (DefnBase.thy_userdefs {thyname = thy}))
  val thys = [
    "lem_machine_word", "lem", "sail2_instr_kinds", "sail2_operators_bitlists",
    "sail2_operators_mwords", "sail2_operators", "sail2_stateAuxiliary",
    "sail2_state_monad", "sail2_state", "sail2_string",
    "sail2_valuesAuxiliary", "sail2_values", "sail2_concurrency_interface",
    "sail2_monadic_combinators", "sail2_undefined_concurrency_interface",
    "prelude", "undefined_override", "armv9_types"]
  fun def_of name =
    case Term.decls name of
      c :: _ => DB.fetch (#Thy (dest_thy_const c)) (name ^ "_def")
    | [] => raise mk_HOL_ERR "aslEvalLib" "def_of" ("no constant " ^ name)
  (* The instruction-set entry point and decode, down to the call of each
     instruction's own decode function. *)
  val entry_defs = map def_of [
    "ExecuteA64", "DecodeA64", "DecodeA64_BranchExcSys",
    "DecodeA64_DataProcFPSIMD", "DecodeA64_DataProcImm", "DecodeA64_DataProcReg",
    "DecodeA64_LoadStore", "DecodeA64_Reserved", "DecodeA64_SME",
    "DecodeA64_SVE", "DecodeA64_Unallocated1", "DecodeA64_Unallocated2"]
in
  val cmp =
    computeLib.copy reduceLib.num_compset
    |> pairLib.add_pair_compset
    |> optionLib.OPTION_rws
    |> combinLib.add_combin_compset
    |> wordsLib.add_words_compset true
    |> intReduce.add_int_compset
    |> computeLib.add_conv
         (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)
    |> computeLib.add_conv
         (``$= : α word -> α word -> bool``, 2, QCHANGED_CONV blastLib.BBLAST_CONV)
    |> bitstringLib.add_bitstring_compset
    |> (fn cmp => List.foldl (fn (thy, c) => add_types thy c) cmp thys)
    |> (fn cmp => List.foldl (fn (thy, c) => add_defs thy c) cmp thys)
    |> computeLib.add_thms overrides
    |> computeLib.add_thms entry_defs
    |> computeLib.add_thms [pred_setTheory.IMAGE_INSERT, pred_setTheory.IMAGE_EMPTY,
         pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY,
         pred_setTheory.UNION_EMPTY, pred_setTheory.INSERT_UNION_EQ]
  val CEVAL = computeLib.CBV_CONV cmp
  (* Every definition of the specification, for evaluating execution on a
     given state. Weak reduction (none under binders) keeps the branches
     not taken unevaluated. *)
  val model_thys =
    ["prelude", "undefined_override", "armv9_types"] @
    List.tabulate (32, fn i => "armv9_p" ^ Int.toString (i + 1))
  val exec_cmp =
    List.foldl (fn (thy, c) => add_defs thy c) (computeLib.copy cmp)
      (List.filter (fn t => t <> "armv9_types") model_thys)
    |> (fn c => computeLib.set_skip c boolSyntax.conditional (SOME 1))
  val EXEC = computeLib.WEAK_CBV_CONV exec_cmp

  (* Evaluates a definition about the specification's state with every
     definition of the specification, splitting it into its conjuncts. *)
  fun facts_of defs th =
    th |> CONV_RULE (computeLib.CBV_CONV (computeLib.add_thms defs exec_cmp))
       |> CONJUNCTS

  (* Proves a guard true or false from facts about bits of registers. *)
  fun decide facts g =
    let
      val hyp = list_mk_conj (map concl facts)
      val facts_th = LIST_CONJ facts
      fun prove t = SOME (MP (blastLib.BBLAST_PROVE (mk_imp (hyp, t))) facts_th)
                    handle HOL_ERR _ => NONE | UNCHANGED => NONE
    in
      case prove g of
        SOME th => SOME (EQT_INTRO th)
      | NONE => Option.map EQF_INTRO (prove (mk_neg g))
    end

  (* Evaluates an execution of the specification on a state, deciding each
     conditional it gets stuck on from the facts. *)
  val trace = ref false
  fun EXEC_WITH facts tm =
    let
      val globals = free_varsl (tm :: map concl facts)
      fun closed g = List.all (fn v => tmem v globals) (free_vars g)
      (* The guards evaluation is stuck on: those of conditionals outside
         any binder (the code under a binder has not been reached yet). *)
      fun guards t =
        if is_cond t then
          let val (g, _, _) = dest_cond t
          in (if closed g then [g] else []) @ guards g end
        else if is_comb t then guards (rator t) @ guards (rand t)
        else []
      fun first_decided [] = NONE
        | first_decided (g :: gs) =
            (case decide facts g of NONE => first_decided gs | d => d)
      fun loop th =
        case first_decided (guards (rhs (concl th))) of
          NONE => th
        | SOME d =>
            (if !trace then
               (print ("EXEC decided " ^ term_to_string (lhs (concl d)) ^ " = " ^
                       term_to_string (rhs (concl d)) ^ "; size " ^
                       Int.toString (term_size (rhs (concl th))) ^ "\n"))
             else ();
            (case total (CONV_RULE (RAND_CONV
                           (QCONV (PURE_ONCE_REWRITE_CONV [d] THENC EXEC)))) th of
               SOME th' => if aconv (rhs (concl th')) (rhs (concl th)) then th
                           else loop th'
             | NONE => th))
    in
      loop (EXEC tm)
    end
end

end
