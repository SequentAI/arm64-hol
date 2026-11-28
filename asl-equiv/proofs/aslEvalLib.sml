(* Symbolic evaluation of the Armv9.4-A specification (asl-equiv/model).

   CEVAL evaluates with every definition of the Sail and Lem libraries and of
   the model's types theory, plus the instruction-set entry points, so an
   instruction's decode runs down to the call of its execute function. Adapted
   from HOL's examples/l3-machine-code/arm8/asl-equiv/l3_equivalenceLib. *)
structure aslEvalLib =
struct

open HolKernel boolLib bossLib
open armv9_p32Theory arm64AslTheory aslLemmasTheory

(* Word equalities left by evaluation recur many times per instruction, so
   their bit-blasting results, failures included, are remembered. *)
val eq_trace = ref false
val eq_memo = ref (Redblackmap.mkDict Term.compare : (term, thm option) Redblackmap.dict)
fun memo_eq_conv t =
  let val r = case Redblackmap.peek (!eq_memo, t) of
                SOME r => r
              | NONE =>
                  (* Bit-blasting cannot settle integer arithmetic, and can
                     search for long trying. *)
                  if can (find_term (fn x => type_of x = intSyntax.int_ty)) t then NONE else
                  let val () = if !eq_trace then print ("BLAST " ^ term_to_string t ^ "\n") else ()
                      (* Only decisions: an undecided equation's bit-level
                         form (carry chains, say) is much bigger. *)
                      fun decision th =
                        let val r = rhs (concl th)
                        in if aconv r T orelse aconv r F then SOME th else NONE end
                      val t0 = Time.now ()
                      val r = decision (blastLib.BBLAST_CONV t)
                              handle UNCHANGED => NONE | HOL_ERR _ => NONE
                      val () = if !eq_trace then print ("BLAST done " ^ (if isSome r then "rewrote" else "no") ^ " " ^ Time.toString (Time.- (Time.now (), t0)) ^ "\n") else ()
                  in eq_memo := Redblackmap.insert (!eq_memo, t, r); r end
  in case r of SOME th => th | NONE => raise UNCHANGED end
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
    aslLemmasTheory.read_gpr_eq, aslLemmasTheory.write_gpr_eq,
    aslLemmasTheory.n2w_w2n_add, aslLemmasTheory.bool_of_bitU_eq,
    aslLemmasTheory.add_vec_word, aslLemmasTheory.add_vec_int_word,
    aslLemmasTheory.foreachM_rw, sail2_valuesAuxiliaryTheory.index_list_rw,
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
     evaluation reduces without going under a binder; alignment on words as
     shifts (align_bits_word), since evaluation unfolds the dictionary
     argument before an equation for align_bits could match it. *)
  val def_rewrites =
    [arm64AslTheory.update_lambda, aslLemmasTheory.align_bits_word]
  fun add_defs thy cmp =
    List.foldl add_def cmp
      (map (PURE_REWRITE_RULE def_rewrites o unpack o #thm)
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
    (* add_with_carry stays as it is: AddWithCarry_add_with_carry states the
       specification's AddWithCarry with it, as arm64-hol does. *)
    |> (fn c => computeLib.scrub_const c wordsSyntax.add_with_carry_tm)
    |> intReduce.add_int_compset
    |> computeLib.add_conv
         (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)
    |> computeLib.add_conv
         (``$= : α word -> α word -> bool``, 2, memo_eq_conv)
    |> bitstringLib.add_bitstring_compset
    |> stringLib.add_string_compset
    |> (fn cmp => List.foldl (fn (thy, c) => add_types thy c) cmp thys)
    |> (fn cmp => List.foldl (fn (thy, c) => add_defs thy c) cmp thys)
    (* Register names stay as num_to_dec_string, as in gpr_rel. *)
    |> (fn c => computeLib.scrub_const c ``num_to_dec_string``)
    |> computeLib.add_thms
         (map (PURE_REWRITE_RULE [arm64AslTheory.update_lambda]) overrides)
    (* The instruction fetched, as arm64-hol's fetch, which evaluation
       leaves as it is: decode then waits for its encoding. *)
    |> computeLib.add_thms [aslLemmasTheory.FLOOKUP_asl_mem, sumTheory.sum_case_def,
                            aslLemmasTheory.fetch_bits, wordsTheory.w2w_id]
    |> computeLib.add_thms (arm64AslTheory.arm64_asl_next_def :: entry_defs)
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
    th |> CONV_RULE (computeLib.CBV_CONV
                       (computeLib.add_thms (wordsTheory.word_bit_def :: defs) exec_cmp))
       |> CONJUNCTS

  (* A field of an instruction's encoding, (h >< l) w, as the variable of
     the encoding that it is, proved bit by bit. Fields recur, so each is
     proved once. *)
  fun ERR f m = mk_HOL_ERR "aslEvalLib" f m
  val field_cache = ref ([] : thm list)
  fun FIELD_CONV t =
    case List.find (fn th => aconv (lhs (concl th)) t) (!field_cache) of
      SOME th => th
    | NONE =>
    let
      val (_, _, w, _) = wordsSyntax.dest_word_extract t
      val vs = List.filter (fn v => type_of v = type_of t) (free_vars w)
      fun try [] = raise ERR "FIELD_CONV" "no variable"
        | try (v :: vs) = blastLib.BBLAST_PROVE (mk_eq (t, v))
                          handle HOL_ERR _ => try vs
                               | HolSatLib.SAT_cex _ => try vs
      val th = try vs
    in
      field_cache := th :: List.take (!field_cache, Int.min (length (!field_cache), 63));
      th
    end
  val FIELDS_CONV = DEPTH_CONV FIELD_CONV

  (* Proves a guard true or false from facts about bits of registers. Integer
     comparisons of words' values become comparisons of words first. *)
  val guard_conv =
    QCONV (SIMP_CONV (srw_ss())
      [integerTheory.int_ge, integerTheory.int_gt, integerTheory.INT_LT,
       integerTheory.INT_LE, integerTheory.INT_INJ, aslLemmasTheory.w2n_le_word_ls,
       aslLemmasTheory.w2n_lt_31, aslLemmasTheory.w2n_lt_64, aslLemmasTheory.w2n_add_lt_64,
       aslLemmasTheory.w2n_lt_word_lo, aslLemmasTheory.word_lo_w2n,
       aslLemmasTheory.int_sub_lt_0, aslLemmasTheory.w2n_eq_n2w])
  fun decide facts g =
    let
      (* Facts fix registers or their bits to values (the feature register,
         say); rewriting with them and evaluating can settle a guard by
         itself. *)
      fun rewrite_of th =
        if is_eq (concl th) then th
        else if is_neg (concl th) then EQF_INTRO th
        else EQT_INTRO th
      val eqs = map rewrite_of facts
      fun is_word_fact th =
        not (is_forall (concl th)) andalso
        (not (is_eq (concl th)) orelse
         wordsSyntax.is_word_type (type_of (lhs (concl th))))
      val word_facts = List.filter is_word_fact facts
      val hyp = list_mk_conj (map concl word_facts)
      val facts_th = LIST_CONJ word_facts
      fun is_bool_lit t = aconv t T orelse aconv t F
      (* A bit of a word no fact mentions (of a stored register, say)
         cannot be decided; bit-blasting would only search. *)
      fun free_bit t =
        fcpSyntax.is_fcp_index t andalso
        let val w = fst (fcpSyntax.dest_fcp_index t)
        in not (wordsSyntax.is_word_literal w) andalso
           not (List.exists (fn th => can (find_term (aconv w)) (concl th)) facts)
        end
      (* Fields of the encoding first, so that a guard on one (Rn = 31, say)
         is the fact about it (n ≠ 31w) that rewriting settles. *)
      val pre =
        if free_bit g then raise mk_HOL_ERR "aslEvalLib" "decide" "free bit" else
        QCONV (FIELDS_CONV THENC PURE_REWRITE_CONV eqs THENC EXEC THENC
               (fn t => if is_bool_lit t then raise UNCHANGED
                        else (guard_conv THENC REWRITE_CONV eqs) t)) g
      val g' = rhs (concl pre)
      (* Most guards hold or fail by themselves (bits of an instruction's
         encoding, say); only the rest need the facts. *)
      fun prove_alone t = SOME (blastLib.BBLAST_PROVE t)
                          handle HOL_ERR _ => NONE | UNCHANGED => NONE
                               | HolSatLib.SAT_cex _ => NONE
      fun prove t = SOME (MP (blastLib.BBLAST_PROVE (mk_imp (hyp, t))) facts_th)
                    handle HOL_ERR _ => NONE | UNCHANGED => NONE
                         | HolSatLib.SAT_cex _ => NONE
      fun first [] = NONE
        | first (f :: fs) = case f () of NONE => first fs | r => r
    in
      if aconv g' T orelse aconv g' F then SOME pre
      else if free_bit g' then NONE
      else
        first [
          fn () => Option.map (fn th => TRANS pre (EQT_INTRO th)) (prove_alone g'),
          fn () => Option.map (fn th => TRANS pre (EQF_INTRO th)) (prove_alone (mk_neg g')),
          fn () => Option.map (fn th => TRANS pre (EQT_INTRO th)) (prove g'),
          fn () => Option.map (fn th => TRANS pre (EQF_INTRO th)) (prove (mk_neg g'))]
    end
    handle HOL_ERR _ => NONE

  (* Evaluates an execution of the specification on a state, deciding each
     conditional it gets stuck on from the facts, and, where none can be
     decided, rewriting with the equations rws (the state's memory and PC
     as arm64-hol's, say) and evaluating on. *)
  val trace = ref false
  fun exec_with deadline facts rws tm =
    let
      val t0 = Time.now ()
      fun out_of_time () =
        case deadline of NONE => false | SOME d => Time.> (Time.now (), d)
      fun stamp () = Real.fmt (StringCvt.FIX (SOME 3)) (Time.toReal (Time.- (Time.now (), t0)))
      val globals = free_varsl (tm :: map concl (facts @ rws))
      fun closed g = List.all (fn v => tmem v globals) (free_vars g)
      (* The guards evaluation is stuck on: those of conditionals outside
         any binder (the code under a binder has not been reached yet). *)
      fun guards t =
        if is_cond t then
          let val (g, _, _) = dest_cond t
          in (if closed g then [g] else []) @ guards g end
        else if is_comb t then guards (rator t) @ guards (rand t)
        else []
      (* Guards that could not be decided stay so: the facts do not change. *)
      val undecided = ref (HOLset.empty Term.compare)
      fun decide_new g =
        if HOLset.member (!undecided, g) then NONE
        else (if !trace then print (stamp () ^ " EXEC deciding " ^ term_to_string g ^ "\n") else ();
              decide facts g) |> (fn r => case r of
               NONE => (undecided := HOLset.add (!undecided, g);
                        if !trace then print (stamp () ^ " EXEC undecided " ^ term_to_string g ^ "\n") else ();
                        NONE)
             | d => d)
      fun loop th =
        if out_of_time () then th else
        case total (CONV_RULE (RAND_CONV (QCHANGED_CONV (PURE_REWRITE_CONV rws)))) th of
          SOME th' =>
            (if !trace then
               print (stamp () ^ " EXEC rewriting; size " ^
                      Int.toString (term_size (rhs (concl th))) ^ "\n")
             else ();
             loop (CONV_RULE (RAND_CONV (QCONV EXEC)) th'))
        | NONE =>
        (* Every guard evaluation is stuck on that can be decided, at once:
           each round evaluates the whole term again. *)
        case List.mapPartial decide_new
               (HOLset.listItems (HOLset.addList (HOLset.empty Term.compare,
                                                  guards (rhs (concl th))))) of
          [] => th
        | ds =>
            (if !trace then
               List.app (fn d => print (stamp () ^ " EXEC decided " ^ term_to_string (lhs (concl d)) ^
                                        " = " ^ term_to_string (rhs (concl d)) ^ "\n")) ds
             else ();
             case total (CONV_RULE (RAND_CONV (QCONV (PURE_REWRITE_CONV ds THENC EXEC)))) th of
               SOME th' => if aconv (rhs (concl th')) (rhs (concl th)) then th else loop th'
             | NONE => th)
    in
      loop (QCONV EXEC tm)
    end
  fun EXEC_WITH_RW facts rws tm = exec_with NONE facts rws tm
  fun EXEC_WITH facts tm = EXEC_WITH_RW facts [] tm

  (* Facts from assumptions: arm64_asl_ok and state_rel split into the
     conditions they state, evaluated as the specification's registers are;
     other assumptions as they are. *)
  val ok_facts =
    facts_of [arm64AslTheory.arm64_asl_ok_def, aslLemmasTheory.asl_features_eq]
  (* Equations evaluated on each side, so that word equations stay
     equations. *)
  fun rel_facts th =
    th |> PURE_REWRITE_RULE [arm64AslTheory.state_rel_def, arm64AslTheory.vreg_rel_def,
                             arm64AslTheory.flag_rel_def, LET_THM]
       |> BETA_RULE
       |> CONJUNCTS
       |> map (fn c => if is_eq (concl c) then CONV_RULE (BINOP_CONV (QCONV EXEC)) c else c)
  fun is_app c th = same_const (fst (strip_comb (concl th))) c
                    handle HOL_ERR _ => false
  (* The facts of an assumption are the same at every step of a proof. *)
  val facts_memo = ref (Redblackmap.mkDict Term.compare)
  fun assum_facts th =
    case Redblackmap.peek (!facts_memo, concl th) of
      SOME r => r
    | NONE =>
      let val r =
            if is_app ``arm64_asl_ok`` th then (ok_facts th, [])
            else if is_app ``state_rel`` th then
              let val fs = rel_facts th in (fs, List.filter (is_eq o concl) fs) end
            else ([th], if is_eq (concl th) then [th] else [])
      in facts_memo := Redblackmap.insert (!facts_memo, concl th, r); r end
  (* Evaluates the first subterm of the goal matching pat, with the
     assumptions as facts and rewrites, and the extra rewrites rws. *)
  fun EXEC_AT_TAC pat rws : tactic = fn (asms, g) =>
    let
      val t = find_term (can (match_term pat)) g
      val (fs, eqs) = (List.concat ## List.concat)
                        (ListPair.unzip (map (assum_facts o ASSUME) asms))
      val th = EXEC_WITH_RW fs (eqs @ rws) t
    in
      PURE_ONCE_REWRITE_TAC [th] (asms, g)
    end
  (* One slice of evaluation of a subterm of the goal: about slice seconds of
     it, so that each proof step stays well within the tactic timeout; a
     proof gives as many such steps as the evaluation takes. Once the term
     is a single outcome, a slice does nothing. *)
  val slice = ref 0.6
  fun is_value_singleton t =
    pred_setSyntax.is_insert t andalso pred_setSyntax.is_empty (rand t) andalso
    can (match_term ``Value v``) (fst (pairSyntax.dest_pair (rand (rator t))))
    handle HOL_ERR _ => false
  fun exec_step_tac select : tactic = fn (asms, g) =>
    let
      val t = select g
    in
      if is_value_singleton t then ALL_TAC (asms, g)
      else
        let
          val deadline = Time.+ (Time.now (), Time.fromReal (!slice))
          val (fs, eqs) = (List.concat ## List.concat)
                            (ListPair.unzip (map (assum_facts o ASSUME) asms))
          val th = exec_with (SOME deadline) fs eqs t
        in
          if aconv (rhs (concl th)) t then ALL_TAC (asms, g)
          else PURE_ONCE_REWRITE_TAC [th] (asms, g)
        end
    end
  (* In a goal ∃asl'. t = {(Value (), asl')} ∧ ..., t. *)
  val EXEC_STEP_TAC = exec_step_tac (lhs o fst o dest_conj o snd o dest_exists)
  val EXEC_LHS_STEP_TAC = exec_step_tac lhs
  (* Evaluates the left-hand side of the goal. *)
  val EXEC_TAC : tactic = fn (asms, g) =>
    EXEC_AT_TAC (lhs g) [] (asms, g)
  (* Evaluates the right-hand side of the goal, and proves it if both sides
     are then the same. *)
  val EXEC_RHS_TAC : tactic = fn (asms, g) =>
    let
      val (fs, eqs) = (List.concat ## List.concat)
                        (ListPair.unzip (map (assum_facts o ASSUME) asms))
      val th = EXEC_WITH_RW fs eqs (rhs g)
    in
      (CONV_TAC (RHS_CONV (K th)) THEN TRY (MATCH_ACCEPT_TAC EQ_REFL)) (asms, g)
    end
end

end
