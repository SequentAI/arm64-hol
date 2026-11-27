Theory arm64IsaCv
Ancestors arm64Isa arm64Crypto RoundOp Mult tables cv_std sptree words
Libs cv_transLib wordsLib

Type finite_state = ``:(word64 spt, word8 spt, perm spt, word128 spt) arm64_machine``

Definition no_access_def:
  no_access = <| read := F; write := F; execute := F |>
End

Definition lookup_default_def:
  lookup_default default tree index =
    case lookup index tree of NONE => default | SOME value => value
End

Definition lookup_word_def:
  lookup_word default tree address = lookup_default default tree (w2n address)
End

Definition insert_word_def:
  insert_word address value tree = insert (w2n address) value tree
End

Definition finite_storage_def:
  finite_storage = <|
    get_reg := (λf (r:word5). lookup_word (0w:word64) f r);
    put_reg := (λ(r:word5) (v:word64) f. insert_word r v f);
    get_vec := (λf (r:word5). lookup_word (0w:word128) f r);
    put_vec := (λ(r:word5) (v:word128) f. insert_word r v f);
    get_byte := (λf (a:word64). lookup_word (0w:word8) f a);
    put_byte := (λ(a:word64) (v:word8) f. insert_word a v f);
    get_perm := (λf (a:word64). lookup_word no_access f a)
  |>
End

Triviality finite_storage_apply:
  finite_storage.get_reg f r = lookup_word 0w f r ∧
  finite_storage.put_reg r v f = insert_word r v f ∧
  finite_storage.get_vec q r = lookup_word 0w q r ∧
  finite_storage.put_vec r w q = insert_word r w q ∧
  finite_storage.get_byte m a = lookup_word 0w m a ∧
  finite_storage.put_byte a b m = insert_word a b m ∧
  finite_storage.get_perm p a = lookup_word no_access p a
Proof
  simp[finite_storage_def]
QED

Definition abstract_state_def:
  abstract_state (s:finite_state) : arm64_state =
    <| regs := lookup_word 0w s.regs;
       sp := s.sp;
       pc := s.pc;
       nzcv := s.nzcv;
       vregs := lookup_word 0w s.vregs;
       mem := lookup_word 0w s.mem;
       perms := lookup_word no_access s.perms |>
End

Definition abstract_result_def:
  abstract_result (Next s) = Next (abstract_state s) ∧
  abstract_result (Fault reason) = Fault reason
End

Theorem lookup_word_insert[simp]:
  lookup_word default (insert_word a v tree) =
    (a =+ v) (lookup_word default tree)
Proof
  rw[FUN_EQ_THM, lookup_word_def, lookup_default_def, insert_word_def,
     lookup_insert, combinTheory.APPLY_UPDATE_THM] >> Cases_on `x = a` >> simp[]
QED

Triviality abstract_read_bytes:
  ∀n s a. read_bytes functional_storage n (abstract_state s) a =
          read_bytes finite_storage n s a
Proof
  Induct >> simp[read_bytes_def, functional_storage_def, finite_storage_def, abstract_state_def]
QED

Triviality abstract_access_ok:
  ∀n s k a. access_ok functional_storage k n (abstract_state s) a =
            access_ok finite_storage k n s a
Proof
  Induct >> simp[access_ok_def, functional_storage_def, finite_storage_def, abstract_state_def]
QED

Triviality abstract_write_bytes:
  ∀n s a v. write_bytes functional_storage n a v (abstract_state s) =
            abstract_state (write_bytes finite_storage n a v s)
Proof
  Induct >> simp[write_bytes_def] >> rpt gen_tac >>
  `abstract_state s with mem := functional_storage.put_byte a (w2w v) (abstract_state s).mem =
   abstract_state (s with mem := finite_storage.put_byte a (w2w v) s.mem)` by
    simp[abstract_state_def, functional_storage_def, finite_storage_def] >>
  asm_simp_tac std_ss []
QED

Triviality abstract_updates:
  (abstract_state (s with pc := p) = (abstract_state s with pc := p)) ∧
  (abstract_state (s with sp := p) = (abstract_state s with sp := p)) ∧
  (abstract_state (s with nzcv := f) = (abstract_state s with nzcv := f)) ∧
  (abstract_state (s with regs := insert_word r v s.regs) =
    (abstract_state s with regs := (r =+ v) (abstract_state s).regs)) ∧
  (abstract_state (s with vregs := insert_word r w s.vregs) =
    (abstract_state s with vregs := (r =+ w) (abstract_state s).vregs)) ∧
  (abstract_state (s with vregs := insert_word r w (insert_word q u s.vregs)) =
    (abstract_state s with vregs := (r =+ w) ((q =+ u) (abstract_state s).vregs)))
Proof
  simp[abstract_state_def]
QED

Triviality abstract_reads:
  gpr functional_storage (abstract_state s) r = gpr finite_storage s r ∧
  base_reg functional_storage (abstract_state s) r = base_reg finite_storage s r ∧
  (abstract_state s).pc = s.pc ∧
  (abstract_state s).sp = s.sp ∧
  (abstract_state s).nzcv = s.nzcv ∧
  (abstract_state s).perms a = lookup_word no_access s.perms a ∧
  (abstract_state s).mem a = lookup_word 0w s.mem a ∧
  (abstract_state s).vregs q = lookup_word 0w s.vregs q
Proof
  simp[gpr_def, base_reg_def, functional_storage_def, finite_storage_def, abstract_state_def]
QED

Triviality abstract_gpr:
  set_gpr functional_storage r v (abstract_state s) =
    abstract_state (set_gpr finite_storage r v s)
Proof
  rw[set_gpr_def, functional_storage_def, finite_storage_def, abstract_updates]
QED

Triviality abstract_base:
  set_base functional_storage r v (abstract_state s) =
    abstract_state (set_base finite_storage r v s)
Proof
  rw[set_base_def, abstract_gpr, abstract_updates]
QED

Triviality abstract_pc:
  advance (abstract_state s) = abstract_state (advance s) ∧
  branch imm (abstract_state s) = abstract_state (branch imm s)
Proof
  simp[advance_def, branch_def, abstract_reads, abstract_updates]
QED

Triviality abstract_storage:
  functional_storage.get_perm (abstract_state s).perms a =
    finite_storage.get_perm s.perms a ∧
  functional_storage.get_byte (abstract_state s).mem a =
    finite_storage.get_byte s.mem a ∧
  functional_storage.get_vec (abstract_state s).vregs r =
    finite_storage.get_vec s.vregs r ∧
  (abstract_state s with vregs :=
    functional_storage.put_vec r v (abstract_state s).vregs) =
    abstract_state (s with vregs := finite_storage.put_vec r v s.vregs) ∧
  (abstract_state s with vregs := functional_storage.put_vec r v
    (functional_storage.put_vec q u (abstract_state s).vregs)) =
    abstract_state (s with vregs :=
      finite_storage.put_vec r v (finite_storage.put_vec q u s.vregs))
Proof
  simp[functional_storage_def, finite_storage_def, abstract_reads, abstract_updates]
QED

Triviality abstract_gather:
  ∀elems a. gather functional_storage elems bytes stride (abstract_state s) a =
            gather finite_storage elems bytes stride s a
Proof
  Induct >> simp[gather_def, abstract_read_bytes]
QED

Triviality abstract_scatter:
  ∀elems a v s. scatter functional_storage elems bytes stride a v (abstract_state s) =
                abstract_state (scatter finite_storage elems bytes stride a v s)
Proof
  Induct >> simp[scatter_def, abstract_write_bytes]
QED

Triviality abstract_transfers:
  (∀k s. load_vectors functional_storage k t gap elems bytes stride a (abstract_state s) =
         abstract_state (load_vectors finite_storage k t gap elems bytes stride a s)) ∧
  (∀k s. store_vectors functional_storage k t gap elems bytes stride shift a
           (abstract_state s) =
         abstract_state (store_vectors finite_storage k t gap elems bytes stride shift a s)) ∧
  (∀k s. load_lanes functional_storage k t bytes index a (abstract_state s) =
         abstract_state (load_lanes finite_storage k t bytes index a s))
Proof
  rpt conj_tac >> Induct >>
  simp[load_vectors_def, store_vectors_def, load_lanes_def, LET_THM, abstract_gather,
       abstract_scatter, abstract_read_bytes, abstract_storage]
QED

Triviality abstract_structures:
  execute_multi functional_storage q load post m opc sz t n (abstract_state s) =
    abstract_result (execute_multi finite_storage q load post m opc sz t n s) ∧
  execute_lane functional_storage q load post m r lopc sbit sz t n (abstract_state s) =
    abstract_result (execute_lane finite_storage q load post m r lopc sbit sz t n s)
Proof
  simp[execute_multi_def, execute_lane_def, structure_offset_def, pairTheory.UNCURRY,
       LET_THM, abstract_reads] >>
  rw[finish_mem_def, abstract_access_ok, abstract_transfers, abstract_base, abstract_pc,
     abstract_result_def]
QED

Triviality abstract_execute:
  execute_with functional_storage i (abstract_state s) =
    abstract_result (execute_with finite_storage i s)
Proof
  Cases_on `i` >>
  simp[execute_with_def, execute_mem_def, execute_pair_def, put_loaded_def,
       stored_value_def, finish_mem_def, logical_flags_def,
       write_arith_def, pairTheory.UNCURRY, abstract_reads, abstract_storage, abstract_gpr,
       abstract_structures,
       abstract_base, abstract_pc, abstract_access_ok, abstract_read_bytes,
       abstract_write_bytes, GSYM abstract_updates] >>
  TRY (Cases_on `m`) >>
  rw[execute_mem_def, put_loaded_def, stored_value_def, finish_mem_def, abstract_storage, abstract_result_def, abstract_gpr,
     abstract_base, abstract_pc, abstract_access_ok, abstract_read_bytes,
     abstract_write_bytes, abstract_reads, GSYM abstract_updates]
QED

Definition step_cv_def:
  step_cv feat s = step_with finite_storage feat s
End

Theorem step_cv_refines:
  step feat (abstract_state s) = abstract_result (step_cv feat s)
Proof
  simp[step_def, step_cv_def, step_with_def, abstract_reads, abstract_access_ok,
       fetch_def, abstract_read_bytes] >>
  Cases_on `decode feat (w2w (read_bytes finite_storage 4 s s.pc))` >>
  rw[abstract_result_def, abstract_execute]
QED

(* Specialize the shared definitions before translation. This removes the
   higher-order storage argument while keeping the defining equations checked. *)
Definition cv_gpr_def:
  cv_gpr s r = gpr finite_storage s r
End

Definition cv_base_reg_def:
  cv_base_reg s r = base_reg finite_storage s r
End

Definition cv_set_gpr_def:
  cv_set_gpr r value s = set_gpr finite_storage r value s
End

Definition cv_set_base_def:
  cv_set_base r value s = set_base finite_storage r value s
End

Definition cv_read_bytes_def:
  cv_read_bytes 0 (s:finite_state) (a:word64) = 0w ∧
  cv_read_bytes (SUC n) s a =
    (w2w (lookup_word 0w s.mem a) : word128) ||
    (cv_read_bytes n s (a + 1w) << 8)
End

Triviality cv_read_bytes_eq:
  ∀n s a. cv_read_bytes n s a = read_bytes finite_storage n s a
Proof
  Induct >> simp[cv_read_bytes_def, read_bytes_def, finite_storage_def]
QED

Definition cv_write_bytes_def:
  cv_write_bytes 0 (a:word64) (v:word128) (s:finite_state) = s ∧
  cv_write_bytes (SUC n) a v s =
    cv_write_bytes n (a + 1w) (v >>> 8)
      (s with mem := insert_word a (w2w v : word8) s.mem)
End

Triviality cv_write_bytes_eq:
  ∀n a v s. cv_write_bytes n a v s = write_bytes finite_storage n a v s
Proof
  Induct >> simp[cv_write_bytes_def, write_bytes_def, finite_storage_def]
QED

Definition cv_access_ok_def:
  (cv_access_ok k 0 (s:finite_state) (a:word64) ⇔ T) ∧
  (cv_access_ok k (SUC n) s a ⇔
    allowed k (lookup_word no_access s.perms a) ∧ cv_access_ok k n s (a + 1w))
End

Triviality cv_access_ok_eq:
  ∀n k s a. cv_access_ok k n s a ⇔ access_ok finite_storage k n s a
Proof
  Induct >> simp[cv_access_ok_def, access_ok_def, finite_storage_def]
QED

Definition cv_gather_def:
  cv_gather 0 bytes stride (s:finite_state) (a:word64) = (0w:word128) ∧
  cv_gather (SUC elems) bytes stride s a =
    cv_read_bytes bytes s a || (cv_gather elems bytes stride s (a + n2w stride) << (8 * bytes))
End

Triviality cv_gather_eq:
  ∀elems s a. cv_gather elems bytes stride s a = gather finite_storage elems bytes stride s a
Proof
  Induct >> simp[cv_gather_def, gather_def, cv_read_bytes_eq]
QED

Definition cv_scatter_def:
  cv_scatter 0 bytes stride (a:word64) (v:word128) (s:finite_state) = s ∧
  cv_scatter (SUC elems) bytes stride a v s =
    cv_scatter elems bytes stride (a + n2w stride) (v >>> (8 * bytes))
      (cv_write_bytes bytes a v s)
End

Triviality cv_scatter_eq:
  ∀elems a v s. cv_scatter elems bytes stride a v s = scatter finite_storage elems bytes stride a v s
Proof
  Induct >> simp[cv_scatter_def, scatter_def, cv_write_bytes_eq]
QED

Definition cv_load_vectors_def:
  cv_load_vectors 0 (t:word5) gap elems bytes stride (a:word64) (s:finite_state) = s ∧
  cv_load_vectors (SUC k) t gap elems bytes stride a s =
    cv_load_vectors k t gap elems bytes stride a
      (s with vregs := insert_word (t + n2w k)
         (cv_gather elems bytes stride s (a + n2w (k * gap))) s.vregs)
End

Triviality cv_load_vectors_eq:
  ∀k s. cv_load_vectors k t gap elems bytes stride a s =
        load_vectors finite_storage k t gap elems bytes stride a s
Proof
  Induct >> simp[cv_load_vectors_def, load_vectors_def, cv_gather_eq, finite_storage_def]
QED

Definition cv_store_vectors_def:
  cv_store_vectors 0 (t:word5) gap elems bytes stride shift (a:word64) (s:finite_state) = s ∧
  cv_store_vectors (SUC k) t gap elems bytes stride shift a s =
    cv_store_vectors k t gap elems bytes stride shift a
      (cv_scatter elems bytes stride (a + n2w (k * gap))
         (lookup_word 0w s.vregs (t + n2w k) >>> shift) s)
End

Triviality cv_store_vectors_eq:
  ∀k s. cv_store_vectors k t gap elems bytes stride shift a s =
        store_vectors finite_storage k t gap elems bytes stride shift a s
Proof
  Induct >> simp[cv_store_vectors_def, store_vectors_def, cv_scatter_eq, finite_storage_def]
QED

Definition cv_load_lanes_def:
  cv_load_lanes 0 (t:word5) bytes index (a:word64) (s:finite_state) = s ∧
  cv_load_lanes (SUC k) t bytes index a s =
    cv_load_lanes k t bytes index a
      (s with vregs := insert_word (t + n2w k)
         ((lookup_word 0w s.vregs (t + n2w k) &&
           ¬(((1w << (8 * bytes)) - 1w) << (8 * bytes * index))) ||
          (cv_read_bytes bytes s (a + n2w (k * bytes)) << (8 * bytes * index))) s.vregs)
End

Triviality cv_load_lanes_eq:
  ∀k s. cv_load_lanes k t bytes index a s = load_lanes finite_storage k t bytes index a s
Proof
  Induct >> simp[cv_load_lanes_def, load_lanes_def, LET_THM, cv_read_bytes_eq,
                 finite_storage_def]
QED

Definition cv_fetch_def:
  cv_fetch (s:finite_state) = fetch finite_storage s
End

Triviality cv_fetch_eq:
  cv_fetch s = (w2w (cv_read_bytes 4 s s.pc) : word32)
Proof
  simp[cv_fetch_def, fetch_def, cv_read_bytes_eq]
QED

Definition cv_execute_def:
  cv_execute i s = execute_with finite_storage i s
End

Definition cv_write_arith_def:
  cv_write_arith base sf sub flags carry d x y s =
    write_arith finite_storage base sf sub flags carry d x y s
End

Definition cv_finish_mem_def:
  cv_finish_mem mode n base offset s = finish_mem finite_storage mode n base offset s
End

Definition cv_put_loaded_def:
  cv_put_loaded vec t v s = put_loaded finite_storage vec t v s
End

Definition cv_stored_value_def:
  cv_stored_value vec t s = stored_value finite_storage vec t s
End

Definition cv_execute_mem_def:
  cv_execute_mem vec opc size mode t n offset s =
    execute_mem finite_storage vec opc size mode t n offset s
End

Definition cv_structure_offset_def:
  cv_structure_offset s m total = structure_offset finite_storage s m total
End

Definition cv_execute_multi_def:
  cv_execute_multi q load post m opc sz t n s =
    execute_multi finite_storage q load post m opc sz t n s
End

Definition cv_execute_lane_def:
  cv_execute_lane q load post m r opc sbit sz t n s =
    execute_lane finite_storage q load post m r opc sbit sz t n s
End

Definition cv_execute_pair_def:
  cv_execute_pair vec opc load mode t u n imm s =
    execute_pair finite_storage vec opc load mode t u n imm s
End

val aliases = [cv_gpr_def, cv_base_reg_def, cv_set_gpr_def, cv_set_base_def,
               cv_read_bytes_eq, cv_write_bytes_eq, cv_access_ok_eq,
               cv_fetch_def, cv_write_arith_def, cv_finish_mem_def, cv_put_loaded_def,
               cv_gather_eq, cv_scatter_eq, cv_load_vectors_eq, cv_store_vectors_eq,
               cv_load_lanes_eq, cv_structure_offset_def, cv_execute_multi_def,
               cv_execute_lane_def,
               cv_stored_value_def, cv_execute_mem_def, cv_execute_pair_def,
               cv_execute_def, step_cv_def];

fun specialise_clause th =
  let
    val eq = SPEC_ALL th
    val arg = hd (snd (strip_comb (lhs (concl eq))))
    val storage = ``finite_storage``
    val typed = INST_TYPE (match_type (type_of arg) (type_of storage)) eq
  in
    INST [inst (match_type (type_of arg) (type_of storage)) arg |-> storage] typed
    |> PURE_REWRITE_RULE (map (GSYM o SPEC_ALL) aliases)
    |> SIMP_RULE (srw_ss()) [finite_storage_apply]
    |> PURE_REWRITE_RULE (map (GSYM o SPEC_ALL) aliases)
  end;

fun translate th =
  cv_auto_trans (PURE_REWRITE_RULE [lookup_word_def, insert_word_def] th);

fun translate_specialised th =
  translate (LIST_CONJ (map specialise_clause (CONJUNCTS (SPEC_ALL th))));

val () = cv_auto_trans bitTheory.BIT_REVERSE_def;

(* For the eight byte indices, use the translated word_bit operation. *)
Triviality byte_index_is_bit:
  n < 8 ⇒ ((w:word8) ' n ⇔ word_bit n w)
Proof
  simp[word_bit_thm]
QED

val () =
  let
    fun at_byte th = INST_TYPE [alpha |-> ``:8``] th
    fun count_clause i =
      SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `^(numSyntax.term_of_int i)`]
        (SPEC_ALL (at_byte bit_count_upto_SUC)))
    val clauses = at_byte bit_count_upto_0 :: List.tabulate (8, count_clause)
  in
    cv_auto_trans (SIMP_RULE (srw_ss()) (byte_index_is_bit :: clauses)
      (at_byte bit_count_def))
  end;
val () = app (fn ty =>
  cv_auto_trans (INST_TYPE [alpha |-> ty] word_quot_def)) [``:32``, ``:64``];
val aes_sbox_pre_def = cv_auto_trans_pre "aes_sbox_pre" Sbox_def;
val aes_inv_sbox_pre_def = cv_auto_trans_pre "aes_inv_sbox_pre" InvSbox_def;

val byte_bound = SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:8``] w2n_lt);

Theorem aes_sbox_pre[cv_pre]:
  aes_sbox_pre x
Proof
  simp[aes_sbox_pre_def, byte_bound]
QED

Theorem aes_inv_sbox_pre[cv_pre]:
  aes_inv_sbox_pre x
Proof
  simp[aes_inv_sbox_pre_def, byte_bound]
QED

(* Instantiate the FIPS round maps before translating them. *)
fun translate_aes_map def map_def =
  cv_auto_trans (SIMP_RULE std_ss [map_def] (AP_THM def
    (mk_var ("s", dom_rng (type_of (lhs (concl def))) |> #1))));

val () = app cv_auto_trans
  [to_state_def, from_state_def, ShiftRows_def, InvShiftRows_def,
   vector_to_aes_def, aes_pack_column_def, aes_to_vector_def];
val () = app (fn def => translate_aes_map def genSubBytes_def) [SubBytes_def, InvSubBytes_def];
val () = app (cv_auto_trans o REWRITE_RULE [mult_unroll]) [MultCol_def, InvMultCol_def];
val () = app (fn def => translate_aes_map def genMixColumns_def) [MixColumns_def, InvMixColumns_def];
val () = app cv_auto_trans [aes_value_def, crc32_bit_def, crc32_bits_def,
                            crc32_value_def, clmul_def, pmull_value_def];

val () = cv_auto_trans encode_def;
val () = cv_auto_trans decode_def;
val () = app translate [cv_read_bytes_def, cv_write_bytes_def, cv_access_ok_def,
                        cv_gather_def, cv_scatter_def, cv_load_vectors_def,
                        cv_store_vectors_def, cv_load_lanes_def];
val () = cv_auto_trans cv_fetch_eq;
val () = app (fn ty =>
  cv_auto_trans (REWRITE_RULE [LET_THM]
    (INST_TYPE [alpha |-> ty] wordsTheory.add_with_carry_def)))
  [``:32``, ``:64``];
val () = app translate_specialised
  [gpr_def, base_reg_def, set_gpr_def, set_base_def, write_arith_def, finish_mem_def,
   put_loaded_def, stored_value_def, execute_mem_def, execute_pair_def,
   structure_offset_def, execute_multi_def, execute_lane_def, execute_with_def, step_with_def];
