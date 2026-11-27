Theory arm64Native
Ancestors arm64IsaCv arm64NativeCases
Libs cv_transLib wordsLib

Definition nzcv_of_bits_def:
  nzcv_of_bits (f:word4) = (word_bit 3 f, word_bit 2 f, word_bit 1 f, word_bit 0 f)
End

Definition bits_of_nzcv_def:
  bits_of_nzcv (n,z,c,v) : word4 =
    (if n then 8w else 0w) || (if z then 4w else 0w) ||
    (if c then 2w else 0w) || (if v then 1w else 0w)
End

Definition byte_at_def:
  byte_at (w:word32) i = w2w (w >>> (8 * i)) : word8
End

Definition put_many_def:
  put_many base [] tree = tree ∧
  put_many base (value::values) tree =
    put_many (base + 1) values (insert base value tree)
End

Definition read_window_def:
  read_window default 0 base tree = [] ∧
  read_window default (SUC n) base tree =
    lookup_default default tree base :: read_window default n (base + 1) tree
End

(* The observed vector registers start at vbase and wrap from V31 to V0. *)
Definition put_vectors_def:
  put_vectors base [] tree = tree ∧
  put_vectors base (value::values) tree =
    put_vectors ((base + 1) MOD 32) values (insert base value tree)
End

Definition read_vectors_def:
  read_vectors 0 base tree = [] ∧
  read_vectors (SUC n) base tree =
    lookup_default 0w tree base :: read_vectors n ((base + 1) MOD 32) tree
End

Definition test_state_at_def:
  test_state_at vbase w (pc,sp,flags,link,regs,vectors,data) : finite_state =
    let gpr = insert 30 link (put_many 0 regs LN);
        vec = put_vectors vbase vectors LN;
        code = put_many 208 literal_pool (put_many 268 literal_pool
          (put_many 256 [byte_at w 0; byte_at w 1; byte_at w 2; byte_at w 3] LN));
        mem = put_many 4096 data code;
        code_perms = put_many 208 (REPLICATE 48 (perm T F T))
          (put_many 268 (REPLICATE 48 (perm T F T))
            (put_many 256 (REPLICATE 4 (perm T F T)) LN));
        perms = put_many 4096 (REPLICATE 64 (perm T T F)) code_perms
    in arm64_machine gpr sp pc (nzcv_of_bits flags) vec mem perms
End

Definition test_state_def:
  test_state w sample = test_state_at 0 w sample
End

Definition observe_at_def:
  observe_at vbase (s:finite_state) : observation =
    (s.pc, s.sp, bits_of_nzcv s.nzcv, lookup_word 0w s.regs (30w:word5),
     read_window 0w 4 0 s.regs,
     read_vectors 4 vbase s.vregs,
     read_window 0w 64 4096 s.mem)
End

Definition observe_def:
  observe s = observe_at 0 s
End

Definition agrees_at_def:
  agrees_at vbase ((w,instr,before,after) : native_case) ⇔
    decode armv9_4 w = SOME instr ∧ encode instr = SOME w ∧
    (case step_cv armv9_4 (test_state_at vbase w before) of
       Fault reason => F
     | Next s => observe_at vbase s = after)
End

Definition agrees_def:
  agrees c ⇔ agrees_at 0 c
End

val feature = EVAL ``armv9_4``;
val enabled = rhs (concl feature);

val simd_cases =
  map (fn pair => let val (index, base) = pairSyntax.dest_pair pair in
                    (numSyntax.int_of_term index, numSyntax.int_of_term base)
                  end)
    (fst (listSyntax.dest_list (rhs (concl native_simd_cases_def))));

fun check i =
  let
    val name = "native_case_" ^ Int.toString i
    val def = DB.fetch "arm64NativeCases" (name ^ "_def")
    val sample = rhs (concl def)
    val (word, rest) = pairSyntax.dest_pair sample
    val (instr, rest) = pairSyntax.dest_pair rest
    val initial = fst (pairSyntax.dest_pair rest)
    val vbase = case List.find (fn (index, _) => i = index) simd_cases of
                  SOME (_, base) => base
                | NONE => 0
    val base = numSyntax.term_of_int vbase
    val prepared = EVAL ``test_state_at ^base ^word ^initial``
    val decoded = cv_eval ``decode ^enabled ^word``
    val encoded = cv_eval ``encode ^instr``
    val state = rhs (concl prepared)
    val stepped = cv_eval ``step_cv ^enabled ^state``
    val predicate = if vbase = 0 then ``agrees`` else ``agrees_at ^base``
    val comparison = REWRITE_CONV
      [agrees_def, agrees_at_def, feature, prepared, decoded, encoded, stepped]
      (mk_comb (predicate, sample))
    val result = EQT_ELIM (TRANS comparison (EVAL (rhs (concl comparison))))
  in
    ignore (save_thm (name ^ "_agrees",
      PURE_REWRITE_RULE [GSYM def] result))
  end;

fun check_fault name feat input reason =
  let
    val prepare = EVAL THENC SIMP_CONV (srw_ss ())
      [arm64IsaTheory.arm64_machine_fn_updates,
       arm64IsaTheory.arm64_machine_accessors] THENC EVAL
    val prepared = prepare input
    val state = rhs (concl prepared)
    val stepped = cv_eval ``step_cv ^feat ^state``
    val expected = ``Fault ^reason : finite_state arm64_result``
    val result = TRANS (AP_TERM ``step_cv ^feat`` prepared) stepped
  in
    if aconv (rhs (concl result)) expected then ignore (save_thm (name, result))
    else raise Fail (name ^ ": expected " ^ term_to_string expected)
  end handle cv_repLib.NeedsTranslation (_, term) =>
    raise Fail (name ^ ": could not evaluate " ^ term_to_string (fst (strip_comb term)));

val initial = ``(256w, 8192w, 0w, 0w, [4096w;4096w], [], REPLICATE 64 0w) : observation``;
val store_state = ``test_state 0xad000400w ^initial``;
val load_state = ``test_state 0xad400420w ^initial``;
val () = check_fault "store_rejects_read_only_last_byte" enabled
  ``^store_state with perms := insert 4127 (perm T F F) (^store_state).perms`` ``Store``;
val () = check_fault "store_rejects_executable_last_byte" enabled
  ``^store_state with perms := insert 4127 (perm T T T) (^store_state).perms`` ``Store``;
val () = check_fault "load_rejects_unreadable_last_byte" enabled
  ``^load_state with perms := insert 4127 (perm F F F) (^load_state).perms`` ``Load``;
val () = check_fault "fetch_rejects_writable_code" enabled
  ``^store_state with perms := insert 259 (perm T T T) (^store_state).perms`` ``Fetch``;
val () = check_fault "fetch_rejects_misaligned_pc" enabled
  ``^store_state with pc := 257w`` ``PCAlignment``;
val () = check_fault "sp_load_rejects_misaligned_base" enabled
  ``test_state 0x384017e1w ^initial with sp := 4097w`` ``SPAlignment``;
val () = check_fault "q_store_requires_asimd" ``^enabled with asimd := F`` store_state ``Unsupported``;
val () = check_fault "crc_requires_crc32" ``^enabled with crc32 := F``
  ``test_state 0x9ac15c00w ^initial`` ``Unsupported``;
val () = check_fault "crc_rejects_wrong_sf" enabled
  ``test_state 0x1ac15c00w ^initial`` ``Unsupported``;
val () = check_fault "pmull_requires_pmull" ``^enabled with pmull := F``
  ``test_state 0x4ee1e000w ^initial`` ``Unsupported``;
val () = check_fault "pmull_rejects_unsupported_8h_form" enabled
  ``test_state 0x0e21e000w ^initial`` ``Unsupported``;
val () = check_fault "aese_requires_aes" ``^enabled with aes := F``
  ``test_state 0x4e284820w ^initial`` ``Unsupported``;
val () = check_fault "aese_requires_asimd" ``^enabled with asimd := F``
  ``test_state 0x4e284820w ^initial`` ``Unsupported``;
val () = check_fault "unknown_word_is_unsupported" enabled
  ``test_state 0w ^initial`` ``Unsupported``;
val () = check_fault "ccmp_rejects_bit4" enabled
  ``test_state 0xfa498812w ^initial`` ``Unsupported``;
val () = check_fault "and_imm_rejects_reserved_mask" enabled
  ``test_state 0x1200fc00w ^initial`` ``Unsupported``;
val () = check_fault "post_index_load_rejects_base_destination_overlap" enabled
  ``test_state 0x38401442w ^initial`` ``Unsupported``;
val () = check_fault "q_load_rejects_destination_overlap" enabled
  ``test_state 0xad400020w ^initial`` ``Unsupported``;

(* Single-register post-index transfers must check the last byte before writeback. *)
val single_store = ``test_state 0xb8004401w ^initial``;
val single_load = ``test_state 0xf8408401w ^initial``;
val () = check_fault "single_store_rejects_executable_last_byte" enabled
  ``^single_store with perms := insert 4099 (perm T T T) (^single_store).perms`` ``Store``;
val () = check_fault "single_load_rejects_unreadable_last_byte" enabled
  ``^single_load with perms := insert 4103 (perm F F F) (^single_load).perms`` ``Load``;

val pair_store = ``test_state 0xa8810801w ^initial``;
val () = check_fault "scalar_pair_rejects_executable_last_byte" enabled
  ``^pair_store with perms := insert 4111 (perm T T T) (^pair_store).perms`` ``Store``;
val () = check_fault "scalar_pair_rejects_unreadable_last_byte" enabled
  ``test_state 0xa8c10801w ^initial with
    perms := insert 4111 (perm F F F) (^pair_store).perms`` ``Load``;
val () = check_fault "scalar_preindex_sp_checks_base" enabled
  ``test_state 0xa9bf8be1w ^initial with sp := 4104w`` ``SPAlignment``;
val () = check_fault "pair_writeback_rejects_base_overlap" enabled
  ``test_state 0xa8810800w ^initial`` ``Unsupported``;
val () = check_fault "pair_writeback_rejects_second_register_overlap" enabled
  ``test_state 0xa8810001w ^initial`` ``Unsupported``;
val () = check_fault "scalar_pair_load_rejects_duplicate_destination" enabled
  ``test_state 0xa9400401w ^initial`` ``Unsupported``;
val () = check_fault "w_bitfield_rejects_oversize_rotation" enabled
  ``test_state 0x53207c20w ^initial`` ``Unsupported``;

val q_post_load = ``test_state 0x3cc10420w ^initial``;
val () = check_fault "q_post_load_rejects_unreadable_last_byte" enabled
  ``^q_post_load with perms := insert 4111 (perm F F F) (^q_post_load).perms`` ``Load``;
val () = check_fault "q_post_load_checks_sp_before_access" enabled
  ``test_state 0x3cc107e0w ^initial with sp := 4097w`` ``SPAlignment``;
val () = check_fault "q_pair_store_checks_sp_before_access" enabled
  ``test_state 0xad0003e0w ^initial with sp := 4097w`` ``SPAlignment``;
val () = check_fault "simd_unprivileged_load_is_unallocated" enabled
  ``test_state 0x3cc10820w ^initial`` ``Unsupported``;
val () = check_fault "addv_64bit_arrangement_is_unsupported" enabled
  ``test_state 0x4ef1b800w ^initial`` ``Unsupported``;
(* Match the RET on the read-only page used by the hardware test. *)
val page_store = ``test_state 0xf9000001w ^initial``;
val read_only_page =
  ``^page_store with
    <| mem := put_many 4096 (GENLIST (byte_at 0xd65f03c0w) 4) (^page_store).mem;
       perms := put_many 4096 (REPLICATE 64 (perm T F F)) (^page_store).perms |>``;
val () = check_fault "read_only_page_denies_store" enabled read_only_page ``Store``;
val () = check_fault "read_only_page_denies_fetch" enabled
  ``^read_only_page with pc := 4096w`` ``Fetch``;
val () = check_fault "cnt_rejects_reserved_size" enabled
  ``test_state 0x0e605800w ^initial`` ``Unsupported``;
val () = check_fault "tbl_multi_register_is_unsupported" enabled
  ``test_state 0x4e012000w ^initial`` ``Unsupported``;
val () = check_fault "ext_64bit_arrangement_is_unsupported" enabled
  ``test_state 0x2e010000w ^initial`` ``Unsupported``;
val () = check_fault "rev32_rejects_reserved_size" enabled
  ``test_state 0x6ea00800w ^initial`` ``Unsupported``;
val () = check_fault "shl_16bit_lanes_are_unsupported" enabled
  ``test_state 0x4f105400w ^initial`` ``Unsupported``;
val q_store = ``test_state 0x3d800020w ^initial``;
val () = check_fault "q_store_rejects_unwritable_last_byte" enabled
  ``^q_store with perms := insert 4111 (perm T F F) (^q_store).perms`` ``Store``;
val () = check_fault "q_store_checks_sp_before_access" enabled
  ``test_state 0x3d8003e0w ^initial with sp := 4097w`` ``SPAlignment``;
val () = check_fault "umulh_rejects_reserved_accumulator" enabled
  ``test_state 0x9bc07800w ^initial`` ``Unsupported``;
val () = app (fn (index, _) =>
  let
    val name = "native_case_" ^ Int.toString index
    val sample = rhs (concl (DB.fetch "arm64NativeCases" (name ^ "_def")))
    val (word, _) = pairSyntax.dest_pair sample
  in
    check_fault (name ^ "_requires_asimd") ``^enabled with asimd := F``
      ``test_state ^word ^initial`` ``Unsupported``
  end) simd_cases;

val count = numSyntax.int_of_term (rhs (concl native_case_count_def));
val () = List.app check (List.tabulate (count, I));
