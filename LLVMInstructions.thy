theory LLVMInstructions
  imports "LLVMState"
begin



section "Execution"


subsection "Memory instruction helpers"

fun store_to_stack_or_heap :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value \<Rightarrow> state result" where
  "store_to_stack_or_heap (r, s, h) (saddr a) v = do {
    s' \<leftarrow> set_memory s a v;
    return (r, s', h)
  }"
| "store_to_stack_or_heap (r, s, h) (haddr a) v = do {
    h' \<leftarrow> set_memory h a v;
    return (r, s, h')
  }"

fun store_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "store_value (r, s, m) v (ptr p) = do {
    a \<leftarrow> get_value r p;
    ad \<leftarrow> (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address);
    val \<leftarrow> get_value r v;
    store_to_stack_or_heap (r, s, m) ad val
  }"

lemma store_value_ok_if[wp_intro]:
  assumes "(\<exists>a ad val s' p. pointer = ptr p \<and> get_value r p = ok a \<and> a = addr ad \<and> get_value r v = ok val \<and> store_to_stack_or_heap (r, s, m) ad val = ok s')"
  shows "(\<exists>s'. store_value (r, s, m) v pointer = ok s')"
  using assms by auto

lemma store_value_intro:
  assumes "\<exists>s'. store_value s v p = ok s'"
  assumes "\<And>s'. store_value s v p = ok s' \<Longrightarrow> Q s'"
  shows "wp_never_err (store_value s v p) Q"
  using assms by auto


fun load_from_stack_or_heap :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "load_from_stack_or_heap (r, s, h) (saddr a) = get_memory s a"
| "load_from_stack_or_heap (r, s, h) (haddr a) = get_memory h a"

fun load_value :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "load_value (r, s, h) n (ptr p) = do {
    a \<leftarrow> get_value r p;
    ad \<leftarrow> (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address);
    v \<leftarrow> load_from_stack_or_heap (r, s, h) ad;
    r' \<leftarrow> set_register r n v;
    return (r', s, h)
  }"


subsection "Add instruction helpers"
(* TODO: support pointers *)

fun unsigned_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "unsigned_overflow32 a b = ((a + b) < a)"

fun signed_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "signed_overflow32 a b = (sint a + sint b \<noteq> sint (a + b))"

fun unsigned_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "unsigned_overflow64 a b = ((a + b) < a)"

fun signed_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "signed_overflow64 a b = (sint a + sint b \<noteq> sint (a + b))"

fun add_values :: "llvm_add_wrap \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "add_values wrap (vi32 a) (vi32 b) = (
      let uov = unsigned_overflow32 a b;
          sov = signed_overflow32 a b
      in case wrap of
           add_default \<Rightarrow> ok (vi32 (a + b))
         | add_nuw \<Rightarrow> (if uov then ok poison else ok (vi32 (a + b)))
         | add_nsw \<Rightarrow> (if sov then ok poison else ok (vi32 (a + b)))
         | add_nuw_nsw \<Rightarrow>
               (if uov \<or> sov then ok poison else ok (vi32 (a + b)))
     )"
| "add_values wrap (vi64 a) (vi64 b) = (
      let uov = unsigned_overflow64 a b;
          sov = signed_overflow64 a b
      in case wrap of
           add_default \<Rightarrow> ok (vi64 (a + b))
         | add_nuw \<Rightarrow> (if uov then ok poison else ok (vi64 (a + b)))
         | add_nsw \<Rightarrow> (if sov then ok poison else ok (vi64 (a + b)))
         | add_nuw_nsw \<Rightarrow>
               (if uov \<or> sov then ok poison else ok (vi64 (a + b)))
     )"
| "add_values _ poison (vi32 _) = ok poison"
| "add_values _ (vi32 _) poison = ok poison"
| "add_values _ poison (vi64 _) = ok poison"
| "add_values _ (vi64 _) poison = ok poison"
| "add_values _ poison poison = ok poison"
| "add_values _ _ _ = err incompatible_types"


subsection "Compare instruction helpers"

fun compare_values_32 :: "llvm_compare_condition \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> llvm_value" where
  "compare_values_32 comp_eq a b = vi1 (a = b)"
| "compare_values_32 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_32 comp_ugt a b = vi1 ((uint a) > (uint b))"
| "compare_values_32 comp_uge a b = vi1 ((uint a) \<ge> (uint b))"
| "compare_values_32 comp_ult a b = vi1 ((uint a) < (uint b))"
| "compare_values_32 comp_ule a b = vi1 ((uint a) \<le> (uint b))"
| "compare_values_32 comp_sgt a b = vi1 ((sint a) > (sint b))"
| "compare_values_32 comp_sge a b = vi1 ((sint a) \<ge> (sint b))"
| "compare_values_32 comp_slt a b = vi1 ((sint a) < (sint b))"
| "compare_values_32 comp_sle a b = vi1 ((sint a) \<le> (sint b))"

fun compare_values_64 :: "llvm_compare_condition \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> llvm_value" where
  "compare_values_64 comp_eq a b = vi1 (a = b)"
| "compare_values_64 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_64 comp_ugt a b = vi1 ((uint a) > (uint b))"
| "compare_values_64 comp_uge a b = vi1 ((uint a) \<ge> (uint b))"
| "compare_values_64 comp_ult a b = vi1 ((uint a) < (uint b))"
| "compare_values_64 comp_ule a b = vi1 ((uint a) \<le> (uint b))"
| "compare_values_64 comp_sgt a b = vi1 ((sint a) > (sint b))"
| "compare_values_64 comp_sge a b = vi1 ((sint a) \<ge> (sint b))"
| "compare_values_64 comp_slt a b = vi1 ((sint a) < (sint b))"
| "compare_values_64 comp_sle a b = vi1 ((sint a) \<le> (sint b))"

(* TODO: support pointers *)
fun compare_values :: "llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values c (vi32 a) (vi32 b) = ok (compare_values_32 c a b)"
| "compare_values c (vi64 a) (vi64 b) = ok (compare_values_64 c a b)"
| "compare_values _ _ _ = err incompatible_types"

fun same_signs :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "same_signs a b = ((a \<ge> 0 \<and> b \<ge> 0) \<or> (a < 0 \<and> b < 0))"

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if same_signs (sint a) (sint b) then compare_values c (vi32 a) (vi32 b) else ok poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if same_signs (sint a) (sint b) then compare_values c (vi64 a) (vi64 b) else ok poison)"
| "compare_values_sign True c _ _ = err incompatible_types"


subsection "Phi instruction helpers"

fun phi_lookup :: "llvm_label option \<Rightarrow> (llvm_label * llvm_value_ref) list \<Rightarrow> llvm_value_ref result" where
  "phi_lookup l ls = do {
    previous \<leftarrow> some_or_err l phi_no_previous_block;
    some_or_err (map_of ls previous) phi_label_not_found
  }"


subsection "Instruction"


fun execute_instruction :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction \<Rightarrow> state result" where
  (* Allocate new memory value on the stack, and set the specified register to its address. *)
  "execute_instruction (r, s, h) _ (alloca name type align) =
    (do {
      (s', a) \<leftarrow> return (allocate_memory s);
      r' \<leftarrow> set_register r name (addr (saddr a));
      return (r', s', h)
    })"
  (* Read address from pointer and store value in the stack or the heap. *)
| "execute_instruction s _ (store type value pointer align) = do {
    s' \<leftarrow> store_value s value pointer;
    return s'
  }"
  (* Read address from pointer and load value from either the stack or the heap. *)
| "execute_instruction s _ (load register type pointer align) = do {
    s' \<leftarrow> load_value s register pointer;
    return s'
  }"
  (* Get values, add according to wrap option (or poison), and store in register. *)
| "execute_instruction (r, s, h) _ (add register wrap type v1 v2) = do {
    v1' \<leftarrow> get_value r v1;
    v2' \<leftarrow> get_value r v2;
    res \<leftarrow> add_values wrap v1' v2';
    r' \<leftarrow> set_register r register res;
    return (r', s, h)
  }"
  (* Get values, do comparison, and store in register. *)
| "execute_instruction (r, s, h) _ (icmp register same_sign cond type v1 v2) = do {
    v1' \<leftarrow> get_value r v1;
    v2' \<leftarrow> get_value r v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    r' \<leftarrow> set_register r register res;
    return (r', s, h)
  }"
  (* Check previous executed block, store proper value in register. *)
| "execute_instruction (r, s, h) p (phi register type values) = do {
    v \<leftarrow> phi_lookup p values;
    v' \<leftarrow> get_value r v;
    r' \<leftarrow> set_register r register v';
    return (r', s, h)
  }"

lemma "get_register r name = err unknown_register \<Longrightarrow> wp_never_err (execute_instruction (r,s,m) p (alloca name type align)) Q"
  apply (simp only: execute_instruction.simps(1))
  apply (intro wp_intro)
  using register_set_ok_unknown apply fast
  
  oops

lemma "abs_value s value = Some v \<Longrightarrow> abs_value s pr = Some (addr a) \<Longrightarrow> abs_memory s a \<noteq> None \<Longrightarrow>
    wp_never_err (execute_instruction s p (store type value pointer align))
    (\<lambda>x. (abs_value x = abs_value s \<and> abs_memory x = (abs_memory s)(a \<mapsto> Some v)))"
  apply (simp only: execute_instruction.simps(2))
  apply (intro wp_intro)
  by simp_all


subsection "Blocks and functions"

fun execute_block :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> (state * llvm_block_return) result" where
  "execute_block s previous (i#is, t) = do {
    s' \<leftarrow> execute_instruction s previous i;
    execute_block s' previous (is, t)
  }"
| "execute_block (r, s, h) previous (_, br_i1 v l1 l2) = do {
    val \<leftarrow> get_value r v;
    label \<leftarrow> (case val of (vi1 b) \<Rightarrow> ok (if b then l1 else l2) | _ \<Rightarrow> err incompatible_types);
    return ((r, s, h), branch_label label)
  }"
| "execute_block s previous (_, br_label l) = return (s, branch_label l)"
| "execute_block (r, s, h) previous (_, ret t v) = do {
    res \<leftarrow> get_value r v;
    return ((r, s, h), return_value res)
  }"

partial_function (tailrec) execute_blocks :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> llvm_labeled_blocks \<Rightarrow> (state * llvm_value option) result" where
  "execute_blocks state previous current block labeled_blocks =
    (case execute_block state previous block of
      err e \<Rightarrow> err e
    | ok (s', br) \<Rightarrow>
      (case br of
        return_value v \<Rightarrow> ok (s', Some v)
      | branch_label l \<Rightarrow>
        (case map_of labeled_blocks l of
          None \<Rightarrow> err unknown_label
        | Some b' \<Rightarrow> execute_blocks s' current (Some l) b' labeled_blocks
        )
      )
    )"

lemmas [code] = execute_blocks.simps

fun execute_function :: "state \<Rightarrow> llvm_function \<Rightarrow> (llvm_value option) result" where
  "execute_function s (func _ is ls) = do {
    (_, r) \<leftarrow> execute_blocks s None None is ls;
    return r
  }"

lemma "wp_never_err (do { (s, r) \<leftarrow> execute_block empty_state None ([], ret i32 (val (vi32 0))); return r}) (\<lambda>r. r = return_value (vi32 0))"
  unfolding empty_state_def
  by (simp add: get_value_def)

lemma block_return_iff[simp]: "wp_ignore_err (execute_block s p (instrs, final))
  (\<lambda>(s', r). case final of
    ret _ _ \<Rightarrow> (\<exists>v. r = return_value v)
  | br_i1 _ _ _ \<Rightarrow> (\<exists>l. r = branch_label l)
  | br_label l \<Rightarrow> r = branch_label l)"
  apply (cases "execute_block s p (instrs, final)"; simp)
  apply (induction instrs arbitrary: s; auto)
  by (cases final; auto)

end