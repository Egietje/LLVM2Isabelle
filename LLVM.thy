theory LLVM                                                                                          
  imports "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.AList_Mapping" "MemoryModel" "RegisterModel"
begin

section "AST"


subsection "Types and values"

datatype llvm_type = i1 | i32 | i64 | f32 | saddr | maddr

datatype llvm_address = saddr memory_model_address | haddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison

type_synonym llvm_memory_model = "llvm_value memory_model"
type_synonym llvm_register_name = string
type_synonym llvm_register_model = "(llvm_register_name, llvm_value) register_model"

datatype llvm_value_ref = reg llvm_register_name | val llvm_value

(* Should only have a memory address or memory address... *)
datatype llvm_pointer = ptr llvm_value_ref

type_synonym llvm_label = string


subsection "Instructions"

type_synonym llvm_align = int

datatype llvm_add_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default
datatype llvm_compare_condition = comp_eq | comp_ne
                                | comp_ugt | comp_uge | comp_ult | comp_ule
                                | comp_sgt | comp_sge | comp_slt | comp_sle
type_synonym llvm_same_sign = bool


datatype llvm_instruction = alloca llvm_register_name llvm_type "llvm_align option"
                          | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
                          | load llvm_register_name llvm_type llvm_pointer "llvm_align option"
                          | add llvm_register_name llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
                          | icmp llvm_register_name llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
                          | phi llvm_register_name llvm_type "(llvm_label * llvm_value_ref) list"

datatype llvm_terminator_instruction = ret llvm_type llvm_value_ref
                                     | br_i1 llvm_value_ref llvm_label llvm_label
                                     | br_label llvm_label


subsection "Blocks, functions, programs"

type_synonym llvm_instruction_block = "(llvm_instruction list * llvm_terminator_instruction)"

type_synonym llvm_labeled_blocks = "(llvm_label, llvm_instruction_block) mapping"

datatype llvm_block_return = return_value llvm_value
                           | branch_label llvm_label

datatype llvm_function_definition = func_def string llvm_type

datatype llvm_function = func llvm_function_definition llvm_instruction_block llvm_labeled_blocks

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm_program = program llvm_metadata "llvm_function list" llvm_attributes



section "Execution"


subsection "State"

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"

definition empty_state :: "state" where
  "empty_state = (empty_register_model, empty_memory_model, empty_memory_model)"

definition get_value :: "llvm_register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"


subsection "Store instruction helpers"

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


subsection "Load instruction helpers"

fun load_from_stack_or_heap :: "llvm_memory_model \<Rightarrow> llvm_memory_model \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "load_from_stack_or_heap s h (saddr a) = get_memory s a"
| "load_from_stack_or_heap s h (haddr a) = get_memory h a"

fun load_value :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "load_value (r, s, h) n (ptr p) = do {
    a \<leftarrow> get_value r p;
    ad \<leftarrow> (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address);
    v \<leftarrow> load_from_stack_or_heap s h ad;
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
    some_or_err (Mapping.lookup (Mapping.of_alist ls) previous) phi_label_not_found
  }"
(*TODO look into direct alist lookup*)


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
  apply simp apply (intro wp_intro) apply auto subgoal for s' a apply (cases "set_register r name
             (addr
               (llvm_address.saddr
 a))") using register_set_ok_unknown apply auto oops


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
        (case Mapping.lookup labeled_blocks l of
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