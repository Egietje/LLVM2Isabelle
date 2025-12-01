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
                          | ret llvm_type llvm_value_ref
                          | icmp llvm_register_name llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
                          | br_i1 llvm_value_ref llvm_label llvm_label
                          | br_label llvm_label
                          | phi llvm_register_name llvm_type "(llvm_value_ref * llvm_label) list"


subsection "Blocks, functions, programs"

type_synonym llvm_instruction_block = "llvm_instruction list"

type_synonym llvm_labeled_blocks = "(llvm_label, llvm_instruction_block) mapping"

datatype llvm_function_definition = func_def string llvm_type

datatype llvm_function = func llvm_function_definition llvm_instruction_block llvm_labeled_blocks

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm_program = program llvm_metadata "llvm_function list" llvm_attributes



section "Execution"


subsection "State"

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"

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


subsection "Instruction"

fun execute_instruction :: "state \<Rightarrow> llvm_instruction \<Rightarrow> (state * llvm_value option * llvm_label option) result" where
  (* Allocate new memory value on the stack, and set the specified register to its address. *)
  "execute_instruction (r, s, h) (alloca name type align) =
    (let (s', a) = allocate_memory s in do {
      r' \<leftarrow> set_register r name (addr (saddr a));
      return ((r', s', h), None, None)
    })"
  (* Read address from pointer and store value in the stack or the heap. *)
| "execute_instruction s (store type value pointer align) = do {
    s' \<leftarrow> store_value s value pointer;
    return (s', None, None)
  }"
  (* Read address from pointer and load value from either the stack or the heap. *)
| "execute_instruction s (load register type pointer align) = do {
    s' \<leftarrow> load_value s register pointer;
    return (s', None, None)
  }"
  (* Get values, add according to wrap option (or poison), and store in register. *)
| "execute_instruction (r, s, h) (add register wrap type v1 v2) = do {
    v1' \<leftarrow> get_value r v1;
    v2' \<leftarrow> get_value r v2;
    res \<leftarrow> add_values wrap v1' v2';
    r' \<leftarrow> set_register r register res;
    return ((r', s, h), None, None)
  }"
  (* Set the return value to the value of v. *)
| "execute_instruction (r, s, h) (ret t v) = do {
    res \<leftarrow> get_value r v;
    return ((r, s, h), Some res, None)
  }"
  (* Get values, do comparison, and store in register. *)
| "execute_instruction (r, s, h) (icmp register same_sign cond type v1 v2) = do {
    v1' \<leftarrow> get_value r v1;
    v2' \<leftarrow> get_value r v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    r' \<leftarrow> set_register r register res;
    return ((r', s, h), None, None)
  }"
  (* Return branch label as third return value. *)
| "execute_instruction (r, s, h) (br_i1 v l1 l2) = do {
    val \<leftarrow> get_value r v;
    label \<leftarrow> (case val of (vi1 b) \<Rightarrow> ok (if b then l1 else l2) | _ \<Rightarrow> err incompatible_types);
    return ((r, s, h), None, Some label)
  }"
| "execute_instruction s (br_label l) = ok (s, None, Some l)"
  (* Check previous executed block, store proper value in register. *)
| "execute_instruction (r, s, h) (phi register type values) = ok ((r, s, h), None, None)"

subsection "Block and function"

partial_function (tailrec) execute_block
  :: "state \<Rightarrow> llvm_instruction_block \<Rightarrow> llvm_labeled_blocks \<Rightarrow> (state * llvm_value option) result"
where
  "execute_block s is ls =
    (case is of
       [] \<Rightarrow> ok (s, None)
     | i # is' \<Rightarrow>
         (case execute_instruction s i of
            err e \<Rightarrow> err e
          | ok (s', r, l) \<Rightarrow>
              (case r of
                 Some v \<Rightarrow> ok (s', Some v)
               | None \<Rightarrow>
                   (case l of
                      None \<Rightarrow> execute_block s' is' ls
                    | Some label \<Rightarrow>
                        (case Mapping.lookup ls label of
                           None \<Rightarrow> err unknown_label
                         | Some is'' \<Rightarrow> execute_block s' is'' ls)))))"
(*  by auto
termination execute_block
  sorry (* TODO... although we cannot prove this since programs can loop forever... *)
(* But we do want this to generate code so we can evaluate things *)
*)

lemmas [code] = execute_block.simps


fun execute_function :: "state \<Rightarrow> llvm_function \<Rightarrow> (llvm_value option) result" where
  "execute_function s (func _ is ls) = do {
    (_, r) \<leftarrow> execute_block s is ls;
    return r
  }"



section "Test program"


definition bmain :: "llvm_instruction_block" where
  "bmain = [
    alloca ''%1'' i32 (Some 4),
    alloca ''%2'' i32 (Some 4),
    alloca ''%3'' i32 (Some 4),
    alloca ''%4'' i32 (Some 4),
    alloca ''%5'' i32 (Some 4),
    store i32 (val (vi32 0)) (ptr (reg ''%1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''%2'')) (Some 4),
    store i32 (val (vi32 2)) (ptr (reg ''%3'')) (Some 4),
    load ''%6'' i32 (ptr (reg ''%2'')) (Some 4),
    add ''%7'' add_nsw i32 (reg ''%6'') (val (vi32 1)),
    load ''%8'' i32 (ptr (reg ''%3'')) (Some 4),
    icmp ''%9'' False comp_eq i32 (reg ''%7'') (reg ''%8''),
    br_i1 (reg ''%9'') ''10'' ''12''
  ]"

definition b10 :: "llvm_instruction_block" where
  "b10 = [
    store i32 (val (vi32 3)) (ptr (reg ''%4'')) (Some 4),
    load ''%11'' i32 (ptr (reg ''%4'')) (Some 4),
    store i32 (reg ''%11'') (ptr (reg ''%3'')) (Some 4),
    br_label ''14''
  ]"

definition b12 :: "llvm_instruction_block" where
  "b12 = [
    store i32 (val (vi32 4)) (ptr (reg ''%5'')) (Some 4),
    load ''%13'' i32 (ptr (reg ''%5'')) (Some 4),
    store i32 (reg ''%13'') (ptr (reg ''%3'')) (Some 4),
    br_label ''14''
  ]"

definition b14 :: "llvm_instruction_block" where
  "b14 = [
    load ''%15'' i32 (ptr (reg ''%3'')) (Some 4),
    ret i32 (reg ''%15'')
  ]"

definition main :: "llvm_function" where
  "main = func (func_def ''main'' i32) bmain (Mapping.of_alist [(''10'', b10), (''12'', b12), (''14'', b14)])"(*
int main() {
    int y = 1;
    int x = y?1:0;
    return x;
}

define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  %5 = load i32, ptr %2, align 4
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %7, label %9

7:
  store i32 1, ptr %4, align 4
  %8 = load i32, ptr %4, align 4
  br label %10

9:
  br label %10

10:
  %11 = phi i32 [ %8, %9 ], [ 0, %9 ]
  store i32 %11, ptr %3, align 4
  %12 = load i32, ptr %3, align 4
  ret i32 %12
}
*)

value "execute_function (empty_register_model, empty_memory_model, empty_memory_model) main"


end