theory LLVM
  imports Main "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.AList_Mapping" "HOL-Library.Monad_Syntax"
begin

find_consts "('k, 'a) Mapping.mapping \<Rightarrow> 'k \<Rightarrow> 'a option "
value "Mapping.ordered_entries (Mapping.empty :: (nat, nat) mapping)"

section "LLVM AST"

datatype llvm_type = i1 | i32 | i64 | f32 | saddr | maddr

type_synonym llvm_register_name = string
type_synonym memory_model_address = nat

datatype llvm_address = saddr memory_model_address | haddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison | freed | unset

datatype llvm_value_ref = reg llvm_register_name | val llvm_value

(* Should only have a memory address or memory address... *)
datatype llvm_pointer = ptr llvm_value_ref

datatype llvm_function_definition = func_def string llvm_type

type_synonym llvm_align = int

datatype llvm_add_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default
datatype llvm_compare_condition = comp_eq | comp_ne
                                | comp_ugt | comp_uge | comp_ult | comp_ule
                                | comp_sgt | comp_sge | comp_slt | comp_sle
type_synonym llvm_same_sign = bool

type_synonym llvm_label = string

datatype llvm_instruction = alloca llvm_register_name llvm_type "llvm_align option"
                          | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
                          | load llvm_register_name llvm_type llvm_pointer "llvm_align option"
                          | add llvm_register_name llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
                          | ret llvm_type llvm_value_ref
                          | icmp llvm_register_name llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
                          | br_i1 llvm_value_ref llvm_label llvm_label
                          | br_label llvm_label

type_synonym llvm_instructions = "llvm_instruction list"

type_synonym llvm_labeled_instructions = "llvm_label \<Rightarrow> llvm_instructions option"

datatype llvm_function = func llvm_function_definition llvm_instructions llvm_labeled_instructions

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm = llvm llvm_metadata "llvm_function list" llvm_attributes



section "Execution"

subsection "Result monad"


datatype error = unknown_register | uninitialized_register | register_override
  | unallocated_address
  | uninitialized_stack_address | uninitialized_heap_address
  | not_an_address | incompatible_types | unknown_label

datatype 'a result = ok 'a | err error


definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind



subsection "State"


type_synonym register_model = "(llvm_register_name, llvm_value) mapping"
type_synonym memory_model = "llvm_value list"
type_synonym state = "register_model * memory_model * memory_model"


(* Register model operations and lemmas *)
definition get_register :: "register_model \<Rightarrow> llvm_register_name \<Rightarrow> llvm_value result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register | Some v \<Rightarrow> ok v)"

definition set_register :: "register_model \<Rightarrow> llvm_register_name \<Rightarrow> llvm_value \<Rightarrow> register_model result" where
  "set_register r n v = (case Mapping.lookup r n of None \<Rightarrow> ok (Mapping.update n v r) | Some _ \<Rightarrow> err register_override)"

definition empty_register_model :: "register_model" where
  "empty_register_model = Mapping.empty"


lemma register_empty_get: "get_register empty_register_model n = err unknown_register"
  unfolding get_register_def empty_register_model_def
  by auto

lemma register_set_ok_unknown: "set_register r n v = ok r' \<longrightarrow> get_register r n = err unknown_register"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_get_set_get: "get_register r n = ok v \<longrightarrow> set_register r n' v' = ok r' \<longrightarrow> get_register r' n = ok v"
  unfolding get_register_def set_register_def option.case_eq_if
  using lookup_update' result.distinct(2) result.simps(1)
  by metis

lemma register_set_get: "set_register r n v = ok r' \<longrightarrow> get_register r' n = ok v"
  using register_set_ok_unknown
  unfolding set_register_def get_register_def option.case_eq_if
  by auto

lemma register_get_ok_set: "get_register r n = ok v \<longrightarrow> set_register r n v' = err register_override"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_set_set: "set_register r n v = ok r' \<longrightarrow> set_register r' n v' = err register_override"
  unfolding set_register_def option.case_eq_if
  by auto



definition get_value :: "register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"


(* Memory model operations and lemmas *)
definition allocate_memory :: "memory_model \<Rightarrow> (memory_model * memory_model_address)" where
  "allocate_memory s = (s@[unset], length s)"

definition valid_memory_address :: "memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_memory_address s a = (a < length s)"

definition get_memory :: "memory_model \<Rightarrow> memory_model_address \<Rightarrow> llvm_value result" where
  "get_memory s a = (if valid_memory_address s a then ok (s!a) else err unallocated_address)"

definition set_memory :: "memory_model \<Rightarrow> memory_model_address \<Rightarrow> llvm_value \<Rightarrow> memory_model result" where
  "set_memory s a v = (if valid_memory_address s a then ok (s[a:=v]) else err unallocated_address)"

definition empty_memory_model :: "memory_model" where
  "empty_memory_model = []"


lemma memory_empty_get: "get_memory empty_memory_model a = err unallocated_address"
  unfolding empty_memory_model_def get_memory_def valid_memory_address_def by simp

lemma memory_allocate_get_unset: "allocate_memory s = (s', i) \<longrightarrow> get_memory s' i = ok unset"
  using allocate_memory_def get_memory_def valid_memory_address_def by auto

lemma memory_allocate_invalid: "(s', i) = allocate_memory s \<longrightarrow> \<not>valid_memory_address s i"
  using allocate_memory_def valid_memory_address_def
  by simp

lemma memory_allocate_valid: "(s', i) = allocate_memory s \<longrightarrow> valid_memory_address s' i"
  using allocate_memory_def valid_memory_address_def
  by simp

lemma memory_valid_suc: "valid_memory_address s (Suc i) \<longrightarrow> valid_memory_address s i"
  using valid_memory_address_def
  by simp

lemma memory_set_unallocated: "\<not>valid_memory_address s i \<longrightarrow> set_memory s i v = err unallocated_address"
  unfolding set_memory_def
  by simp

lemma memory_set_ok_valid: "set_memory s i v = ok s' \<longrightarrow> valid_memory_address s' i \<and> valid_memory_address s i"
  unfolding set_memory_def valid_memory_address_def
  by auto

(* GET (PUT X) = X *)
lemma memory_set_get: "valid_memory_address s i \<longrightarrow> set_memory s i v = ok s' \<longrightarrow> get_memory s' i = ok v"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (PUT X) Y = Y*)
lemma memory_set_set_get: "valid_memory_address s i \<longrightarrow> set_memory s i v = ok s' \<longrightarrow> set_memory s' i v' = ok s'' \<longrightarrow> get_memory s'' i = ok v'"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (GET I) = ID*)
lemma memory_get_set_id: "valid_memory_address s i \<longrightarrow> get_memory s i = ok v \<longrightarrow> set_memory s i v = ok s' \<longrightarrow> s = s'"
  unfolding set_memory_def get_memory_def
  by auto

(*GET a1, PUT a2, GET a1*)
lemma memory_set_independent: "valid_memory_address s a1 \<longrightarrow> valid_memory_address s a2 \<longrightarrow> a1 \<noteq> a2 \<longrightarrow> get_memory s a1 = ok v1 \<longrightarrow> set_memory s a2 v2 = ok s' \<longrightarrow> get_memory s' a1 = ok v1"
  unfolding get_memory_def set_memory_def valid_memory_address_def
  by auto

(*VALID a1 \<rightarrow> ALLOC \<rightarrow> VALID a1*)
lemma memory_valid_alloc_valid: "valid_memory_address s a \<longrightarrow> allocate_memory s = (s', a') \<longrightarrow> valid_memory_address s' a"
  unfolding valid_memory_address_def allocate_memory_def
  by auto

(*VALID a1 \<rightarrow> GET a1 = (ALLOC, GET a1)*)
lemma memory_alloc_get_eq: "valid_memory_address s a \<longrightarrow> get_memory s a = ok v \<longrightarrow> allocate_memory s = (s', a') \<longrightarrow> get_memory s' a = ok v"
  unfolding get_memory_def allocate_memory_def valid_memory_address_def
  using nth_append_left
  by auto



subsection "Executors"

(* Store instruction helpers *)
fun store_to_stack_or_heap :: "register_model \<Rightarrow> memory_model \<Rightarrow> memory_model \<Rightarrow> llvm_address \<Rightarrow> llvm_value \<Rightarrow> state result" where
  "store_to_stack_or_heap r s h (saddr a) v = do {
    s' \<leftarrow> set_memory s a v;
    return (r, s', h)
  }"
| "store_to_stack_or_heap r s h (haddr a) v = do {
    h' \<leftarrow> set_memory h a v;
    return (r, s, h')
  }"

fun store_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "store_value (r, s, m) v (ptr p) = do {
    a \<leftarrow> get_value r p;
    ad \<leftarrow> (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address);
    val \<leftarrow> get_value r v;
    store_to_stack_or_heap r s m ad val
  }"

(* Load instruction helpers *)
fun load_from_stack_or_heap :: "memory_model \<Rightarrow> memory_model \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "load_from_stack_or_heap s h (saddr a) = do {
    val \<leftarrow> get_memory s a;
    res \<leftarrow> (case val of unset \<Rightarrow> err uninitialized_stack_address | v \<Rightarrow> ok v);
    return res
  }"
| "load_from_stack_or_heap s h (haddr a) = do {
    val \<leftarrow> get_memory h a;
    res \<leftarrow> (case val of unset \<Rightarrow> err uninitialized_stack_address | v \<Rightarrow> ok v);
    return res
  }"

fun load_value :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "load_value (r, s, h) n (ptr p) = do {
    a \<leftarrow> get_value r p;
    ad \<leftarrow> (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address);
    v \<leftarrow> load_from_stack_or_heap s h ad;
    r' \<leftarrow> set_register r n v;
    return (r', s, h)
  }"

(* Add instruction helpers *)
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

(* Compare instruction helpers *)
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

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if (sint a) \<ge> 0 \<and> (sint b) \<ge> 0 then compare_values c (vi32 a) (vi32 b) else ok poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if (sint a) \<ge> 0 \<and> (sint b) \<ge> 0 then compare_values c (vi64 a) (vi64 b) else ok poison)"
| "compare_values_sign True c _ _ = err incompatible_types"

(* Execute a single instruction *)
fun execute_instruction :: "state \<Rightarrow> llvm_instruction \<Rightarrow> (state * llvm_value option * llvm_label option) result" where
  (* Allocate new memory value, and set the specified register to its address. *)
  "execute_instruction (r, s, h) (alloca name type align) =
    (let (s', a) = allocate_memory s in do {
      r' \<leftarrow> set_register r name (addr (saddr a));
      return ((r', s', h), None, None)
    })"
  (* Read address from pointer and store value in either memory or memory. *)
| "execute_instruction s (store type value pointer align) = do {
    s' \<leftarrow> store_value s value pointer;
    return (s', None, None)
  }"
  (* Read address from pointer, and load value from either memory or memory. *)
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

function execute_instructions
  :: "state \<Rightarrow> llvm_instructions \<Rightarrow> llvm_labeled_instructions \<Rightarrow> (state * llvm_value option) result"
where
  "execute_instructions s is ls =
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
                      None \<Rightarrow> execute_instructions s' is' ls
                    | Some label \<Rightarrow>
                        (case ls label of
                           None \<Rightarrow> err unknown_label
                         | Some is'' \<Rightarrow> execute_instructions s' is'' ls)))))"
  by auto
termination execute_instructions
  sorry (* TODO... although we cannot prove this since programs can loop forever... *)

fun execute_function :: "state \<Rightarrow> llvm_function \<Rightarrow> (llvm_value option) result" where
  "execute_function s (func _ is ls) = do {
    (_, r) \<leftarrow> execute_instructions s is ls;
    return r
  }"



definition b10 :: "llvm_instructions" where
  "b10 = [
    store i32 (val (vi32 3)) (ptr (reg ''%4'')) (Some 4),
    load ''%11'' i32 (ptr (reg ''%4'')) (Some 4),
    store i32 (reg ''%11'') (ptr (reg ''%3'')) (Some 4),
    br_label ''14''
  ]"

definition b12 :: "llvm_instructions" where
  "b12 = [
    store i32 (val (vi32 4)) (ptr (reg ''%5'')) (Some 4),
    load ''%13'' i32 (ptr (reg ''%5'')) (Some 4),
    store i32 (reg ''%13'') (ptr (reg ''%3'')) (Some 4),
    br_label ''14''
  ]"

definition b14 :: "llvm_instructions" where
  "b14 = [
    load ''%15'' i32 (ptr (reg ''%3'')) (Some 4),
    ret i32 (reg ''%15'')
  ]"

definition main :: "llvm_function" where
  "main = func (func_def ''main'' i32) [
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
  ] (\<lambda>x. (case x of ''10'' \<Rightarrow> Some b10 | ''12'' \<Rightarrow> Some b12 | ''14'' \<Rightarrow> Some b14 | _ \<Rightarrow> None))"
(*
int main() {
    int x = 1;
    int y = 2;
    if (x + 1 == y) {
        int z = 3;
        y = z;
    } else {
        int z = 4;
        y = z;
    }
    return y;
}

define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  store i32 2, ptr %3, align 4
  %6 = load i32, ptr %2, align 4
  %7 = add nsw i32 %6, 1
  %8 = load i32, ptr %3, align 4
  %9 = icmp eq i32 %7, %8
  br i1 %9, label %10, label %12

10:
  store i32 3, ptr %4, align 4
  %11 = load i32, ptr %4, align 4
  store i32 %11, ptr %3, align 4
  br label %14

12:
  store i32 4, ptr %5, align 4
  %13 = load i32, ptr %5, align 4
  store i32 %13, ptr %3, align 4
  br label %14

14:
  %15 = load i32, ptr %3, align 4
  ret i32 %15
}
*)

value "execute_function (empty_register_model, empty_memory_model, empty_memory_model) main"


end