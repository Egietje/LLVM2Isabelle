theory LLVM
  imports Main "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.AList_Mapping" "HOL-Library.Monad_Syntax"
begin

find_consts "('k, 'a) Mapping.mapping \<Rightarrow> 'k \<Rightarrow> 'a option "
value "Mapping.ordered_entries (Mapping.empty :: (nat, nat) mapping)"

section "LLVM AST"

datatype llvm_type = i32 | i64 | f32 | saddr | maddr

type_synonym llvm_register_name = string
type_synonym memory_model_address = nat

datatype llvm_address = saddr memory_model_address | haddr memory_model_address

datatype llvm_value = vi32 word32 | vi64 word64 | addr llvm_address | poison | freed | unset

datatype llvm_value_ref = reg llvm_register_name | val llvm_value

(* Should only have a memory address or memory address... *)
datatype llvm_pointer = ptr llvm_value_ref

datatype llvm_function_definition = func_def string llvm_type

type_synonym llvm_align = int

datatype llvm_add_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default

datatype llvm_instruction
  = alloca llvm_register_name llvm_type "llvm_align option"
  | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
  | load llvm_register_name llvm_type llvm_pointer "llvm_align option"
  | add llvm_register_name llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
  | ret llvm_type llvm_value_ref

type_synonym llvm_instructions = "llvm_instruction list"

type_synonym llvm_labeled_instructions = "string \<Rightarrow> llvm_instructions option"

datatype llvm_function = func llvm_function_definition llvm_instructions llvm_labeled_instructions

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm = llvm llvm_metadata "llvm_function list" llvm_attributes



section "Execution"

subsection "Result monad"


datatype error = unknown_register | uninitialized_register | register_override
  | unallocated_address
  | uninitialized_stack_address | uninitialized_heap_address
  | not_an_address | incompatible_types

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


(* Execute a single instruction *)
fun execute_instruction :: "state \<Rightarrow> llvm_instruction \<Rightarrow> (state * llvm_value option) result" where
  (* Allocate new memory value, and set the specified register to its address. *)
  "execute_instruction (r, s, h) (alloca name type align) =
    (let (s', a) = allocate_memory s in do {
      r' \<leftarrow> set_register r name (addr (saddr a));
      return ((r', s', h), None)
    })"
  (* Read address from pointer and store value in either memory or memory. *)
| "execute_instruction s (store type value pointer align) = do {
    s' \<leftarrow> store_value s value pointer;
    return (s', None)
  }"
  (* Read address from pointer, and load value from either memory or memory. *)
| "execute_instruction s (load register type pointer align) = do {
    s' \<leftarrow> load_value s register pointer;
    return (s', None)
  }"
  (* Get values, add according to wrap option (or poison), and store in register. *)
| "execute_instruction (r, s, h) (add register wrap type v1 v2) = do {
  v1' \<leftarrow> get_value r v1;
  v2' \<leftarrow> get_value r v2;
  res \<leftarrow> add_values wrap v1' v2';
  r' \<leftarrow> set_register r register res;
  return ((r', s, h), None)
}"
  (* Set the return value to the value of v. *)
| "execute_instruction (r, s, m) (ret t v) = do {
  res \<leftarrow> get_value r v;
  return ((r,s,m), Some res)
}"


fun execute_instructions :: "state \<Rightarrow> llvm_instruction list \<Rightarrow> (state * llvm_value option) result" where
  "execute_instructions s [] = ok (s, None)" |
  "execute_instructions s (i#is) = do {
    (s', r) \<leftarrow> execute_instruction s i;
    res \<leftarrow> (case r of None \<Rightarrow> execute_instructions s' is | _ \<Rightarrow> return (s', r));
    return res
  }"

fun execute_function :: "state \<Rightarrow> llvm_function \<Rightarrow> (llvm_value option) result" where
  "execute_function v (func _ i _) = do {
    (_, r) \<leftarrow> execute_instructions v i;
    return r
  }"



definition main :: "llvm_function" where
  "main = func (func_def ''main'' i32) [
    alloca ''%1'' i32 (Some 4),
    alloca ''%2'' i32 (Some 4),
    alloca ''%3'' i32 (Some 4),
    alloca ''%4'' i32 (Some 4),
    store i32 (val (vi32 0)) (ptr (reg ''%1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''%2'')) (Some 4),
    store i32 (val (vi32 2)) (ptr (reg ''%3'')) (Some 4),
    store i32 (val (vi32 3)) (ptr (reg ''%3'')) (Some 4),
    load ''%5'' i32 (ptr (reg ''%2'')) (Some 4),
    load ''%6'' i32 (ptr (reg ''%3'')) (Some 4),
    add ''%7'' add_nuw i32 (reg ''%5'') (reg ''%6''),
    store i32 (reg ''%7'') (ptr (reg ''%4'')) (Some 4),
    load ''%8'' i32 (ptr (reg ''%4'')) (Some 4),
    ret i32 (reg ''%8'')
  ] (\<lambda>x. None)"


value "execute_function (empty_register_model, empty_memory_model, empty_memory_model) main"


end