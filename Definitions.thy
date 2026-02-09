theory Definitions
  imports "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.Mapping" "Result"
begin

section "LLVM AST"


subsection "Types and values"

datatype llvm_type = i1 | i32 | i64 | addr_type

type_synonym memory_model_address = nat
datatype llvm_address = saddr memory_model_address | haddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison

type_synonym llvm_register_name = string
type_synonym llvm_ssa_name = string

datatype llvm_value_ref = ssa_val llvm_ssa_name | val llvm_value

(* Should only have a memory address or memory address... *)
type_synonym llvm_pointer = llvm_value_ref

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

type_synonym llvm_labeled_blocks = "(llvm_label * llvm_instruction_block) list"

datatype llvm_block_return = return_value llvm_value
                           | branch_label llvm_label

datatype llvm_function_definition = func_def string llvm_type

datatype llvm_function = func llvm_function_definition llvm_instruction_block llvm_labeled_blocks

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm_program = program llvm_metadata "llvm_function list" llvm_attributes



section "Registers and Memory"


subsection "Definitions"

datatype ('n, 'v) ssa = ssa_bottom "('n, 'v) mapping" | ssa_layer "('n, 'v) mapping" "('n, 'v) ssa"
type_synonym llvm_ssa_model = "(llvm_ssa_name, llvm_value) ssa"

definition empty_ssa :: "('n, 'v) ssa" where
  "empty_ssa = ssa_bottom Mapping.empty"


datatype 'a memory_value = mem_unset | mem_val 'a | mem_freed
type_synonym 'a memory_model = "'a memory_value list"
type_synonym llvm_memory_model = "llvm_value memory_model"

definition empty_memory :: "'a memory_model" where
  "empty_memory = []"

type_synonym state = "llvm_ssa_model * llvm_memory_model * llvm_memory_model"

definition empty_state :: "state" where
  "empty_state = (empty_ssa, empty_memory, empty_memory)"


subsection "SSA-value operations"

fun get_ssa_value :: "('n, 'v) ssa \<Rightarrow> 'n \<Rightarrow> 'v result" where
  "get_ssa_value (ssa_bottom l) n = (case Mapping.lookup l n of None \<Rightarrow> err unknown_ssa_name | Some v \<Rightarrow> ok v)"
| "get_ssa_value (ssa_layer l ls) n = (case Mapping.lookup l n of None \<Rightarrow> get_ssa_value ls n | Some v \<Rightarrow> ok v)"

fun get_ssa :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_ssa _ (val v) = ok v"
| "get_ssa (l,s,h) (ssa_val n) = get_ssa_value l n"


fun set_ssa_value :: "('n, 'v) ssa \<Rightarrow> 'n \<Rightarrow> 'v \<Rightarrow> ('n, 'v) ssa result" where
  "set_ssa_value (ssa_bottom l) n v = (case Mapping.lookup l n of None \<Rightarrow> ok (ssa_bottom (Mapping.update n v l)) | Some _ \<Rightarrow> err ssa_override)"
| "set_ssa_value (ssa_layer l ls) n v = (case Mapping.lookup l n of None \<Rightarrow> ok (ssa_layer (Mapping.update n v l) ls) | Some _ \<Rightarrow> err ssa_override)"

definition set_ssa :: "state \<Rightarrow> llvm_ssa_name \<Rightarrow> llvm_value \<Rightarrow> state result" where
  "set_ssa s n v = do {
    (l,s,h) \<leftarrow> return s;
    l' \<leftarrow> set_ssa_value l n v;
    return (l',s,h)
  }"


definition new_ssa_value_layer :: "('n, 'v) ssa \<Rightarrow> ('n, 'v) ssa" where
  "new_ssa_value_layer l = ssa_layer Mapping.empty l"

fun new_ssa_layer :: "state \<Rightarrow> state" where
  "new_ssa_layer (l,s,h) = (new_ssa_value_layer l, s, h)"


subsection "Memory operations"

definition allocate_single_memory :: "'a memory_model \<Rightarrow> ('a memory_model * memory_model_address)" where
  "allocate_single_memory m = (m@[mem_unset], length m)"

definition allocate_stack :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_stack s = (case s of (r,s,h) \<Rightarrow> let (s', a) = allocate_single_memory s in ((r,s',h), saddr a))"

definition allocate_heap :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_heap s = (case s of (r,s,h) \<Rightarrow> let (h', a) = allocate_single_memory h in ((r,s,h'), haddr a))"


definition valid_single_memory_address :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_single_memory_address m a = (a < length m \<and> m!a \<noteq> mem_freed)"

fun valid_memory_address :: "state \<Rightarrow> llvm_address \<Rightarrow> bool" where
  "valid_memory_address (r,s,h) (haddr a) = valid_single_memory_address h a"
| "valid_memory_address (r,s,h) (saddr a) = valid_single_memory_address s a"


definition get_single_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a result" where
  "get_single_memory m a = do {
    assert unallocated_address (valid_single_memory_address m a);
    (case (m!a) of
      mem_unset \<Rightarrow> err uninitialized_address
    | mem_val v \<Rightarrow> ok v
    | mem_freed \<Rightarrow> err unallocated_address)
  }"

fun get_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "get_memory (r,s,h) (haddr a) = get_single_memory h a"
| "get_memory (r,s,h) (saddr a) = get_single_memory s a"


definition set_single_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a \<Rightarrow> 'a memory_model result" where
  "set_single_memory m a v = do {
    assert unallocated_address (valid_single_memory_address m a);
    return (m[a:=(mem_val v)])
  }"

fun set_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value \<Rightarrow> state result" where
  "set_memory (r,s,h) (haddr a) v = do {
    h' \<leftarrow> set_single_memory h a v;
    return (r,s,h')
  }"
| "set_memory (r,s,h) (saddr a) v = do {
    s' \<leftarrow> set_single_memory s a v;
    return (r,s',h)
  }"


definition free_single_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a memory_model result" where
  "free_single_memory m a = do {
    assert unallocated_address (valid_single_memory_address m a);
    return (m[a:=mem_freed])
  }"

fun free_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> state result" where
  "free_memory (r,s,h) (haddr a) = do {
    h' \<leftarrow> free_single_memory h a;
    return (r,s,h')
  }"
| "free_memory (r,s,h) (saddr a) = do {
    s' \<leftarrow> free_single_memory s a;
    return (r,s',h)
  }"


section "Abstractions"


subsection "Memory"

definition single_memory_\<alpha> where
  "single_memory_\<alpha> m a \<equiv> if valid_single_memory_address m a then 
    case m!a of 
      mem_val v \<Rightarrow> Some (Some v)
    | mem_unset \<Rightarrow> Some None
    | mem_freed \<Rightarrow> None
  else None"

fun memory_\<alpha> :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value option option" where
  "memory_\<alpha> (r,s,h) (saddr a) = single_memory_\<alpha> s a"
| "memory_\<alpha> (r,s,h) (haddr a) = single_memory_\<alpha> h a"


subsection "SSA"

fun ssa_\<alpha> :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "ssa_\<alpha> (r,s,h) (val v) = Some v"
| "ssa_\<alpha> (ssa_bottom l,s,h) (ssa_val n) = Mapping.lookup l n"
| "ssa_\<alpha> (ssa_layer l ls,s,h) (ssa_val n) = (case Mapping.lookup l n of None \<Rightarrow> ssa_\<alpha> (ls,s,h) (ssa_val n) | Some v \<Rightarrow> Some v)"

fun ssa_layer_\<alpha> :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "ssa_layer_\<alpha> (r,s,h) (val v) = Some v"
| "ssa_layer_\<alpha> (ssa_bottom l,s,h) (ssa_val n) = Mapping.lookup l n"
| "ssa_layer_\<alpha> (ssa_layer l ls,s,h) (ssa_val n) = Mapping.lookup l n"

end