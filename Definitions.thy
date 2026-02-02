theory Definitions
  imports "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.Mapping" "Result"
begin

section "LLVM AST"


subsection "Types and values"

datatype llvm_type = i1 | i32 | i64 | saddr | maddr

type_synonym memory_model_address = nat
datatype llvm_address = saddr memory_model_address | haddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison

type_synonym llvm_register_name = string

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

type_synonym ('n, 'v) register_model = "('n, 'v) mapping"
type_synonym llvm_register_model = "(llvm_register_name, llvm_value) register_model"

definition empty_register_model :: "('n, 'v) register_model" where
  "empty_register_model = Mapping.empty"


datatype 'a memory_value = mem_unset | mem_val 'a | mem_freed
type_synonym 'a memory_model = "'a memory_value list"
type_synonym llvm_memory_model = "llvm_value memory_model"

definition empty_memory_model :: "'a memory_model" where
  "empty_memory_model = []"

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"

definition empty_state :: "state" where
  "empty_state = (empty_register_model, empty_memory_model, empty_memory_model)"


subsection "Register operations"

definition get_register :: "('n, 'v) register_model \<Rightarrow> 'n \<Rightarrow> 'v result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register | Some v \<Rightarrow> ok v)"

definition set_register :: "('n, 'v) register_model \<Rightarrow> 'n \<Rightarrow> 'v \<Rightarrow> ('n, 'v) register_model result" where
  "set_register r n v = (case Mapping.lookup r n of None \<Rightarrow> ok (Mapping.update n v r) | Some _ \<Rightarrow> err register_override)"


subsection "Memory operations"

definition allocate_memory :: "'a memory_model \<Rightarrow> ('a memory_model * memory_model_address)" where
  "allocate_memory m = (m@[mem_unset], length m)"

definition valid_memory_address :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_memory_address m a = (a < length m \<and> m!a \<noteq> mem_freed)"

definition get_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a result" where
  "get_memory m a = do {
    assert unallocated_address (valid_memory_address m a);
    (case (m!a) of
      mem_unset \<Rightarrow> err uninitialized_address
    | mem_val v \<Rightarrow> ok v
    | mem_freed \<Rightarrow> err unallocated_address)
  }"

definition set_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a \<Rightarrow> 'a memory_model result" where
  "set_memory m a v = do {
    assert unallocated_address (valid_memory_address m a);
    return (m[a:=(mem_val v)])
  }"

definition free_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a memory_model result" where
  "free_memory m a = do {
    assert unallocated_address (valid_memory_address m a);
    return (m[a:=mem_freed])
  }"



section "Abstractions"


subsection "Memory"

definition proof_single_memory where
  "proof_single_memory m a \<equiv> if valid_memory_address m a then 
    case m!a of 
      mem_val v \<Rightarrow> Some (Some v)
    | mem_unset \<Rightarrow> Some None
    | mem_freed \<Rightarrow> None
  else None"

fun proof_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value option option" where
  "proof_memory (r,s,h) (saddr a) = proof_single_memory s a"
| "proof_memory (r,s,h) (haddr a) = proof_single_memory h a"

definition abs_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "abs_value s v = (case v of (val va) \<Rightarrow> Some va | (reg re) \<Rightarrow> (case s of (r,_,_) \<Rightarrow> Mapping.lookup r re))"

definition get_value :: "llvm_register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"

end