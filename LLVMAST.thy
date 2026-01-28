theory LLVMAST
  imports "MemoryModel" "RegisterModel" "Word_Lib/Word_64" "Word_Lib/Word_32"
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

type_synonym llvm_labeled_blocks = "(llvm_label * llvm_instruction_block) list"

datatype llvm_block_return = return_value llvm_value
                           | branch_label llvm_label

datatype llvm_function_definition = func_def string llvm_type

datatype llvm_function = func llvm_function_definition llvm_instruction_block llvm_labeled_blocks

datatype llvm_metadata = meta string string string

type_synonym llvm_attributes = "string list"

datatype llvm_program = program llvm_metadata "llvm_function list" llvm_attributes

end