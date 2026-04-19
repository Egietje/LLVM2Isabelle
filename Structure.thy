theory Structure
  imports Main "Word_Lib/Word_Names"
begin

type_synonym mem_addr = "nat"
datatype llvm_address = saddr mem_addr | haddr mem_addr (* stack or heap *)

instantiation llvm_address :: linorder
begin

fun less_eq_llvm_address where
  "less_eq_llvm_address (saddr a) (saddr b) \<longleftrightarrow> a \<le> b"
| "less_eq_llvm_address (haddr a) (haddr b) \<longleftrightarrow> a \<le> b"
| "less_eq_llvm_address (saddr _) (haddr _) \<longleftrightarrow> True"
| "less_eq_llvm_address (haddr _) (saddr _) \<longleftrightarrow> False"

fun less_llvm_address where
  "less_llvm_address (saddr a) (saddr b) \<longleftrightarrow> a < b"
| "less_llvm_address (haddr a) (haddr b) \<longleftrightarrow> a < b"
| "less_llvm_address (saddr _) (haddr _) \<longleftrightarrow> True"
| "less_llvm_address (haddr _) (saddr _) \<longleftrightarrow> False"

instance
  apply standard
  apply (auto elim: less_llvm_address.elims less_eq_llvm_address.elims)
  using less_eq_llvm_address.elims(3) apply fastforce
  subgoal for x y z by (cases x; cases y; cases z; simp)
  done

end

datatype llvm_type = i1 | i32 | i64 | ptr
datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | vptr llvm_address

datatype llvm_identifier = local_id string | global_id string (* models %id and @id *)

datatype llvm_value_reference = reg_val llvm_identifier | const_val llvm_value (* either a value in a register, or constant *)


datatype llvm_phi_instruction = phi llvm_identifier llvm_type "(llvm_value_reference * llvm_identifier) list"

type_synonym llvm_align = "nat option"

datatype llvm_add_no_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default
datatype llvm_icmp_cond = comp_eq | comp_ne
                        | comp_ugt | comp_uge | comp_ult | comp_ule
                        | comp_sgt | comp_sge | comp_slt | comp_sle
type_synonym llvm_icmp_ss = bool

datatype llvm_instruction = alloca llvm_identifier llvm_type "llvm_type * llvm_value option" llvm_align
                          | load llvm_identifier llvm_type llvm_value_reference llvm_align
                          | store llvm_type llvm_value_reference llvm_align
                          | add llvm_identifier llvm_add_no_wrap llvm_type llvm_value_reference llvm_value_reference
                          | icmp llvm_identifier llvm_icmp_ss llvm_icmp_cond llvm_type llvm_value_reference llvm_value_reference

datatype llvm_terminator_instruction = ret llvm_type llvm_value_reference
                                     | ret_void
                                     | br_label llvm_identifier
                                     | br_i1 llvm_value_reference llvm_identifier llvm_identifier
datatype llvm_block_terminator_result = branch_to llvm_identifier | return_val llvm_value | return_void

datatype llvm_basic_block = block llvm_identifier "llvm_phi_instruction list"  "llvm_instruction list" llvm_terminator_instruction

datatype llvm_function = func llvm_identifier llvm_type "llvm_basic_block list"

end