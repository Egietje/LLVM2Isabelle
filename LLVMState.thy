theory LLVMState
  imports "LLVMAST" "RegisterModel" "MemoryModel"
begin

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"

definition abs_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value option option" where
  "abs_memory = undefined"

definition abs_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "abs_value = undefined"


lemma store_value_abs:
  assumes "abs_value s vr = Some v"
  assumes "abs_value s pr = Some (addr a)"
  assumes "abs_memory s a \<noteq> None"
  shows "wp_never_err (store_value s vr p) (\<lambda>s'. abs_value s' = abs_value s \<and> abs_memory s' = (abs_memory s)(a := Some (Some v)))"
  sorry

lemmas [wp_intro] = store_value_abs[THEN consequence]

definition empty_state :: "state" where
  "empty_state = (empty_register_model, empty_memory_model, empty_memory_model)"

definition get_value :: "llvm_register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"

end