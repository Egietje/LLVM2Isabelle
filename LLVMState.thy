theory LLVMState
  imports "LLVMAST" "RegisterModel" "MemoryModel"
begin

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"


section "Memory Abstraction for Proofs"

definition proof_single_memory where
  "proof_single_memory s a \<equiv> if valid_memory_address s a then 
    case s!a of 
      mem_val v \<Rightarrow> Some (Some v)
    | mem_unset \<Rightarrow> Some None
    | mem_freed \<Rightarrow> None
  else None"


                      
definition abs_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "abs_value = undefined"

lemma wp_get_memory_intro[wp_intro]:
  assumes "proof_single_memory s a = Some (Some x)"
  assumes "Q x"
  shows "wp (get_memory s a) Q"
  using assms
  unfolding get_memory_def proof_single_memory_def
  apply (intro wp_intro; cases "s!a"; auto)
  by (intro wp_intro; simp)

lemma wp_set_memory_update: "proof_single_memory s a \<noteq> None \<Longrightarrow> wp (set_memory s a v) (\<lambda>s'. proof_single_memory s' = (proof_single_memory s)(a := Some (Some v)))"
  unfolding set_memory_def
  apply (intro wp_intro)
  by (auto split: if_splits simp: valid_memory_address_def proof_single_memory_def)

lemma wp_set_memory_intro[wp_intro]:
  assumes "proof_single_memory s a \<noteq> None"
  assumes "\<And>s'. proof_single_memory s' = (proof_single_memory s)(a := Some (Some v)) \<Longrightarrow> Q s'"
  shows "wp (set_memory s a v) Q"
  using assms
  by (simp add: wp_set_memory_update[THEN consequence])

(*
Do it for combined memory model
Also for allocate, was free before, now not etc.

Have basic example for proof

arrays :'D

For related work:
Look at existing memory models
Hoare
Separation logic
Floyd's verification logic
Peter's papers
*)


definition empty_state :: "state" where
  "empty_state = (empty_register_model, empty_memory_model, empty_memory_model)"

definition get_value :: "llvm_register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"

end