theory LLVMState
  imports "LLVMAST" "RegisterModel" "MemoryModel"
begin

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"


section "Memory Abstraction for Proofs"

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
  "abs_value = undefined"

lemma proof_single_memory_some_some_iff[simp]:
  "proof_single_memory s a = Some (Some v) \<longleftrightarrow> valid_memory_address s a \<and> s!a = mem_val v"
  unfolding get_memory_def proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)

lemma proof_single_memory_update[simp]:
  assumes "proof_single_memory s a \<noteq> None"
  shows "proof_single_memory (s[a := mem_val v]) = (proof_single_memory s)(a := Some (Some v))"
  using assms
  unfolding proof_single_memory_def valid_memory_address_def
  by (auto split: if_splits)

lemma proof_single_memory_none_iff[simp]:
  "\<not>valid_memory_address s a \<longleftrightarrow> proof_single_memory s a = None"
  unfolding proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)

lemma proof_single_memory_not_none_iff[simp]:
  "valid_memory_address s a \<longleftrightarrow> proof_single_memory s a \<noteq> None"
  unfolding proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)


lemma wp_get_memory_intro[wp_intro]:
  assumes "proof_single_memory s a = Some (Some x)"
  assumes "Q x"
  shows "wp (get_memory s a) Q"
  using assms
  unfolding get_memory_def
  by (intro wp_intro; simp)

lemma wp_set_memory_intro[wp_intro]:
  assumes "proof_single_memory s a \<noteq> None"
  assumes "\<And>s'. proof_single_memory s' = (proof_single_memory s)(a := Some (Some v)) \<Longrightarrow> Q s'"
  shows "wp (set_memory s a v) Q"
  using assms
  unfolding set_memory_def
  by (intro wp_intro; simp)

lemma wp_free_memory_intro[wp_intro]:
  assumes "proof_single_memory s a \<noteq> None"
  assumes "\<And>s'. free_memory s a = ok s' \<Longrightarrow> Q s'"
  shows "wp (free_memory s a) Q"
  using assms
  unfolding free_memory_def
  by (intro wp_intro; simp)

lemma wp_allocate_memory_intro[wp_intro]:
  assumes "\<And>s' a. proof_single_memory s' a = Some None \<Longrightarrow> Q (s', a)"
  shows "wp (return (allocate_memory s)) Q"
  using assms
  unfolding allocate_memory_def
  apply (intro wp_intro)
  unfolding proof_single_memory_def valid_memory_address_def
  by simp


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