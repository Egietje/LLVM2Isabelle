theory LLVMState
  imports "LLVMAST" "RegisterModel" "MemoryModel"
begin

type_synonym state = "llvm_register_model * llvm_memory_model * llvm_memory_model"


section "Memory Abstraction for Proofs"

definition abs_memory where
  "abs_memory s a \<equiv> if valid_memory_address s a then 
    case s!a of 
      mem_val v \<Rightarrow> Some (Some v)
    | mem_unset \<Rightarrow> Some None
    | mem_freed \<Rightarrow> None
  else None"

fun memory_\<alpha> :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value option option" where
  "memory_\<alpha> (r,s,h) (saddr a) = abs_memory s a"
| "memory_\<alpha> (r,s,h) (haddr a) = abs_memory h a"


fun abs_memory_aux :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "abs_memory_aux (r,s,h) (saddr a) = get_memory s a"
| "abs_memory_aux (r,s,h) (haddr a) = get_memory h a"

definition memory_\<alpha>_old :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value option option" where
  "memory_\<alpha>_old s a = (case abs_memory_aux s a of
    ok v \<Rightarrow> Some (Some v)
  | err uninitialized_address \<Rightarrow> Some None
  | _ \<Rightarrow> None)"

lemma "memory_\<alpha>_old s a = memory_\<alpha> s a" 
  unfolding memory_\<alpha>_old_def 
  apply (cases a; cases s; auto split: option.splits result.splits simp: get_memory_def abs_memory_def)
     apply (auto split: memory_value.splits)
  done

definition abs_value :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "abs_value = undefined"

lemma wp_never_err_assert[wp_intro]:  "\<lbrakk> P; Q () \<rbrakk> \<Longrightarrow> wp (assert e P) Q"
  apply (cases P) apply auto done

lemma wp_get_memory[THEN consequence, wp_intro]: "abs_memory s a = Some (Some v) \<Longrightarrow> wp (get_memory s a) (\<lambda>r. r=v)"
  unfolding get_memory_def
  apply (intro wp_intro)
   apply (split memory_value.split)
   apply (auto simp: abs_memory_def split: if_splits)
  done

lemma wp_set_memory_update[THEN consequence, wp_intro]: "abs_memory s a \<noteq> None \<Longrightarrow> wp (set_memory s a v) (\<lambda>s'. abs_memory s' = (abs_memory s)(a := Some (Some v)))"
  unfolding set_memory_def
  apply (intro wp_intro)
  by (auto split: if_splits simp: valid_memory_address_def abs_memory_def)



(*
do the same for get/set
DO it for combined
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

thm wp_intro


lemma set_memory_abs:
  assumes "set_memory h a v = ok h'"
  shows "memory_\<alpha>_old (r, s, h') (haddr a) = Some (Some v)"
  using assms
  unfolding memory_\<alpha>_old_def set_memory_def apply simp
  unfolding valid_memory_address_def get_memory_def by auto

lemma abs_mem_ind:
  assumes "set_memory h a v = ok h'"
  shows "\<forall>a'. a' \<noteq> a \<longrightarrow> memory_\<alpha>_old (r,s,h) (haddr a') = memory_\<alpha>_old (r,s,h') (haddr a')"
  using assms
  unfolding memory_\<alpha>_old_def
  by (simp add: memory_set_independent_get)

lemma abs_mem_ind':
  assumes "set_memory h a v = ok h'"
  shows "\<forall>a'. a' \<noteq> a \<longrightarrow> ((memory_\<alpha>_old (r,s,h))((haddr a) := Some (Some v))) (haddr a') = memory_\<alpha>_old (r,s,h') (haddr a')"
  using assms abs_mem_ind
  by simp

lemma abs_mem_ind'':
  assumes "set_memory h a v = ok h'"
  shows "\<forall>a'. ((memory_\<alpha>_old (r,s,h))((haddr a) := Some (Some v))) (saddr a') = memory_\<alpha>_old (r,s,h') (saddr a')"
  using assms
  by (simp add: memory_\<alpha>_old_def)

lemma abs_memory_update_heap_forall:
  assumes "set_memory h a v = ok h'"
  shows "\<forall>a'. ((memory_\<alpha>_old (r, s, h))((haddr a) := Some (Some v))) a' = (memory_\<alpha>_old (r, s, h')) a'"
  using assms set_memory_abs abs_mem_ind' abs_mem_ind''
  apply auto
  subgoal for a'
    apply (cases a')
    by auto
  done

lemma abs_memory_update_heap:
  assumes "set_memory h a v = ok h'"
  shows "((memory_\<alpha>_old (r, s, h))((haddr a) := Some (Some v))) = (memory_\<alpha>_old (r, s, h'))"
  using assms abs_memory_update_heap_forall
  by auto

lemma store_value_abs:
  assumes "abs_value s vr = Some v"
  assumes "abs_value s pr = Some (addr a)"
  assumes "abs_memory s a \<noteq> None"
  shows "wp (store_value s vr p) (\<lambda>s'. abs_value s' = abs_value s \<and> abs_memory s' = (abs_memory s)(a := Some (Some v)))"
  oops

lemmas [wp_intro] = store_value_abs[THEN consequence]

definition empty_state :: "state" where
  "empty_state = (empty_register_model, empty_memory_model, empty_memory_model)"

definition get_value :: "llvm_register_model \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "get_value r v = (case v of (val va) \<Rightarrow> ok va | (reg re) \<Rightarrow> get_register r re)"

end