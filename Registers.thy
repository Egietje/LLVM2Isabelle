theory Registers
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (r,s,h) = memory_\<alpha> (r',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma register_\<alpha>_update_eq[simp]:
  "register_\<alpha> (Mapping.update n v r, s, h) = (register_\<alpha> (r, s, h))(reg n := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x by (cases x; simp)
  done

lemma register_\<alpha>_val_eq[simp]:
  "register_\<alpha> s (val v) = Some v"
  by (cases s; simp)



section "register_\<alpha> operation"

lemma set_register_\<alpha>:
  "register_\<alpha> (set_register n v s) = (register_\<alpha> s)(reg n := Some v)"
  apply (cases s; rule ext)
  subgoal for r' s' h' x by (cases x; auto simp: set_register_value_def)
  done



section "Intro rules"

named_theorems register_intro

lemma wp_set_register_value_intro[THEN consequence, register_intro]:
  "wp (return (set_register_value n v r,s,h)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> (r,s,h))(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> (vs,s,h))"
  unfolding set_register_value_def
  by (intro wp_intro wp_return_intro; simp)

lemma wp_set_register_intro[THEN consequence, wp_intro]:
  shows "wp (return (set_register n v s)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  by (cases s; simp; intro wp_intro register_intro; simp)


lemma wp_get_register_intro[THEN consequence, wp_intro]:        
  assumes "register_\<alpha> s n \<noteq> None"
  shows "wp (get_register s n) (\<lambda>v'. register_\<alpha> s n = Some v')"
  using assms
  by (cases s; cases n; simp; intro wp_intro; auto)

end