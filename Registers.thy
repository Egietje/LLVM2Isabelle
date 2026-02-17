theory Registers
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (vs,s,h) = memory_\<alpha> (vs',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma register_\<alpha>_update_eq[simp]:
  "register_\<alpha> (Mapping.update n v vs, s, h) = (register_\<alpha> (vs, s, h))(reg n := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x by (cases x; simp)
  done

lemma register_\<alpha>_val_eq[simp]:
  "register_\<alpha> s (val v) = Some v"
  by (cases s; simp)


section "Lemmas"

named_theorems register_intro

lemma wp_set_register_value_intro[THEN consequence, register_intro]:
  "wp (return (set_register_value vs n v,s,h)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> (vs,s,h))(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> (vs,s,h))"
  unfolding set_register_value_def
  by (intro wp_intro wp_return_intro; simp)

lemma wp_set_register_intro[THEN consequence, wp_intro]:
  shows "wp (return (set_register s n v)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  by (cases s; simp; intro wp_intro register_intro; simp)


lemma wp_get_register_intro[THEN consequence, wp_intro]:        
  assumes "register_\<alpha> s n \<noteq> None"
  shows "wp (get_register s n) (\<lambda>v'. register_\<alpha> s n = Some v')"
  using assms
  by (cases s; cases n; simp; intro wp_intro; auto)

end