theory Registers
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (r,s,h) = memory_\<alpha> (r',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done


section "Lemmas"

named_theorems register_op_intro

lemma wp_set_register_op_intro[THEN consequence, register_op_intro]:
  "register_\<alpha> (r,s,h) (reg n) = None \<Longrightarrow> wp (set_register_op r n v) (\<lambda>r'. register_\<alpha> (r',s,h) = (register_\<alpha> (r,s,h))(reg n := Some v))"
  unfolding set_register_op_def
  apply (intro wp_intro; auto; intro wp_intro; rule ext)
  subgoal for n'
    by (cases n'; simp)
  done

lemma wp_set_register_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s (reg n) = None"
  shows "wp (set_register s n v) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding set_register_def
  using assms
  by (cases s; intro wp_intro register_op_intro wp_return_intro; simp)


lemma wp_get_register_op_intro[THEN consequence, register_op_intro]:
  assumes "register_\<alpha> (r,s,h) (reg n) = Some v"
  shows "wp (get_register_op r n) (\<lambda>v'. v' = v)"
  unfolding get_register_op_def
  using assms
  by (intro wp_intro; auto)

lemma wp_get_register_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s n = Some v"
  shows "wp (get_register s n) (\<lambda>v'. v' = v)"
  using assms
  by (cases s; cases n; simp; intro register_op_intro; simp)

end