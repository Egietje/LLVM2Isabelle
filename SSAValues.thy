theory SSAValues
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (vs,s,h) = memory_\<alpha> (vs',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma ssa_set_\<alpha>_update_eq[simp]:
  "ssa_set_\<alpha> (ssa (Mapping.update n v m) (insert n a), s, h) = (ssa_set_\<alpha> (ssa m a, s, h))(n := True)"
  by (auto simp: fun_eq_iff)

lemma ssa_\<alpha>_update_eq[simp]:
  "ssa_\<alpha> (ssa (Mapping.update n v m) (insert n a), s, h) = (ssa_\<alpha> (ssa m a, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x by (cases x; simp)
  done


section "Lemmas"

named_theorems ssa_value_intro

lemma wp_set_ssa_value_intro[THEN consequence, ssa_value_intro]:
  assumes "\<not>ssa_set_\<alpha> (vs,s,h) n"
  shows "wp (set_ssa_value vs n v) (\<lambda>vs'. ssa_set_\<alpha> (vs',s,h) = (ssa_set_\<alpha> (vs,s,h))(n := True) \<and> ssa_\<alpha> (vs',s,h) = (ssa_\<alpha> (vs,s,h))(ssa_val n := Some v) \<and> memory_\<alpha> (vs',s,h) = memory_\<alpha> (vs,s,h))"
  using assms
  by (cases vs; simp; intro wp_intro; simp)

lemma wp_set_ssa_intro[THEN consequence, wp_intro]:
  assumes "\<not>ssa_set_\<alpha> s n"
  shows "wp (set_ssa s n v) (\<lambda>s'. ssa_set_\<alpha> s' = (ssa_set_\<alpha> s)(n := True) \<and> ssa_\<alpha> s' = (ssa_\<alpha> s)(ssa_val n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding set_ssa_def
  using assms
  by (intro wp_intro ssa_value_intro wp_return_intro; simp)


lemma wp_reset_ssa_assigned_intro[THEN consequence, wp_intro]:
  shows "wp (return (reset_ssa_assigned s)) (\<lambda>s'. ssa_set_\<alpha> s' = (\<lambda>n. False) \<and> ssa_\<alpha> s' = ssa_\<alpha> s \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  apply (cases s; simp)
  apply (intro wp_intro wp_return_intro; auto; rule ext)
  subgoal for vs _ _ n by (cases vs; cases n; simp)
  subgoal for vs _ _ n by (cases vs; cases n; simp)
  subgoal for vs _ _ n by (cases vs; cases n; simp)
  done


lemma wp_get_ssa_value_intro[THEN consequence, ssa_value_intro]:
  assumes "ssa_\<alpha> (vs,s,h) (ssa_val n) = Some v"
  shows "wp (get_ssa_value vs n) (\<lambda>v'. v' = v)"
  using assms
  by (induction vs; simp; intro wp_intro; simp add: option.case_eq_if split: if_splits)

lemma wp_get_ssa_intro[THEN consequence, wp_intro]:
  assumes "ssa_\<alpha> s n = Some v"
  shows "wp (get_ssa s n) (\<lambda>v'. v' = v)"
  using assms
  by (cases s; cases n; simp; intro ssa_value_intro; simp)

end