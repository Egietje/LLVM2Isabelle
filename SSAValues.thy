theory SSAValues
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (vs,s,h) = memory_\<alpha> (vs',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma ssa_\<alpha>_update_eq[simp]:
  "ssa_\<alpha> (Mapping.update n v vs, s, h) = (ssa_\<alpha> (vs, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x by (cases x; simp)
  done


section "Lemmas"

named_theorems ssa_value_intro

lemma wp_set_ssa_value_intro[THEN consequence, ssa_value_intro]:
  "wp (return (set_ssa_value vs n v,s,h)) (\<lambda>s'. ssa_\<alpha> s' = (ssa_\<alpha> (vs,s,h))(ssa_val n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> (vs,s,h))"
  unfolding set_ssa_value_def
  by (intro wp_intro wp_return_intro; simp)

lemma wp_set_ssa_intro[THEN consequence, wp_intro]:
  shows "wp (return (set_ssa s n v)) (\<lambda>s'. ssa_\<alpha> s' = (ssa_\<alpha> s)(ssa_val n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  by (cases s; simp; intro wp_intro ssa_value_intro; simp)


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