theory SSAValues
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (l,s,h) = memory_\<alpha> (l',s,h)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done


lemma ssa_layer_\<alpha>_update_eq_bottom[simp]:
  "ssa_layer_\<alpha> (ssa_bottom (Mapping.update n v l), s, h) = (ssa_layer_\<alpha> (ssa_bottom l, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff)
  subgoal for x by (cases x; simp)
  done

lemma ssa_layer_\<alpha>_update_eq_layer[simp]:
  "ssa_layer_\<alpha> (ssa_layer (Mapping.update n v l) ls, s, h) = (ssa_layer_\<alpha> (ssa_layer l ls, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff)
  subgoal for x by (cases x; simp)
  done


lemma ssa_\<alpha>_update_eq_bottom[simp]:
  "ssa_\<alpha> (ssa_bottom (Mapping.update n v l), s, h) = (ssa_\<alpha> (ssa_bottom l, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff)
  subgoal for x by (cases x; simp)
  done

lemma ssa_\<alpha>_update_eq_layer[simp]:
  "ssa_\<alpha> (ssa_layer (Mapping.update n v l) ls, s, h) = (ssa_\<alpha> (ssa_layer l ls, s, h))(ssa_val n := Some v)"
  apply (auto simp: fun_eq_iff)
  subgoal for x by (cases x; simp)
  done


lemma ssa_layer_\<alpha>_implies_ssa_\<alpha>[simp]:
  "ssa_layer_\<alpha> (l,s,h) n = Some v \<Longrightarrow> ssa_\<alpha> (l,s,h) n = Some v"
  by (induction l; cases n; simp)


section "Lemmas"

named_theorems ssa_value_intro

lemma wp_set_ssa_value_intro[THEN consequence, ssa_value_intro]:
  assumes "ssa_layer_\<alpha> (l,s,h) (ssa_val n) = None"
  shows "wp (set_ssa_value l n v) (\<lambda>l'. ssa_layer_\<alpha> (l',s,h) = (ssa_layer_\<alpha> (l,s,h))(ssa_val n := Some v) \<and> ssa_\<alpha> (l',s,h) = (ssa_\<alpha> (l,s,h))(ssa_val n := Some v) \<and> memory_\<alpha> (l',s,h) = memory_\<alpha> (l,s,h))"
  using assms
  by (cases l; simp; intro wp_intro; simp)

lemma wp_set_ssa_intro[THEN consequence, wp_intro]:
  assumes "ssa_layer_\<alpha> s (ssa_val n) = None"
  shows "wp (set_ssa s n v) (\<lambda>s'. ssa_layer_\<alpha> s' = (ssa_layer_\<alpha> s)(ssa_val n := Some v) \<and> ssa_\<alpha> s' = (ssa_\<alpha> s)(ssa_val n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding set_ssa_def
  using assms
  by (intro wp_intro ssa_value_intro wp_return_intro; simp)


lemma wp_new_ssa_layer_intro[THEN consequence, wp_intro]:
  shows "wp (return (new_ssa_layer s)) (\<lambda>s'. ssa_layer_\<alpha> s' = (\<lambda>n. case n of val v \<Rightarrow> Some v | ssa_val _ \<Rightarrow> None) \<and> ssa_\<alpha> s' = ssa_\<alpha> s \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  apply (cases s; simp)
  apply (intro wp_intro wp_return_intro)
  unfolding new_ssa_value_layer_def
  apply (auto; rule ext)
  subgoal for _ _ _ n by (cases n; simp)
  subgoal for _ _ _ n by (cases n; simp)
  done


lemma wp_get_ssa_value_intro[THEN consequence, ssa_value_intro]:
  assumes "ssa_\<alpha> (l,s,h) (ssa_val n) = Some v"
  shows "wp (get_ssa_value l n) (\<lambda>v'. v' = v)"
  using assms
  by (induction l; simp; intro wp_intro; simp add: option.case_eq_if split: if_splits)

lemma wp_get_ssa_intro[THEN consequence, wp_intro]:
  assumes "ssa_\<alpha> s n = Some v"
  shows "wp (get_ssa s n) (\<lambda>v'. v' = v)"
  using assms
  by (cases s; cases n; simp; intro ssa_value_intro; simp)

end