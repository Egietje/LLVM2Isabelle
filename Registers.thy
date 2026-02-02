theory Registers
  imports Definitions
begin

section "Lemmas"

lemma wp_set_register_intro[wp_intro]:
  assumes "get_register r n = err unknown_register"
  assumes "\<And>r'. set_register r n v = ok r' \<Longrightarrow> Q r'"
  shows "wp (set_register r n v) Q"
  using assms
  unfolding set_register_def get_register_def
  by (cases "Mapping.lookup r n"; simp)


lemma register_empty_get_unknown: "get_register empty_register_model n = err unknown_register"
  unfolding get_register_def empty_register_model_def
  by simp


lemma register_set_ok_unknown: "get_register r n = err unknown_register \<longleftrightarrow> (\<exists>r'. set_register r n v = ok r')"
  unfolding set_register_def get_register_def
  by (auto split: if_splits simp add: option.case_eq_if)


lemma register_set_independent_get: "n \<noteq> n' \<Longrightarrow> set_register r n' v' = ok r' \<Longrightarrow> get_register r n = get_register r' n"
  unfolding get_register_def set_register_def
  by (cases "Mapping.lookup r n'"; auto)

lemma register_set_independent_get_wlp: "n \<noteq> n' \<Longrightarrow> wlp (set_register r n' v) (\<lambda>r'. get_register r' n = get_register r n)"
  unfolding get_register_def set_register_def
  by (cases "Mapping.lookup r n'"; simp)


lemma register_set_get: "set_register r n v = ok r' \<Longrightarrow> get_register r' n = ok v"
  unfolding set_register_def get_register_def
  by (auto split: if_splits simp add: option.case_eq_if)

lemma register_set_get_wlp: "wlp (do { r' \<leftarrow> set_register r n v; get_register r n }) ((=) v)"
  unfolding set_register_def get_register_def
  apply (cases "Mapping.lookup r n"; simp)
  by (intro wp_intro; simp)


lemma register_get_override: "get_register r n = ok v \<Longrightarrow> set_register r n v' = err register_override"
  unfolding set_register_def get_register_def option.case_eq_if
  by (simp split: if_splits)

lemma register_get_override_wlp: "wlp (get_register r n) (\<lambda>_. set_register r n v = err register_override)"
  unfolding get_register_def set_register_def
  by (simp add: option.case_eq_if)


lemma register_set_override: "set_register r n v = ok r' \<Longrightarrow> set_register r' n v' = err register_override"
  unfolding set_register_def option.case_eq_if
  by (auto split: if_splits)

lemma register_set_override_wlp: "wlp (set_register r n v) (\<lambda>r'. set_register r' n v' = err register_override)"
  unfolding get_register_def set_register_def
  by (cases "Mapping.lookup r n"; simp)

end