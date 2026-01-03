theory RegisterModel
  imports "HOL-Library.Mapping" Result
begin

section "Definitions"


subsection "Types"

type_synonym ('n, 'v) register_model = "('n, 'v) mapping"


subsection "Operations"

definition get_register :: "('n, 'v) register_model \<Rightarrow> 'n \<Rightarrow> 'v result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register | Some v \<Rightarrow> ok v)"

definition set_register :: "('n, 'v) register_model \<Rightarrow> 'n \<Rightarrow> 'v \<Rightarrow> ('n, 'v) register_model result" where
  "set_register r n v = (case Mapping.lookup r n of None \<Rightarrow> ok (Mapping.update n v r) | Some _ \<Rightarrow> err register_override)"

definition empty_register_model :: "('n, 'v) register_model" where
  "empty_register_model = Mapping.empty"



section "Lemmas"

lemma set_register_intro[wp_intro]:
  assumes "get_register r name = err unknown_register"
  assumes "case set_register r name v of ok r' \<Rightarrow> wp_never_err (f r') Q | err e \<Rightarrow> False"
  shows "wp_never_err (set_register r name v) (\<lambda>r'. wp_never_err (f r') Q)"
  unfolding wp_never_err_def wp_def using assms apply (cases "set_register r name v") apply auto 
  by (simp add: wp_def wp_never_err_def)
                  
lemma register_empty_get_unknown: "get_register empty_register_model n = err unknown_register"
  unfolding get_register_def empty_register_model_def
  by simp


lemma register_set_ok_unknown: "get_register r n = err unknown_register \<longleftrightarrow> (\<exists>r'. set_register r n v = ok r')"
  unfolding set_register_def get_register_def
  by (auto split: if_splits simp add: option.case_eq_if)


lemma register_set_independent_get: "n \<noteq> n' \<Longrightarrow> set_register r n' v' = ok r' \<Longrightarrow> get_register r n = get_register r' n"
  unfolding get_register_def set_register_def
  by (cases "Mapping.lookup r n'"; auto)

lemma register_set_independent_get_wp: "n \<noteq> n' \<Longrightarrow> wp_ignore_err (set_register r n' v) (\<lambda>r'. get_register r' n = get_register r n)"
  unfolding get_register_def set_register_def
  by auto


lemma register_set_get: "set_register r n v = ok r' \<Longrightarrow> get_register r' n = ok v"
  unfolding set_register_def get_register_def
  by (auto split: if_splits simp add: option.case_eq_if)

lemma register_set_get_wp: "wp_ignore_err (do { r' \<leftarrow> set_register r n v; get_register r n }) ((=) v)"
  unfolding set_register_def get_register_def
  by (simp add: option.case_eq_if)


lemma register_get_override: "get_register r n = ok v \<Longrightarrow> set_register r n v' = err register_override"
  unfolding set_register_def get_register_def option.case_eq_if
  by (simp split: if_splits)

lemma register_get_override_wp: "wp_ignore_err (get_register r n) (\<lambda>_. set_register r n v = err register_override)"
  unfolding get_register_def set_register_def
  by auto


lemma register_set_override: "set_register r n v = ok r' \<Longrightarrow> set_register r' n v' = err register_override"
  unfolding set_register_def option.case_eq_if
  by (auto split: if_splits)

lemma register_set_override_wp: "wp_ignore_err (set_register r n v) (\<lambda>r'. set_register r' n v' = err register_override)"
  unfolding get_register_def set_register_def
  by auto

end