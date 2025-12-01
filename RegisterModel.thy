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

lemma register_empty_get_unknown: "get_register empty_register_model n = err unknown_register"
  unfolding get_register_def empty_register_model_def
  by simp

lemma register_set_ok_unknown: "set_register r n v = ok r' \<Longrightarrow> get_register r n = err unknown_register"
  unfolding set_register_def get_register_def option.case_eq_if
  by (simp split: if_splits)

lemma register_set_independent_get: "set_register r n' v' = ok r' \<Longrightarrow> n \<noteq> n' \<Longrightarrow> get_register r n = get_register r' n"
  unfolding get_register_def set_register_def option.case_eq_if
  by (cases "Mapping.lookup r n'"; auto)

lemma register_set_get: "set_register r n v = ok r' \<Longrightarrow> get_register r' n = ok v"
  using register_set_ok_unknown
  unfolding set_register_def get_register_def option.case_eq_if
  by (auto split: if_splits)

lemma register_get_ok_set: "get_register r n = ok v \<Longrightarrow> set_register r n v' = err register_override"
  unfolding set_register_def get_register_def option.case_eq_if
  by (simp split: if_splits)

lemma register_set_set: "set_register r n v = ok r' \<Longrightarrow> set_register r' n v' = err register_override"
  unfolding set_register_def option.case_eq_if
  by (auto split: if_splits)

end