theory RegisterModel
  imports "HOL-Library.Mapping" Result
begin

section "Definitions"


subsection "Types"

type_synonym register_name = string
type_synonym 'a register_model = "(register_name, 'a) mapping"


subsection "Operations"

definition get_register :: "'a register_model \<Rightarrow> register_name \<Rightarrow> 'a result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register | Some v \<Rightarrow> ok v)"

definition set_register :: "'a register_model \<Rightarrow> register_name \<Rightarrow> 'a \<Rightarrow> 'a register_model result" where
  "set_register r n v = (case Mapping.lookup r n of None \<Rightarrow> ok (Mapping.update n v r) | Some _ \<Rightarrow> err register_override)"

definition empty_register_model :: "'a register_model" where
  "empty_register_model = Mapping.empty"



section "Lemmas"

lemma register_empty_get: "get_register empty_register_model n = err unknown_register"
  unfolding get_register_def empty_register_model_def
  by auto

lemma register_set_ok_unknown: "set_register r n v = ok r' \<longrightarrow> get_register r n = err unknown_register"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_get_set_get: "get_register r n = ok v \<longrightarrow> set_register r n' v' = ok r' \<longrightarrow> get_register r' n = ok v"
  unfolding get_register_def set_register_def option.case_eq_if
  using lookup_update' result.distinct(2) result.simps(1)
  by metis

lemma register_set_get: "set_register r n v = ok r' \<longrightarrow> get_register r' n = ok v"
  using register_set_ok_unknown
  unfolding set_register_def get_register_def option.case_eq_if
  by auto

lemma register_get_ok_set: "get_register r n = ok v \<longrightarrow> set_register r n v' = err register_override"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_set_set: "set_register r n v = ok r' \<longrightarrow> set_register r' n v' = err register_override"
  unfolding set_register_def option.case_eq_if
  by auto

end