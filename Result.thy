theory Result
  imports "HOL-Library.Monad_Syntax"
begin

section "Definitions"


subsection "Types"

datatype error = unknown_register | uninitialized_register | register_override
  | unallocated_address | uninitialized_address
  | not_an_address | incompatible_types | unknown_label

datatype 'a result = ok 'a | err error


subsection "Operations"

definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind


fun assert where "assert e True = ok ()" | "assert e False = err e"



section "Lemmas"

declare bind_def[simp]
declare return_def[simp]

lemma result_monad_left_identity[simp]: "do {x'\<leftarrow>return x; f x'} = f x"
  by auto

lemma result_monad_right_identity[simp]: "do {x \<leftarrow> m; return x} = m"
  by (cases m; simp)

lemma result_monad_associative[simp]: "do {y \<leftarrow> do {x \<leftarrow> (m::'a result); f x}; g y} = do {x \<leftarrow> m; do {y \<leftarrow> f x; g y}}"
  by (cases m; simp)

lemma result_monad_associative'[simp]: "do {x \<leftarrow> (m::'a result); do {y \<leftarrow> f x; g y}} = do {x \<leftarrow> m; y \<leftarrow> f x; g y}"
  by simp

lemma assert_inv_simps[simp]: 
  "assert e P = ok x \<longleftrightarrow> P" 
  "assert e P = err e' \<longleftrightarrow> \<not>P \<and> e'=e"
  apply (cases P; simp)
  by (cases P; auto)

end