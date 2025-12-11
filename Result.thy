theory Result
  imports "HOL-Library.Monad_Syntax"
begin

section "Definitions"


subsection "Types"

datatype error = unknown_register | uninitialized_register | register_override
  | unallocated_address | uninitialized_address
  | not_an_address | incompatible_types | unknown_label
  | phi_no_previous_block | phi_label_not_found

datatype 'a result = ok 'a | err error


subsection "Operations"

definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind

fun assert where "assert e True = ok ()" | "assert e False = err e"

fun some_or_err :: "'a option \<Rightarrow> error \<Rightarrow> 'a result" where
  "some_or_err (Some v) _ = ok v"
| "some_or_err None e = err e"

definition wp :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (error \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp m P E = (case m of ok v \<Rightarrow> P v | err e \<Rightarrow> E e)"

definition wp_ok :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp_ok m P = wp m P (\<lambda>x. True)"



section "Lemmas"

context
  notes bind_def[simp] return_def[simp]
begin


subsection "Monad laws"

lemma result_monad_left_identity[simp]: "do {x'\<leftarrow>return x; f x'} = f x"
  by auto

lemma result_err_propagate[simp]: "do {x \<leftarrow> err e; f x} = err e"
  by auto

lemma result_monad_right_identity[simp]: "do {x \<leftarrow> m; return x} = m"
  by (cases m; simp)

lemma result_monad_associative[simp]: "do {y \<leftarrow> do {x \<leftarrow> (m::'a result); f x}; g y} = do {x \<leftarrow> m; do {y \<leftarrow> f x; g y}}"
  by (cases m; simp)


subsection "Assert simps"

lemma assert_ok_iff[simp]: "assert e P = ok x \<longleftrightarrow> P"
  by (cases P; simp)

lemma assert_err_iff[simp]: "assert e P = err e' \<longleftrightarrow> \<not>P \<and> e'=e"
  by (cases P; auto)


subsection "Result simps"

lemma result_bind_ok_iff[simp]: "do { x\<leftarrow>m; f x } = ok v \<longleftrightarrow> (\<exists>x. m = ok x \<and> f x = ok v)"
  unfolding bind_def
  by (cases m; simp)

lemma result_bind_ok_unit[simp]: "do {ok (); f y} = do {f y}"
  unfolding bind_def
  by simp

lemma result_bind_err_iff[simp]: "do { x\<leftarrow>m; f x } = err e \<longleftrightarrow> (m = err e \<or> (\<exists>x. m = ok x \<and> f x = err e))"
  unfolding bind_def
  by (cases m; simp)

lemma result_return_ok_iff[simp]: "return x = ok y \<longleftrightarrow> x = y"
  unfolding return_def
  by simp

end


subsection "Weakest precondition simps"

lemma wp_ok_iff[simp]: "wp (ok v) P E \<longleftrightarrow> (P v)"
  unfolding wp_def
  by simp

lemma wp_ok_ok_iff[simp]: "wp_ok (ok v) P \<longleftrightarrow> (P v)"
  unfolding wp_ok_def
  by simp

lemma wp_err_iff[simp]: "wp (err e) P E \<longleftrightarrow> (E e)"
  unfolding wp_def
  by simp

lemma wp_ok_err_iff[simp]: "wp_ok (err e) P \<longleftrightarrow> True"
  unfolding wp_ok_def
  by simp

lemma wp_return_iff[simp]: "wp (return x) P E \<longleftrightarrow> (P x)"
  unfolding return_def wp_def
  by simp

lemma wp_ok_return_iff[simp]: "wp_ok (return x) P \<longleftrightarrow> (P x)"
  unfolding wp_ok_def
  by simp

lemma wp_bind_iff[simp]: "wp (do {x \<leftarrow> m; f x}) P E \<longleftrightarrow> ((\<exists>x. m = ok x \<and> (wp (f x) P E)) \<or> (\<exists>e. m = err e \<and> E e))"
  unfolding wp_def bind_def
  by (cases m; simp)

lemma wp_ok_bind_iff[simp]: "wp_ok (do {x \<leftarrow> m; f x}) P \<longleftrightarrow> ((\<exists>x. m = ok x \<and> (wp_ok (f x) P)) \<or> (\<exists>e. m = err e))"
  unfolding wp_ok_def
  by simp


(* TODO: MONADIC IF *)

end