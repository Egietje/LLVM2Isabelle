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

(*wp gen*)
definition wp :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (error \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp m P E = (case m of ok v \<Rightarrow> P v | err e \<Rightarrow> E e)"
(*wlp*)
definition wp_ignore_err :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp_ignore_err m P = wp m P (\<lambda>x. True)"
(*wp*)
definition wp_never_err :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp_never_err m P = wp m P (\<lambda>x. False)"
(* look into abbreviations *)

(* DISCUSS: Monadic if *)
definition ifM :: "bool result \<Rightarrow> 'a result \<Rightarrow> 'a result \<Rightarrow> 'a result" where
  "ifM p i e = do {b \<leftarrow> p; if b then i else e}"



section "Lemmas"

named_theorems wp_intro

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
  by (cases m; simp)

lemma result_bind_ok_unit[simp]: "do {ok (); f y} = do {f y}"
  by simp

lemma result_bind_err_iff[simp]: "do { x\<leftarrow>m; f x } = err e \<longleftrightarrow> (m = err e \<or> (\<exists>x. m = ok x \<and> f x = err e))"
  by (cases m; simp)

lemma result_return_ok_iff[simp]: "return x = ok y \<longleftrightarrow> x = y"
  by simp

lemma result_let_in[simp]: "do { z \<leftarrow> (let x = y in (f x :: 'a result)); g z} = (let x = y in (do {z \<leftarrow> f x; g z }))"
  by simp

end


subsection "Weakest precondition simps"

context
  notes wp_def[simp] wp_ignore_err_def[simp] wp_never_err_def[simp]
begin

lemma wp_ok_iff[simp]: "wp (ok v) P E \<longleftrightarrow> (P v)"
  by simp

lemma wp_ignore_err_ok_iff[simp]: "wp_ignore_err (ok v) P \<longleftrightarrow> (P v)"
  by simp

lemma wp_never_err_ok_iff[simp]: "wp_never_err (ok v) P \<longleftrightarrow> (P v)"
  by simp


lemma wp_err_iff[simp]: "wp (err e) P E \<longleftrightarrow> (E e)"
  by simp

lemma wp_ignore_err_err_iff[simp]: "wp_ignore_err (err e) P \<longleftrightarrow> True"
  by simp

lemma wp_never_err_err_iff[simp]: "wp_never_err (err e) P \<longleftrightarrow> False"
  by simp


lemma wp_return_iff[simp]: "wp (return x) P E \<longleftrightarrow> (P x)"
  unfolding return_def
  by simp

lemma wp_ignore_err_return_iff[simp]: "wp_ignore_err (return x) P \<longleftrightarrow> (P x)"
  unfolding return_def
  by simp

lemma wp_never_err_return_iff[simp]: "wp_never_err (return x) P \<longleftrightarrow> (P x)"
  unfolding return_def
  by auto
lemmas [wp_intro] = wp_never_err_return_iff[THEN iffD2]

(* wp x m; f x = wp m (wp f x) *)
lemma wp_bind_iff[simp]: "wp (do {x \<leftarrow> m; f x}) P E \<longleftrightarrow> ((\<exists>x. m = ok x \<and> (wp (f x) P E)) \<or> (\<exists>e. m = err e \<and> E e))"
  unfolding bind_def
  by (cases m; simp)

lemma wp_never_err_bind'[simp]: "wp_never_err (do {x\<leftarrow>m; f x}) P \<longleftrightarrow> (wp_never_err m (\<lambda>x. wp_never_err (f x) P))"
  unfolding bind_def
  by (cases m; simp)
lemmas [wp_intro] = wp_never_err_bind'[THEN iffD2]

lemma wp_ignore_err_bind_iff[simp]: "wp_ignore_err (do {x \<leftarrow> m; f x}) P \<longleftrightarrow> ((\<exists>x. m = ok x \<and> (wp_ignore_err (f x) P)) \<or> (\<exists>e. m = err e))"
  unfolding bind_def
  by (cases m; simp)

lemma wp_never_err_bind_iff[wp_intro]: "wp_never_err (do {x \<leftarrow> m; f x}) P \<longleftrightarrow> (\<exists>x. m = ok x \<and> (wp_never_err (f x) P))"
  unfolding bind_def
  by (cases m; simp)


lemma wp_case_option_iff[simp]: 
  "wp (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P E \<longleftrightarrow> 
    ((c = None \<and> wp f P E) \<or>
     (\<exists>v. c = Some v \<and> wp (g v) P E))"
  by (cases c; simp)

lemma wp_ignore_err_case_option_iff[simp]: 
  "wp_ignore_err (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P \<longleftrightarrow> 
    ((c = None \<and> wp_ignore_err f P) \<or>
     (\<exists>v. c = Some v \<and> wp_ignore_err (g v) P))"
  by (cases c; simp)

lemma wp_never_err_case_option_iff[simp]: 
  "wp_never_err (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P \<longleftrightarrow> 
    ((c = None \<and> wp_never_err f P) \<or>
     (\<exists>v. c = Some v \<and> wp_never_err (g v) P))"
  by (cases c; simp)
lemmas [wp_intro] = wp_never_err_case_option_iff[THEN iffD2]


lemma wp_case_result_iff[simp]: 
  "wp (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P E \<longleftrightarrow> 
    ((\<exists>e. c = err e \<and> wp (f e) P E) \<or>
     (\<exists>v. c = ok v \<and> wp (g v) P E))"
  by (cases c; simp)

lemma wp_ignore_err_case_result_iff[simp]: 
  "wp_ignore_err (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P \<longleftrightarrow> 
    ((\<exists>e. c = err e \<and> wp_ignore_err (f e) P) \<or>
     (\<exists>v. c = ok v \<and> wp_ignore_err (g v) P))"
  by (cases c; simp)

lemma wp_never_err_case_result_iff[simp]: 
  "wp_never_err (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P \<longleftrightarrow> 
    ((\<exists>e. c = err e \<and> wp_never_err (f e) P) \<or>
     (\<exists>v. c = ok v \<and> wp_never_err (g v) P))"
  by (cases c; simp)


lemma wp_never_err_if[wp_intro]:
  assumes "b \<Longrightarrow> wp_never_err i Q"
  assumes "\<not>b \<Longrightarrow> wp_never_err e Q"
  shows "wp_never_err (if b then i else e) Q"
  using assms by auto

lemma wp_never_err_product_case[wp_intro]:
  assumes "\<And>b c. a = (b,c) \<Longrightarrow> wp_never_err (f b c) Q"
  shows "wp_never_err (case a of (b,c) \<Rightarrow> f b c) Q"
  using assms apply (cases a) by simp

end





end