theory Result
  imports "HOL-Library.Monad_Syntax"
begin

section "Definitions"


subsection "Types"

datatype error = unknown_ssa_name | ssa_override
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

definition wp_gen :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> (error \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp_gen m P E = (case m of ok v \<Rightarrow> P v | err e \<Rightarrow> E e)"

abbreviation "wlp m P \<equiv> wp_gen m P (\<lambda>x. True)"

abbreviation "wp m P \<equiv> wp_gen m P (\<lambda>x. False)"



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


subsection "Weakest precondition intro rules"

context
  notes wp_gen_def[simp]
begin
lemma consequence:
  assumes "wp_gen x Q E"
  assumes "\<And>x. Q x \<Longrightarrow> Q' x"
  assumes "\<And>e. E e \<Longrightarrow> E' e"
  shows "wp_gen x Q' E'"
  using assms
  by (simp split: result.splits)

lemma wp_ok_intro[wp_intro, simp]:
  assumes "Q x"
  shows "wp_gen (ok x) Q E"
  using assms
  by simp

lemma wp_err_intro[wp_intro, simp]:
  assumes "E e"
  shows "wp_gen (err e) Q E"
  using assms
  by simp

lemma wp_return_intro:
  assumes "Q x"
  shows "wp_gen (return x) Q E"
  using assms
  by (simp add: return_def)

lemma wp_assert_intro[wp_intro]:
  assumes "b \<Longrightarrow> wp_gen f P E"
  assumes "\<not>b \<Longrightarrow> E e"
  shows "wp_gen (do {assert e b; f}) P E"
  using assms
  by (auto split: result.splits simp: bind_def) 

lemma wp_bind_intro[wp_intro]:
  assumes "wp_gen m (\<lambda>x. wp_gen (f x) P E) E"
  shows "wp_gen (do {x\<leftarrow>m; f x}) P E"
  using assms
  by (cases m; simp add: bind_def)

lemma wp_case_option_intro[wp_intro]:
  assumes "(c = None \<and> wp_gen f P E) \<or> (\<exists>v. c = Some v \<and> wp_gen (g v) P E)"
  shows "wp_gen (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P E"
  using assms
  by auto

lemma wp_case_result_intro[wp_intro]:
  assumes "(\<exists>e. c = err e \<and> wp_gen (f e) P E) \<or> (\<exists>v. c = ok v \<and> wp_gen (g v) P E)"
  shows "wp_gen (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P E"
  using assms
  by auto

lemma wp_if_intro[wp_intro]:
  assumes "b \<Longrightarrow> wp_gen i Q E"
  assumes "\<not>b \<Longrightarrow> wp_gen e Q E"
  shows "wp_gen (if b then i else e) Q E"
  using assms
  by auto

lemma wp_case_product_intro[wp_intro]:
  assumes "\<And>b c. a = (b,c) \<Longrightarrow> wp_gen (f b c) Q E"
  shows "wp_gen (case a of (b,c) \<Rightarrow> f b c) Q E"
  using assms
  by (cases a; simp)

lemma wp_result_intro:
  assumes "\<And>x. f = ok x \<Longrightarrow> Q x"
  assumes "\<And>e. f = err e \<Longrightarrow> E e"
  shows "wp_gen f Q E"
  using assms
  by (cases f; simp)

end

end
