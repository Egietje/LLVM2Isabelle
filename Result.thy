theory Result
  imports "HOL-Library.Monad_Syntax"
begin

section "Definitions"

ML \<open>
val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>rearranged\<close>
      (Scan.lift (Parse.$$$ "(" |-- Parse.enum1 "," Parse.nat --| Parse.$$$ ")")
        >> (fn ps =>
              Thm.rule_attribute [] (fn _ => Drule.rearrange_prems ps)))
      "rearrange theorem premises");
\<close>
subsection "Types"

datatype error = unknown_register_name | invalid_address | global_register_overwrite
  | not_an_address | incompatible_types | unknown_label
  | phi_no_previous_block | phi_label_not_found | phi_label_not_distinct
  | internal_error | unfreeable_memory | invalid_parameter_length | no_return_value

datatype 'a result = ok 'a | err error


subsection "Operations"

definition bind :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result" where
  "bind R f = (case R of err e \<Rightarrow> err e | ok x \<Rightarrow> f x)"

definition return :: "'a \<Rightarrow> 'a result" where
  "return x = ok x"

adhoc_overloading
  Monad_Syntax.bind==bind

fun assert where "assert e True = ok ()" | "assert e False = err e"

definition wp :: "'a result \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp m P = (case m of ok v \<Rightarrow> P v | err e \<Rightarrow> False)"




section "Lemmas"

named_theorems wp_intro

context
  notes bind_def[simp] return_def[simp]
begin


subsection "Monad laws"

lemma result_monad_left_identity[simp]: "do {x'\<leftarrow>return x; f x'} = f x"
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

lemma result_err_propagate[simp]: "do {x \<leftarrow> err e; f x} = err e"
  by auto

lemma result_let_in[simp]: "do { z \<leftarrow> (let x = y in (f x :: 'a result)); g z} = (let x = y in (do {z \<leftarrow> f x; g z }))"
  by simp

lemma wp_impl_ok[simp]:
  assumes "wp x Q"
  shows "\<exists>v. x = ok v"
  using assms
  unfolding wp_def
  by (cases x; simp)


end


subsection "Weakest precondition intro rules"

context
  notes wp_def[simp]
begin
lemma consequence:
  assumes "wp x Q"
  assumes "\<And>x. Q x \<Longrightarrow> Q' x"
  shows "wp x Q'"
  using assms
  by (simp split: result.splits)

lemma wp_ok_intro[wp_intro, simp]:
  assumes "Q x"
  shows "wp (ok x) Q"
  using assms
  by simp

lemma wp_return_intro:
  assumes "Q x"
  shows "wp (return x) Q"
  using assms
  by (simp add: return_def)

lemma wp_assert_intro[wp_intro]:
  assumes "b \<Longrightarrow> wp f P"
  assumes "\<not>b \<Longrightarrow> False"
  shows "wp (do {assert e b; f}) P"
  using assms
  by (auto split: result.splits simp: bind_def) 
thm wp_assert_intro

lemma wp_bind_intro[wp_intro]:
  assumes "wp m (\<lambda>x. wp (f x) P)"
  shows "wp (do {x\<leftarrow>m; f x}) P"
  using assms
  by (cases m; simp add: bind_def)

lemma wp_case_option_intro[wp_intro]:
  assumes "(c = None \<and> wp f P) \<or> (\<exists>v. c = Some v \<and> wp (g v) P)"
  shows "wp (case c of None \<Rightarrow> f | (Some v) \<Rightarrow> g v) P"
  using assms
  by auto

lemma wp_case_result_intro[wp_intro]:
  assumes "(\<exists>e. c = err e \<and> wp (f e) P) \<or> (\<exists>v. c = ok v \<and> wp (g v) P)"
  shows "wp (case c of err e \<Rightarrow> f e | ok v \<Rightarrow> g v) P"
  using assms
  by auto

lemma wp_if_intro[wp_intro]:
  assumes "b \<Longrightarrow> wp i Q"
  assumes "\<not>b \<Longrightarrow> wp e Q"
  shows "wp (if b then i else e) Q"
  using assms
  by auto

lemma wp_case_product_intro[wp_intro]:
  assumes "\<And>b c. a = (b,c) \<Longrightarrow> wp (f b c) Q"
  shows "wp (case a of (b,c) \<Rightarrow> f b c) Q"
  using assms
  by (cases a; simp)

lemma wp_result_intro:
  assumes "f = ok x" "Q x"
  shows "wp f Q"
  using assms
  by (cases f; simp)

end

end
