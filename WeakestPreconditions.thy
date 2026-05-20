theory WeakestPreconditions
  imports "HOL-Library.Monad_Syntax"
begin

section "Definitions"
                   
fun assert where "assert True = Some ()" | "assert False = None"

definition wp :: "'a option \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wp m P = (case m of Some v \<Rightarrow> P v | None \<Rightarrow> False)"



section "Lemmas"

named_theorems wp_intro

subsection "Assert simps"

lemma assert_simps[simp]:            
  "assert P = Some x \<longleftrightarrow> P"
  "assert P = None \<longleftrightarrow> \<not>P"
  using assert.elims
  by auto


subsection "Intro rules"

context
  notes wp_def[simp]
begin

lemma consequence:
  assumes "wp x Q"
  assumes "\<And>x. Q x \<Longrightarrow> Q' x"
  shows "wp x Q'"
  using assms
  by (cases x; simp)


lemma wp_Some_intro[wp_intro, simp]:
  assumes "Q x"
  shows "wp (Some x) Q"
  using assms
  by simp

lemma wp_None_intro[wp_intro, simp]:
  shows "\<not>wp (None) Q"
  by simp


lemma wp_assert_intro[wp_intro]:
  assumes "b"
  assumes "b \<Longrightarrow> wp f P"
  shows "wp (do {assert b; f}) P"
  using assms
  by (cases b; simp)


lemma wp_bind_intro[wp_intro]:
  assumes "wp m (\<lambda>x. wp (f x) P)"
  shows "wp (do {x\<leftarrow>m; f x}) P"
  using assms
  by (cases m; simp add: bind_def)


lemma wp_case_option_intro[wp_intro]:
  assumes "c = None \<Longrightarrow> wp f P"
  assumes "\<And>v. c = Some v \<Longrightarrow> wp (g v) P"
  shows "wp (case c of None \<Rightarrow> f | Some v \<Rightarrow> g v) P"
  using assms
  by (cases c; simp)


lemma wp_if_intro[wp_intro]:
  assumes "b \<Longrightarrow> wp T Q"
  assumes "\<not>b \<Longrightarrow> wp F Q"
  shows "wp (if b then T else F) Q"
  using assms
  by auto

lemma wp_case_product_intro[wp_intro]:
  assumes "\<And>b c. a = (b,c) \<Longrightarrow> wp (f b c) Q"
  shows "wp (case a of (b,c) \<Rightarrow> f b c) Q"
  using assms
  by (cases a; simp)

lemma wp_option_intro:
  assumes "f \<noteq> None"
  assumes "\<And>x. f = Some x \<Longrightarrow> Q x"
  shows "wp f Q"
  using assms
  by auto

end

end
