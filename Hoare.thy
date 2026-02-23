theory Hoare
  imports "Blocks"
begin

section "Definitions"

definition hoare :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare P c Q \<equiv> (\<forall>x. P x \<longrightarrow> wp (c x) Q)"

definition state_marker :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" where
  "state_marker P \<equiv> P"


lemma hoare_intro:
  assumes "\<And>s. state_marker P s \<Longrightarrow> wp (c s) Q"
  shows "hoare P c Q"
  using assms
  unfolding hoare_def state_marker_def
  by simp

lemma hoare_elim:
  assumes "hoare P c Q" and "P s"
  shows "wp (c s) Q"
  using assms
  unfolding hoare_def
  by simp


lemma vcg:
  assumes "state_marker P s" and "hoare P c Q"
  shows "wp (c s) Q"
  using assms
  unfolding hoare_def state_marker_def
  by simp


lemma hoare_consequence:
  assumes assm: "hoare P c Q"
  assumes pre:  "\<And>s. P' s \<Longrightarrow> P s"
  assumes post: "\<And>s. Q s \<Longrightarrow> Q' s"
  shows "hoare P' c Q'"
  using assms consequence
  unfolding hoare_def
  by blast



section "Instructions specifications"

named_theorems hoare_specs

lemma alloca_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. s' = s)
    (execute_alloca n)
    (\<lambda>s'. \<exists>a. (register_\<alpha> s') = (register_\<alpha> s)(reg n := Some (addr a)) \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some None) \<and> memory_\<alpha> s a = None)"
  apply (rule hoare_intro)
  apply (rule alloca_wp_intro)
  by (auto simp: state_marker_def)

lemma store_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>a. s' = s \<and> register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a \<noteq> None \<and> register_\<alpha> s value \<noteq> None)
    (execute_store value pointer)
    (\<lambda>s'. \<exists>a v. register_\<alpha> s pointer = Some (addr a) \<and> register_\<alpha> s value = Some v \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (Some v)) \<and> register_\<alpha> s = register_\<alpha> s')"
  apply (rule hoare_intro)
  apply (rule store_wp_intro)
  by (auto simp: state_marker_def)

lemma load_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>a v. s' = s \<and> register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a = Some (Some v))
    (execute_load name pointer)
    (\<lambda>s'. \<exists>a v. register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a = Some (Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v))"
  apply (rule hoare_intro)
  apply (rule load_wp_intro)
  by (auto simp: state_marker_def)

lemma add32_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>v1' v2'. s' = s \<and> register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> add_no_poison32 wrap v1' v2')
    (execute_add name wrap v1 v2)
    (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi32 (v1' + v2'))))"
  apply (rule hoare_intro)
  apply (rule add32_wp_intro)
  by (auto simp: state_marker_def)

lemma add64_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>v1' v2'. s' = s \<and> register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> add_no_poison64 wrap v1' v2')
    (execute_add name wrap v1 v2)
    (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi64 (v1' + v2'))))"
  apply (rule hoare_intro)
  apply (rule add64_wp_intro)
  by (auto simp: state_marker_def)

lemma icmp32_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>v1' v2'. s' = s \<and> register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> (if ss then same_signs (sint v1') (sint v2') else True))
    (execute_icmp name ss cond v1 v2)
    (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_32 cond v1' v2')))"
  apply (rule hoare_intro)
  apply (rule wp_intro)
  by (auto simp: state_marker_def)

lemma icmp64_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>v1' v2'. s' = s \<and> register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> (if ss then same_signs (sint v1') (sint v2') else True))
    (execute_icmp name ss cond v1 v2)
    (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_64 cond v1' v2')))"
  apply (rule hoare_intro)
  apply (rule icmp64_wp_intro)
  by (auto simp: state_marker_def)


lemma phi_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>p' v v'. s' = s \<and> distinct (map fst values) \<and> p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v')
    (execute_phi p name values)
    (\<lambda>s'. \<exists>p' v v'. p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v' \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  apply (rule hoare_intro)
  apply (rule phi_wp_intro)
  apply (auto simp: state_marker_def)
  by blast

lemma [hoare_specs]: "hoare P (execute_alloca name) Q \<Longrightarrow> hoare P (execute_instruction (alloca name type align)) Q"
  unfolding hoare_def by simp
lemma [hoare_specs]: "hoare P (execute_store value pointer) Q \<Longrightarrow> hoare P (execute_instruction (store type value pointer align)) Q"
  unfolding hoare_def by simp
lemma [hoare_specs]: "hoare P (execute_load name pointer) Q \<Longrightarrow> hoare P (execute_instruction (load name type pointer align)) Q"
  unfolding hoare_def by simp
lemma [hoare_specs]: "hoare P (execute_add name wrap v1 v2) Q \<Longrightarrow> hoare P (execute_instruction (add name wrap type v1 v2)) Q"
  unfolding hoare_def by simp
lemma [hoare_specs]: "hoare P (execute_icmp name same_sign cond v1 v2) Q \<Longrightarrow> hoare P (execute_instruction (icmp name same_sign cond type v1 v2)) Q"
  unfolding hoare_def by simp




section "Block specifications"

lemma block_phi_spec':
  assumes "hoare ((\<lambda>s'. \<exists>p' v v'. p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v' \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)) (execute_block p (ps, is, t)) Q"
  shows "hoare (\<lambda>s'. \<exists>p' v v'. s' = s \<and> distinct (map fst values) \<and> p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v') (execute_block p ((phi name type values)#ps, is, t)) Q"
  apply (rule hoare_intro)
  apply (rule block_phi_wp_intro)
  apply (rule phi_wp_intro)
  using assms
  apply (auto simp: state_marker_def)
  apply blast
  unfolding hoare_def
  by blast

lemma block_phi_spec[hoare_specs]:
  assumes "hoare P (execute_phi p name values) x"
  assumes "hoare x (execute_block p (ps, is, t)) Q"
  shows "hoare P (execute_block p ((phi name type values)#ps, is, t)) Q"
  apply (rule hoare_intro)
  apply (rule wp_intro)
  using assms
  apply (auto simp: state_marker_def hoare_def consequence)
  by (smt (verit, best) assms(2) consequence hoare_def)

lemma block_instr_spec[hoare_specs]:
  assumes "hoare P (execute_instruction i) x"
  assumes "hoare x (execute_block p ([], is, t)) Q"
  shows "hoare P (execute_block p ([], i#is, t)) Q"
  apply (rule hoare_intro)
  apply (intro wp_intro)
  using assms
  apply (auto simp: state_marker_def hoare_def consequence)
  by (smt (verit, best) assms(2) consequence hoare_def)

lemma block_ret_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>v. s' = s \<and> register_\<alpha> s value = Some v)
    (execute_block p ([], [], ret type value))
    (\<lambda>(s', r). \<exists>v. s' = s \<and> register_\<alpha> s value = Some v \<and> r = return_value v)"
  apply (rule hoare_intro)
  apply (rule block_ret_wp_intro)
  by (auto simp: state_marker_def)

lemma block_br_label_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. s' = s)
    (execute_block p ([], [], br_label l))
    (\<lambda>(s', r). s' = s \<and> r = branch_label l)"
  apply (rule hoare_intro)
  apply (rule block_br_label_wp_intro)
  by (auto simp: state_marker_def)

lemma block_br_i1_spec[hoare_specs]:
  "hoare
    (\<lambda>s'. \<exists>b. s' = s \<and> register_\<alpha> s value = Some (vi1 b))
    (execute_block p ([], [], br_i1 value l1 l2))
    (\<lambda>(s', r). s' = s \<and> (\<exists>b. register_\<alpha> s value = Some (vi1 b) \<and> r = branch_label (if b then l1 else l2)))"
  apply (rule hoare_intro)
  apply (rule block_br_i1_wp_intro)
  by (auto simp: state_marker_def)

end