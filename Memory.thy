theory Memory
  imports Definitions
begin

section "Simps"

named_theorems proof_single_memory_simps

lemma proof_single_memory_some_some_iff[proof_single_memory_simps]:
  "proof_single_memory s a = Some (Some v) \<longleftrightarrow> valid_memory_address s a \<and> s!a = mem_val v"
  unfolding get_memory_def proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)

lemma proof_memory_some_some_iff_heap[simp]:
  "proof_memory (r,s,h) (haddr a) = Some (Some v) \<longleftrightarrow> valid_memory_address h a \<and> h!a = mem_val v"
  using proof_single_memory_some_some_iff
  by simp

lemma proof_single_memory_some_some_iff_stack[simp]:
  "proof_memory (r,s,h) (saddr a) = Some (Some v) \<longleftrightarrow> valid_memory_address s a \<and> s!a = mem_val v"
  using proof_single_memory_some_some_iff
  by simp


lemma proof_single_memory_update[proof_single_memory_simps]:
  assumes "proof_single_memory s a \<noteq> None"
  shows "proof_single_memory (s[a := mem_val v]) = (proof_single_memory s)(a := Some (Some v))"
  using assms
  unfolding proof_single_memory_def valid_memory_address_def
  by (auto split: if_splits)

lemma proof_memory_update_heap[simp]:
  assumes "proof_memory (r,s,h) (haddr a) \<noteq> None"
  shows "\<And>a'. proof_memory (r,s,h[a := mem_val v]) a' = ((proof_memory (r,s,h))((haddr a) := Some (Some v))) a'"
  subgoal for a'
  using assms proof_single_memory_update
  by (cases a'; fastforce)
  done

lemma proof_memory_update_stack[simp]:
  assumes "proof_memory (r,s,h) (saddr a) \<noteq> None"
  shows "\<And>a'. proof_memory (r,s[a := mem_val v],h) a' = ((proof_memory (r,s,h))((saddr a) := Some (Some v))) a'"
  subgoal for a'
  using assms proof_single_memory_update
  by (cases a'; fastforce)
  done


lemma proof_single_memory_none_iff[proof_single_memory_simps]:
  "\<not>valid_memory_address s a \<longleftrightarrow> proof_single_memory s a = None"
  unfolding proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)

lemma proof_memory_none_iff_heap[simp]:
  "\<not>valid_memory_address h a \<longleftrightarrow> proof_memory (r,s,h) (haddr a) = None"
  using proof_single_memory_none_iff by simp

lemma proof_memory_none_iff_stack[simp]:
  "\<not>valid_memory_address s a \<longleftrightarrow> proof_memory (r,s,h) (saddr a) = None"
  using proof_single_memory_none_iff by simp


lemma proof_single_memory_not_none_iff[proof_single_memory_simps]:
  "valid_memory_address s a \<longleftrightarrow> proof_single_memory s a \<noteq> None"
  unfolding proof_single_memory_def valid_memory_address_def
  by (cases "s!a"; simp)

lemma proof_memory_not_none_iff_heap[simp]:
  "valid_memory_address h a \<longleftrightarrow> proof_memory (r,s,h) (haddr a) \<noteq> None"
  using proof_single_memory_not_none_iff by simp

lemma proof_memory_not_none_iff_stack[simp]:
  "valid_memory_address s a \<longleftrightarrow> proof_memory (r,s,h) (saddr a) \<noteq> None"
  using proof_single_memory_not_none_iff by simp



section "Intro rules"

lemma wp_case_memory_value_intro[wp_intro]:
  assumes "x = mem_unset \<Longrightarrow> wp_gen f Q E"
  assumes "\<And>v. x = mem_val v \<Longrightarrow> wp_gen (g v) Q E"
  assumes "x = mem_freed \<Longrightarrow> wp_gen h Q E"
  shows "wp_gen (case x of mem_unset \<Rightarrow> f | mem_val v \<Rightarrow> g v | mem_freed \<Rightarrow> h) Q E"
  using assms
  by (cases x; simp)


lemma wp_get_memory_intro_single:
  assumes "proof_single_memory s a = Some (Some x)"
  assumes "Q x"
  shows "wp (get_memory s a) Q"
  using assms
  unfolding get_memory_def
  by (intro wp_intro; simp add: proof_single_memory_simps)

lemma wp_get_heap_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (haddr a) = Some (Some x)"
  assumes "Q x"
  shows "wp (get_memory h a) Q"
  using assms wp_get_memory_intro_single
  by simp

lemma wp_get_stack_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (saddr a) = Some (Some x)"
  assumes "Q x"
  shows "wp (get_memory s a) Q"
  using assms wp_get_memory_intro_single
  by simp


lemma wp_set_memory_intro_single:
  assumes "proof_single_memory s a \<noteq> None"
  assumes "\<And>s'. proof_single_memory s' = (proof_single_memory s)(a := Some (Some v)) \<Longrightarrow> Q s'"
  shows "wp (set_memory s a v) Q"
  using assms
  unfolding set_memory_def
  by (intro wp_intro; simp add: proof_single_memory_simps)

lemma wp_set_heap_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (haddr a) \<noteq> None"
  assumes "\<And>h'. proof_memory (r,s,h') = (proof_memory (r,s,h))((haddr a) := Some (Some v)) \<Longrightarrow> Q h'"
  shows "wp (set_memory h a v) Q"
  using assms
  unfolding set_memory_def
  apply (intro wp_intro; simp add: proof_single_memory_simps)
  using proof_memory_update_heap by fastforce

lemma wp_set_stack_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (saddr a) \<noteq> None"
  assumes "\<And>s'. proof_memory (r,s',h) = (proof_memory (r,s,h))((saddr a) := Some (Some v)) \<Longrightarrow> Q s'"
  shows "wp (set_memory s a v) Q"
  using assms
  unfolding set_memory_def
  apply (intro wp_intro; simp add: proof_single_memory_simps)
  using proof_memory_update_stack by fastforce


lemma wp_free_memory_intro_single:
  assumes "proof_single_memory s a \<noteq> None"
  assumes "\<And>s'. free_memory s a = ok s' \<Longrightarrow> Q s'"
  shows "wp (free_memory s a) Q"
  using assms
  unfolding free_memory_def
  by (intro wp_intro; simp add: proof_single_memory_simps)

lemma wp_free_heap_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (haddr a) \<noteq> None"
  assumes "\<And>h'. free_memory h a = ok h' \<Longrightarrow> Q h'"
  shows "wp (free_memory h a) Q"
  using assms wp_free_memory_intro_single
  by (simp; blast)

lemma wp_free_stack_intro[wp_intro]:
  assumes "proof_memory (r,s,h) (saddr a) \<noteq> None"
  assumes "\<And>s'. free_memory s a = ok s' \<Longrightarrow> Q s'"
  shows "wp (free_memory s a) Q"
  using assms wp_free_memory_intro_single
  by (simp; blast)


lemma wp_allocate_memory_intro_single:
  assumes "\<And>s' a. proof_single_memory s' a = Some None \<Longrightarrow> Q (s', a)"
  shows "wp (return (allocate_memory s)) Q"
  using assms
  unfolding allocate_memory_def
  apply (intro wp_intro)
  unfolding proof_single_memory_def valid_memory_address_def
  by simp

lemma wp_allocate_heap_intro[wp_intro]:
  assumes "\<And>h' a. proof_memory (r, s, h') (haddr a) = Some None \<Longrightarrow> Q (h', a)"
  shows "wp (return (allocate_memory h)) Q"
  using assms wp_allocate_memory_intro_single
  by auto

lemma wp_allocate_stack_intro[wp_intro]:
  assumes "\<And>s' a. proof_memory (r, s', h) (saddr a) = Some None \<Longrightarrow> Q (s', a)"
  shows "wp (return (allocate_memory s)) Q"
  using assms wp_allocate_memory_intro_single
  by auto



subsection "Simps"

lemma memory_set_ok_iff[simp]: "valid_memory_address m a \<longleftrightarrow> (\<exists>m'. set_memory m a v = ok m')"
  unfolding set_memory_def
  by simp

lemma memory_get_ok_iff[simp]: "valid_memory_address m a \<and> m!a \<noteq> mem_unset \<longleftrightarrow> (\<exists>v. get_memory m a = ok v)"
  unfolding get_memory_def valid_memory_address_def
  by (cases "m!a"; simp)


subsection "Empty"

lemma memory_empty_get: "get_memory empty_memory_model a = err unallocated_address"
  unfolding empty_memory_model_def get_memory_def valid_memory_address_def
  by simp

lemma memory_empty_invalid: "\<not>valid_memory_address empty_memory_model a"
  unfolding empty_memory_model_def valid_memory_address_def
  by simp

lemma memory_empty_set: "set_memory empty_memory_model a v = err unallocated_address"
  unfolding empty_memory_model_def set_memory_def valid_memory_address_def
  by simp


subsection "Allocate"

lemma memory_allocate_validity: "allocate_memory m = (m', i) \<Longrightarrow> \<not>valid_memory_address m i \<and> valid_memory_address m' i"
  unfolding allocate_memory_def valid_memory_address_def
  by auto

lemma memory_allocate_independent_valid[simp]: "allocate_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a \<longleftrightarrow> valid_memory_address m' a"
  unfolding valid_memory_address_def allocate_memory_def
  using nth_append_left
  by fastforce

lemma memory_allocate_independent_get: "allocate_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = get_memory m' a" 
  unfolding valid_memory_address_def allocate_memory_def get_memory_def
  using nth_append_left
  by (cases "a < a'"; fastforce)

lemma memory_allocate_get_uninitialized: "allocate_memory m = (m', a) \<Longrightarrow> get_memory m' a = err uninitialized_address"
  unfolding get_memory_def valid_memory_address_def allocate_memory_def
  by auto


subsection "Set"

lemma memory_set_invalid: "\<not>valid_memory_address m a \<Longrightarrow> set_memory m a v = err unallocated_address"
  unfolding set_memory_def
  by simp

lemma memory_set_ok_valid: "set_memory m a v = ok m' \<Longrightarrow> valid_memory_address m' a \<and> valid_memory_address m a"
  unfolding set_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_ok_valid_wlp: "wlp (set_memory m a v) (\<lambda> m'. valid_memory_address m' a \<and> valid_memory_address m a)"
  unfolding set_memory_def valid_memory_address_def
  by (intro wp_intro; simp)


lemma memory_set_override: "set_memory m i v = ok m' \<Longrightarrow> set_memory m' i v' = ok m'' \<Longrightarrow> get_memory m'' i = ok v'"
  unfolding set_memory_def get_memory_def valid_memory_address_def
  by auto

lemma memory_set_override_wlp:
  "wlp (do {
    m' \<leftarrow> set_memory m a v1;
    m'' \<leftarrow> set_memory m' a v2;
    get_memory m'' a}) (\<lambda>v. v = v2)"
  unfolding set_memory_def get_memory_def valid_memory_address_def
  by (intro wp_intro; simp)


lemma memory_set_identity: "get_memory m i = ok v \<Longrightarrow> set_memory m i v = ok m' \<Longrightarrow> m = m'"
  unfolding get_memory_def set_memory_def
  apply simp
  unfolding valid_memory_address_def
  apply (cases "m!i"; simp)
  using list_update_id
  by metis

lemma memory_set_identity_wlp: "wlp (do { v \<leftarrow> get_memory m a; set_memory m a v }) ((=) m)"
  unfolding get_memory_def set_memory_def valid_memory_address_def
  apply (intro wp_intro; simp)
  apply (cases "m!a"; simp)
  using list_update_id
  by metis


lemma memory_set_get: "set_memory m i v = ok m' \<Longrightarrow> get_memory m' i = ok v"
  unfolding set_memory_def get_memory_def valid_memory_address_def
  by auto

lemma memory_set_get_wlp: "wlp (do {m' \<leftarrow> set_memory m a v; get_memory m' a}) ((=) v)"
  unfolding set_memory_def get_memory_def valid_memory_address_def
  by (intro wp_intro; simp)


lemma memory_set_independent_get: "set_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = get_memory m' a"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_independent_get_wlp: "a \<noteq> a' \<Longrightarrow> wlp (set_memory m a' v) (\<lambda>m'. get_memory m' a = get_memory m a)"
  unfolding set_memory_def get_memory_def
  apply (intro wp_intro)
  apply simp
  unfolding valid_memory_address_def
  by auto


lemma memory_set_independent_valid: "set_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a = valid_memory_address m' a"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


subsection "Get"

lemma memory_get_ok_valid: "get_memory m a = ok v \<Longrightarrow> valid_memory_address m a"
  unfolding get_memory_def
  by simp


subsection "Free"

lemma memory_free_get: "free_memory m a = ok m' \<Longrightarrow> get_memory m' a = err unallocated_address"
  unfolding free_memory_def get_memory_def valid_memory_address_def
  by auto

lemma memory_free_set: "free_memory m a = ok m' \<Longrightarrow> set_memory m' a v = err unallocated_address"
  unfolding free_memory_def set_memory_def valid_memory_address_def
  by auto

lemma memory_free_invalid: "free_memory m a = ok m' \<Longrightarrow> \<not>valid_memory_address m' a \<and> valid_memory_address m a"
  unfolding free_memory_def valid_memory_address_def
  by auto

lemma memory_free_independent_valid: "free_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a \<longleftrightarrow> valid_memory_address m' a"
  unfolding free_memory_def valid_memory_address_def
  by auto

lemma memory_free_independent_get: "free_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = ok v \<longleftrightarrow> get_memory m' a = ok v"
  unfolding free_memory_def get_memory_def valid_memory_address_def
  by auto


end