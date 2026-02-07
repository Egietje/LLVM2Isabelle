theory Memory    
  imports Definitions
begin

section "Simps"

named_theorems single_memory_simps
named_theorems single_memory_intro

lemma register_\<alpha>_eq[simp]: "register_\<alpha> (r,s,h) = register_\<alpha> (r,s',h')"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma unfold_memory_\<alpha>:
  "memory_\<alpha> (r,s,h) = (\<lambda>saddr a \<Rightarrow> single_memory_\<alpha> s a | haddr a \<Rightarrow> single_memory_\<alpha> h a)"
  by (simp add: fun_eq_iff split: llvm_address.splits)


lemma single_memory_\<alpha>_set[single_memory_simps]:
  assumes "single_memory_\<alpha> s a \<noteq> None"
  shows "single_memory_\<alpha> (s[a := mem_val v]) = (single_memory_\<alpha> s)(a := Some (Some v))"
  using assms
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (auto split: if_splits)

lemma memory_\<alpha>_set_heap[simp]:
  assumes "memory_\<alpha> (r,s,h) (haddr a) \<noteq> None"
  shows "memory_\<alpha> (r,s,h[a := mem_val v]) = ((memory_\<alpha> (r,s,h))((haddr a) := Some (Some v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_stack[simp]:
  assumes "memory_\<alpha> (r,s,h) (saddr a) \<noteq> None"
  shows "memory_\<alpha> (r,s[a := mem_val v],h) = ((memory_\<alpha> (r,s,h))((saddr a) := Some (Some v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma single_memory_\<alpha>_allocate[single_memory_simps]:
  assumes "a \<noteq> length m"
  shows "single_memory_\<alpha> (m@[mem_unset]) a = (single_memory_\<alpha> m) a"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  using assms
  by (auto simp: nth_append)

lemma single_memory_\<alpha>_allocated[single_memory_simps]:
  "single_memory_\<alpha> (m@[mem_unset]) (length m) = Some None"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by simp

lemma memory_\<alpha>_allocate_heap_eq:
  assumes "a \<noteq> (haddr (length h))"
  shows "memory_\<alpha> (r,s,h@[mem_unset]) a = memory_\<alpha> (r,s,h) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_stack_eq:
  assumes "a \<noteq> (saddr (length s))"
  shows "memory_\<alpha> (r,s@[mem_unset],h) a = memory_\<alpha> (r,s,h) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_heap[simp]:
  "memory_\<alpha> (r, s, h @ [mem_unset]) = (memory_\<alpha> (r, s, h))(haddr (length h) := Some None)"
  by (auto simp: memory_\<alpha>_allocate_heap_eq single_memory_simps)

lemma memory_\<alpha>_allocate_stack[simp]:
  "memory_\<alpha> (r, s @ [mem_unset], h) = (memory_\<alpha> (r, s, h))(saddr (length s) := Some None)"
  by (auto simp: memory_\<alpha>_allocate_stack_eq single_memory_simps)


lemma single_memory_\<alpha>_free[single_memory_simps]:
  "single_memory_\<alpha> (s[a := mem_freed]) = (single_memory_\<alpha> s)(a := None)"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (auto split: if_splits)

lemma memory_\<alpha>_free_heap[simp]:
  "memory_\<alpha> (r,s,h[a := mem_freed]) = (memory_\<alpha> (r,s,h))(haddr a := None)"
  apply (rule ext)
  subgoal for a'
    by (cases a'; simp add: single_memory_simps)
  done

lemma memory_\<alpha>_free_stack[simp]:
  "memory_\<alpha> (r,s[a := mem_freed],h) = (memory_\<alpha> (r,s,h))(saddr a := None)"
  apply (rule ext)
  subgoal for a'
    by (cases a'; simp add: single_memory_simps)
  done


lemma single_memory_\<alpha>_not_none_iff[single_memory_simps]:
  "valid_single_memory_address s a \<longleftrightarrow> single_memory_\<alpha> s a \<noteq> None"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (cases "s!a"; simp)

lemma memory_\<alpha>_not_none_iff[simp]:
  "valid_memory_address s a \<longleftrightarrow> memory_\<alpha> s a \<noteq> None"
  by (cases s; cases a; simp add: single_memory_simps)


lemma single_memory_\<alpha>_some_some_iff[single_memory_simps]:
  "single_memory_\<alpha> s a = Some (Some v) \<longleftrightarrow> valid_single_memory_address s a \<and> s!a = mem_val v"
  unfolding get_single_memory_def single_memory_\<alpha>_def valid_single_memory_address_def
  by (cases "s!a"; simp)

lemma memory_\<alpha>_some_some_iff_heap[simp]:
  "memory_\<alpha> (r,s,h) (haddr a) = Some (Some v) \<longleftrightarrow> valid_memory_address (r,s,h) (haddr a) \<and> h!a = mem_val v"
  using single_memory_simps
  by fastforce

lemma single_memory_\<alpha>_some_some_iff_stack[simp]:
  "memory_\<alpha> (r,s,h) (saddr a) = Some (Some v) \<longleftrightarrow> valid_memory_address (r,s,h) (saddr a) \<and> s!a = mem_val v"
  using single_memory_simps
  by fastforce


section "Intro rules"

lemma wp_case_memory_value_intro[wp_intro]:
  assumes "x = mem_unset \<Longrightarrow> wp_gen f Q E"
  assumes "\<And>v. x = mem_val v \<Longrightarrow> wp_gen (g v) Q E"
  assumes "x = mem_freed \<Longrightarrow> wp_gen h Q E"
  shows "wp_gen (case x of mem_unset \<Rightarrow> f | mem_val v \<Rightarrow> g v | mem_freed \<Rightarrow> h) Q E"
  using assms
  by (cases x; simp)


lemma wp_get_single_memory[THEN consequence, single_memory_intro]:
  assumes "single_memory_\<alpha> s a \<noteq> None"
  assumes "single_memory_\<alpha> s a \<noteq> Some None"
  shows "wp (get_single_memory s a) (\<lambda>x. single_memory_\<alpha> s a = Some (Some x))"
  using assms
  unfolding get_single_memory_def valid_single_memory_address_def single_memory_\<alpha>_def
  by (intro wp_intro; simp)

lemma wp_get_memory_intro[THEN consequence, wp_intro]:
  assumes "memory_\<alpha> s a \<noteq> None"
  assumes "memory_\<alpha> s a \<noteq> Some None"
  shows "wp (get_memory s a) (\<lambda>x. memory_\<alpha> s a = Some (Some x))"
  using assms
  by (cases a; cases s; simp; intro single_memory_intro; simp)


lemma wp_set_single_memory[THEN consequence, single_memory_intro]:
  assumes "single_memory_\<alpha> m a \<noteq> None"
  shows "wp (set_single_memory m a v) (\<lambda>m'. single_memory_\<alpha> m' = (single_memory_\<alpha> m)(a := Some (Some v)))"
  using assms
  unfolding set_single_memory_def
  by (intro wp_intro; simp add: single_memory_simps)
                                                                               
lemma wp_set_memory_intro[THEN consequence, wp_intro]:
  assumes "memory_\<alpha> s a \<noteq> None"
  shows "wp (set_memory s a v) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (Some v)) \<and> register_\<alpha> s = register_\<alpha> s')"
  using assms 
  apply (cases a; cases s; simp)
  unfolding set_single_memory_def
  by (intro wp_intro; simp add: single_memory_simps)+


lemma wp_free_single_memory[THEN consequence, single_memory_intro]:
  assumes "single_memory_\<alpha> s a \<noteq> None"
  shows "wp (free_single_memory s a) (\<lambda>s'. (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := None))"
  using assms
  unfolding free_single_memory_def
  apply (intro wp_intro)
  apply (simp add: single_memory_simps)
  by (simp add: single_memory_simps)

lemma wp_free_memory_intro[THEN consequence, wp_intro]:
  assumes "memory_\<alpha> s a \<noteq> None"
  shows "wp (free_memory s a) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := None) \<and> register_\<alpha> s = register_\<alpha> s')"
  using assms
  apply (cases a; cases s; simp)
  apply (intro wp_intro single_memory_intro; simp; rule ext)
  subgoal for _ _ _ _ _ a' by (cases a'; simp)
  apply (intro wp_intro single_memory_intro; simp; rule ext)
  subgoal for _ _ _ _ _ a' by (cases a'; simp)
  done


lemma wp_allocate_single_memory[THEN consequence, single_memory_intro]:
  "wp (return (allocate_single_memory s)) (\<lambda>(s', a). (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some None))"
  unfolding allocate_single_memory_def
  by (intro wp_intro; auto simp: single_memory_simps)

lemma wp_allocate_heap_intro[THEN consequence, wp_intro]:
  "wp (return (allocate_heap s)) (\<lambda>(s', a). (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some None) \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_heap_def allocate_single_memory_def
  by (cases s; intro wp_intro; auto)

lemma wp_allocate_stack_intro[THEN consequence, wp_intro]:
  "wp (return (allocate_stack s)) (\<lambda>(s', a). (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some None) \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_stack_def allocate_single_memory_def
  by (cases s; intro wp_intro; auto)

subsection "Simps"

lemma memory_set_ok_iff[simp]: "valid_single_memory_address m a \<longleftrightarrow> (\<exists>m'. set_single_memory m a v = ok m')"
  unfolding set_single_memory_def
  by simp

lemma memory_get_ok_iff[simp]: "valid_single_memory_address m a \<and> m!a \<noteq> mem_unset \<longleftrightarrow> (\<exists>v. get_single_memory m a = ok v)"
  unfolding get_single_memory_def valid_single_memory_address_def
  by (cases "m!a"; simp)


subsection "Empty"

lemma memory_empty_get: "get_single_memory empty_memory_model a = err unallocated_address"
  unfolding empty_memory_model_def get_single_memory_def valid_single_memory_address_def
  by simp

lemma memory_empty_invalid: "\<not>valid_single_memory_address empty_memory_model a"
  unfolding empty_memory_model_def valid_single_memory_address_def
  by simp

lemma memory_empty_set: "set_single_memory empty_memory_model a v = err unallocated_address"
  unfolding empty_memory_model_def set_single_memory_def valid_single_memory_address_def
  by simp


subsection "Allocate"

lemma memory_allocate_validity: "allocate_single_memory m = (m', i) \<Longrightarrow> \<not>valid_single_memory_address m i \<and> valid_single_memory_address m' i"
  unfolding allocate_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_allocate_independent_valid[simp]: "allocate_single_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_single_memory_address m a \<longleftrightarrow> valid_single_memory_address m' a"
  unfolding valid_single_memory_address_def allocate_single_memory_def
  using nth_append_left
  by fastforce

lemma memory_allocate_independent_get: "allocate_single_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_single_memory m a = get_single_memory m' a" 
  unfolding valid_single_memory_address_def allocate_single_memory_def get_single_memory_def
  using nth_append_left
  by (cases "a < a'"; fastforce)

lemma memory_allocate_get_uninitialized: "allocate_single_memory m = (m', a) \<Longrightarrow> get_single_memory m' a = err uninitialized_address"
  unfolding get_single_memory_def valid_single_memory_address_def allocate_single_memory_def
  by auto


subsection "Set"

lemma memory_set_invalid: "\<not>valid_single_memory_address m a \<Longrightarrow> set_single_memory m a v = err unallocated_address"
  unfolding set_single_memory_def
  by simp

lemma memory_set_ok_valid: "set_single_memory m a v = ok m' \<Longrightarrow> valid_single_memory_address m' a \<and> valid_single_memory_address m a"
  unfolding set_single_memory_def
  apply simp
  unfolding valid_single_memory_address_def
  by auto

lemma wp_set_single_memory_independent_validity[THEN consequence, single_memory_intro]:
  assumes "valid_single_memory_address m a"
  shows "wp (set_single_memory m a v) (\<lambda> m'. valid_single_memory_address m' = valid_single_memory_address m)"
  using assms
  by (intro single_memory_intro; simp add: fun_eq_iff single_memory_simps)

lemma wp_set_memory_independent_validity:
  assumes "valid_memory_address s a"
  shows "wp (set_memory s a v) (\<lambda> s'. valid_memory_address s' = valid_memory_address s)"
  using assms
  by (intro wp_intro; simp add: fun_eq_iff)

lemma memory_set_override:
  assumes "set_single_memory m i v = ok m'"
  assumes "set_single_memory m' i v' = ok m''"
  shows "get_single_memory m'' i = ok v'"
  using assms
  unfolding set_single_memory_def get_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_set_override_wlp:
  "wlp (do {
    m' \<leftarrow> set_single_memory m a v1;
    m'' \<leftarrow> set_single_memory m' a v2;
    get_single_memory m'' a}) (\<lambda>v. v = v2)"
  unfolding set_single_memory_def get_single_memory_def valid_single_memory_address_def
  by (intro wp_intro; simp)


lemma memory_set_identity: "get_single_memory m i = ok v \<Longrightarrow> set_single_memory m i v = ok m' \<Longrightarrow> m = m'"
  unfolding get_single_memory_def set_single_memory_def
  apply simp
  unfolding valid_single_memory_address_def
  apply (cases "m!i"; simp)
  using list_update_id
  by metis

lemma memory_set_identity_wlp: "wlp (do { v \<leftarrow> get_single_memory m a; set_single_memory m a v }) ((=) m)"
  unfolding get_single_memory_def set_single_memory_def valid_single_memory_address_def
  apply (intro wp_intro; simp)
  apply (cases "m!a"; simp)
  using list_update_id
  by metis


lemma memory_set_get: "set_single_memory m i v = ok m' \<Longrightarrow> get_single_memory m' i = ok v"
  unfolding get_single_memory_def set_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_set_get_wlp: "wlp (do {m' \<leftarrow> set_single_memory m a v; get_single_memory m' a}) ((=) v)"
  unfolding get_single_memory_def set_single_memory_def valid_single_memory_address_def
  by (intro wp_intro; simp)


lemma memory_set_independent_get: "set_single_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_single_memory m a = get_single_memory m' a"
  unfolding get_single_memory_def set_single_memory_def
  apply simp
  unfolding valid_single_memory_address_def
  by auto

lemma memory_set_independent_get_wlp: "a \<noteq> a' \<Longrightarrow> wlp (set_single_memory m a' v) (\<lambda>m'. get_single_memory m' a = get_single_memory m a)"
  unfolding get_single_memory_def set_single_memory_def
  apply (intro wp_intro)
  apply simp
  unfolding valid_single_memory_address_def
  by auto


lemma memory_set_independent_valid: "set_single_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_single_memory_address m a = valid_single_memory_address m' a"
  unfolding get_single_memory_def set_single_memory_def
  apply simp
  unfolding valid_single_memory_address_def
  by auto


subsection "Get"

lemma memory_get_ok_valid: "get_single_memory m a = ok v \<Longrightarrow> valid_single_memory_address m a"
  unfolding get_single_memory_def
  by simp


subsection "Free"

lemma memory_free_get: "free_single_memory m a = ok m' \<Longrightarrow> get_single_memory m' a = err unallocated_address"
  unfolding free_single_memory_def get_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_free_set: "free_single_memory m a = ok m' \<Longrightarrow> set_single_memory m' a v = err unallocated_address"
  unfolding free_single_memory_def set_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_free_invalid: "free_single_memory m a = ok m' \<Longrightarrow> \<not>valid_single_memory_address m' a \<and> valid_single_memory_address m a"
  unfolding free_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_free_independent_valid: "free_single_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_single_memory_address m a \<longleftrightarrow> valid_single_memory_address m' a"
  unfolding free_single_memory_def valid_single_memory_address_def
  by auto

lemma memory_free_independent_get: "free_single_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_single_memory m a = ok v \<longleftrightarrow> get_single_memory m' a = ok v"
  unfolding free_single_memory_def get_single_memory_def valid_single_memory_address_def
  by auto


end