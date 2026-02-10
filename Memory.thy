theory Memory    
  imports Definitions
begin

section "Simps"

lemma ssa_\<alpha>_eq[simp]: "ssa_\<alpha> (vs,s,h) = ssa_\<alpha> (vs,s',h')"
  apply (rule ext)
  subgoal for x
    by (cases vs; cases x; simp; metis)
  done


named_theorems single_memory_simps
named_theorems single_memory_intro


lemma single_memory_\<alpha>_set[single_memory_simps]:
  assumes "single_memory_\<alpha> s a \<noteq> None"
  shows "single_memory_\<alpha> (s[a := mem_val v]) = (single_memory_\<alpha> s)(a := Some (Some v))"
  using assms
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (auto split: if_splits)

lemma memory_\<alpha>_set_heap[simp]:
  assumes "memory_\<alpha> (vs,s,h) (haddr a) \<noteq> None"
  shows "memory_\<alpha> (vs,s,h[a := mem_val v]) = ((memory_\<alpha> (vs,s,h))((haddr a) := Some (Some v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_stack[simp]:
  assumes "memory_\<alpha> (vs,s,h) (saddr a) \<noteq> None"
  shows "memory_\<alpha> (vs,s[a := mem_val v],h) = ((memory_\<alpha> (vs,s,h))((saddr a) := Some (Some v)))"
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
  shows "memory_\<alpha> (vs,s,h@[mem_unset]) a = memory_\<alpha> (vs,s,h) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_stack_eq:
  assumes "a \<noteq> (saddr (length s))"
  shows "memory_\<alpha> (vs,s@[mem_unset],h) a = memory_\<alpha> (vs,s,h) a"
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
  "memory_\<alpha> (vs,s,h[a := mem_freed]) = (memory_\<alpha> (vs,s,h))(haddr a := None)"
  apply (rule ext)
  subgoal for a'
    by (cases a'; simp add: single_memory_simps)
  done

lemma memory_\<alpha>_free_stack[simp]:
  "memory_\<alpha> (vs,s[a := mem_freed],h) = (memory_\<alpha> (vs,s,h))(saddr a := None)"
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


lemma memory_\<alpha>_allocate_validity[simp]:
  assumes "memory_\<alpha> m' = (memory_\<alpha> m)(a := Some None)"
  assumes "a \<noteq> a'"
  shows "valid_memory_address m a' = valid_memory_address m' a' \<and> valid_memory_address m' a"
  using assms
  by simp

lemma memory_\<alpha>_set_validity[simp]:
  assumes "memory_\<alpha> m' = (memory_\<alpha> m)(a := Some (Some v))"
  assumes "memory_\<alpha> m a \<noteq> None"
  shows "valid_memory_address m = valid_memory_address m'"
  using assms
  by (simp add: fun_eq_iff)

lemma memory_\<alpha>_free_validity[simp]:
  assumes "memory_\<alpha> m' = (memory_\<alpha> m)(a := None)"
  assumes "a \<noteq> a'"
  shows "valid_memory_address m a' = valid_memory_address m' a' \<and> \<not>valid_memory_address m' a"
  using assms
  by simp



section "Intro rules"

lemma wp_case_memory_value_intro[wp_intro]:
  assumes "x = mem_unset \<Longrightarrow> wp_gen f Q E"
  assumes "\<And>v. x = mem_val v \<Longrightarrow> wp_gen (g v) Q E"
  assumes "x = mem_freed \<Longrightarrow> wp_gen h Q E"
  shows "wp_gen (case x of mem_unset \<Rightarrow> f | mem_val v \<Rightarrow> g v | mem_freed \<Rightarrow> h) Q E"
  using assms
  by (cases x; simp)


lemma wp_get_single_memory_intro[THEN consequence, single_memory_intro]:
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


lemma wp_set_single_memory_intro[THEN consequence, single_memory_intro]:
  assumes "single_memory_\<alpha> m a \<noteq> None"
  shows "wp (set_single_memory m a v) (\<lambda>m'. single_memory_\<alpha> m' = (single_memory_\<alpha> m)(a := Some (Some v)))"
  using assms
  unfolding set_single_memory_def
  by (intro wp_intro wp_return_intro; simp add: single_memory_simps)
                                                                               
lemma wp_set_memory_intro[THEN consequence, wp_intro]:
  assumes "memory_\<alpha> s a \<noteq> None"
  shows "wp (set_memory s a v) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (Some v)) \<and> ssa_\<alpha> s = ssa_\<alpha> s')"
  using assms 
  apply (cases a; cases s; simp)
  unfolding set_single_memory_def
  by (intro wp_intro wp_return_intro; simp add: single_memory_simps; rule ext; simp)+


lemma wp_free_single_memory_intro[THEN consequence, single_memory_intro]:
  assumes "single_memory_\<alpha> s a \<noteq> None"
  shows "wp (free_single_memory s a) (\<lambda>s'. (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := None))"
  using assms
  unfolding free_single_memory_def
  apply (intro wp_intro wp_return_intro)
  apply (simp add: single_memory_simps)
  by (simp add: single_memory_simps)

lemma wp_free_memory_intro[THEN consequence, wp_intro]:
  assumes "memory_\<alpha> s a \<noteq> None"
  shows "wp (free_memory s a) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := None) \<and> ssa_\<alpha> s = ssa_\<alpha> s')"
  using assms
  apply (cases a; cases s; simp)
  apply (intro wp_intro single_memory_intro wp_return_intro; simp; rule ext)
  subgoal for _ _ _ _ _ a' by (cases a'; simp)
  apply (intro wp_intro single_memory_intro wp_return_intro; simp; rule ext)
  subgoal for _ _ _ _ _ a' by (cases a'; simp)
  done


lemma wp_allocate_single_memory[THEN consequence, single_memory_intro]:
  "wp (return (allocate_single_memory s)) (\<lambda>(s', a). (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some None))"
  unfolding allocate_single_memory_def
  by (intro wp_intro wp_return_intro; auto simp: single_memory_simps)

lemma wp_allocate_heap_intro[THEN consequence, wp_intro]:
  "wp (return (allocate_heap s)) (\<lambda>(s', a). (\<exists>a'. a = haddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some None) \<and> ssa_\<alpha> s = ssa_\<alpha> s')"
  unfolding allocate_heap_def allocate_single_memory_def
  by (cases s; intro wp_intro wp_return_intro; auto)

lemma wp_allocate_stack_intro[THEN consequence, wp_intro]:
  "wp (return (allocate_stack s)) (\<lambda>(s', a). (\<exists>a'. a = saddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some None) \<and> ssa_\<alpha> s = ssa_\<alpha> s')"
  unfolding allocate_stack_def allocate_single_memory_def
  by (cases s; intro wp_intro wp_return_intro; auto)

end