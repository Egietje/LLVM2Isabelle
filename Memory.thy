theory Memory    
  imports Definitions
begin

section "Simps"

lemma register_\<alpha>_eq[simp]: "register_\<alpha> (lr,gr,sm,hm,gm) = register_\<alpha> (lr,gr,sm',hm',gm')"
  apply (rule ext)
  subgoal for x
    apply (cases x; simp)
    subgoal for id
      by (cases id; simp)
    done
  done


named_theorems single_memory_simps
named_theorems single_memory_intro

lemma single_memory_\<alpha>_set[single_memory_simps]:
  assumes "valid_single_memory_address s a"
  shows "single_memory_\<alpha> (s[a := mem_val v]) = (single_memory_\<alpha> s)(a := Some (mem_val v))"
  using assms
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def valid_single_memory_address_def
  by (auto split: if_splits)

lemma memory_\<alpha>_set_stack[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (saddr a)"
  shows "memory_\<alpha> (lr,gr,sm[a := mem_val v],hm,gm) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((saddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_heap[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (haddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm[a := mem_val v],gm) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((haddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done

lemma memory_\<alpha>_set_global[simp]:
  assumes "valid_memory_address (lr,gr,sm,hm,gm) (gaddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm,gm[a := mem_val v]) = ((memory_\<alpha> (lr,gr,sm,hm,gm))((gaddr a) := Some (mem_val v)))"
  apply (rule ext)
  subgoal for a'
  using assms single_memory_simps
  by (cases a'; fastforce)
  done


lemma single_memory_\<alpha>_allocate[single_memory_simps]:
  assumes "a \<noteq> length m"
  shows "single_memory_\<alpha> (m@[mem_unset]) a = (single_memory_\<alpha> m) a"
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  using assms
  by (auto simp: nth_append)


lemma single_memory_\<alpha>_allocated[single_memory_simps]:
  "single_memory_\<alpha> (m@[mem_unset]) (length m) = Some mem_unset"
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  by simp

lemma memory_\<alpha>_allocate_stack_eq:
  assumes "a \<noteq> (saddr (length sm))"
  shows "memory_\<alpha> (lr,gr,sm@[mem_unset],hm,gm) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_heap_eq:
  assumes "a \<noteq> (haddr (length hm))"
  shows "memory_\<alpha> (lr,gr,sm,hm@[mem_unset],gm) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)

lemma memory_\<alpha>_allocate_global_eq:
  assumes "a \<noteq> (gaddr (length gm))"
  shows "memory_\<alpha> (lr,gr,sm,hm,gm@[mem_unset]) a = memory_\<alpha> (lr,gr,sm,hm,gm) a"
  using assms
  by (cases a; simp add: single_memory_simps)


lemma memory_\<alpha>_allocate_stack[simp]:
  "memory_\<alpha> (lr,gr,sm@[mem_unset],hm,gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(saddr (length sm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_stack_eq single_memory_simps)

lemma memory_\<alpha>_allocate_heap[simp]:
  "memory_\<alpha> (lr,gr,sm,hm@[mem_unset],gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(haddr (length hm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_heap_eq single_memory_simps)

lemma memory_\<alpha>_allocate_global[simp]:
  "memory_\<alpha> (lr,gr,sm,hm,gm@[mem_unset]) = (memory_\<alpha> (lr,gr,sm,hm,gm))(gaddr (length gm) := Some mem_unset)"
  by (auto simp: memory_\<alpha>_allocate_global_eq single_memory_simps)


lemma single_memory_\<alpha>_free[single_memory_simps]:
  assumes "allocated_single_memory_address s a"
  shows "single_memory_\<alpha> (s[a := mem_freed]) = (single_memory_\<alpha> s)(a := Some mem_freed)"
  using assms
  unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
  by (auto split: if_splits)


lemma memory_\<alpha>_free_heap[simp]:
  assumes "allocated_memory_address (lr,gr,sm,hm,gm) (haddr a)"
  shows "memory_\<alpha> (lr,gr,sm,hm[a := mem_freed],gm) = (memory_\<alpha> (lr,gr,sm,hm,gm))(haddr a := Some mem_freed)"
  apply (rule ext)
  subgoal for a'
    using assms
    by (cases a'; simp add: single_memory_simps)
  done


lemma single_memory_\<alpha>_not_none_iff[single_memory_simps]:
  "allocated_single_memory_address s a \<longleftrightarrow> single_memory_\<alpha> s a \<noteq> None"
  unfolding single_memory_\<alpha>_def valid_single_memory_address_def
  by (cases "s!a"; simp)

lemma allocated_address_iff[simp]:
  "allocated_memory_address s a \<longleftrightarrow> memory_\<alpha> s a \<noteq> None"
  by (cases s; cases a; simp add: single_memory_simps)

lemma valid_address_iff[simp]:
  "valid_memory_address s a \<longleftrightarrow> (memory_\<alpha> s a \<noteq> None \<and> memory_\<alpha> s a \<noteq> Some mem_freed)"
  by (cases s; cases a; auto simp: single_memory_\<alpha>_def valid_single_memory_address_def)


lemma memory_\<alpha>_allocate_validity:
  assumes "memory_\<alpha> m' = (memory_\<alpha> m)(a := Some mem_unset)"
  shows "allocated_memory_address m' = (allocated_memory_address m)(a := True)" "valid_memory_address m' = (valid_memory_address m)(a := True)"
  using assms
  by (auto simp: fun_eq_iff)
  


lemma memory_\<alpha>_set_validity:
  assumes "valid_memory_address s a"
  assumes "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v))"
  shows "allocated_memory_address s' = allocated_memory_address s" "valid_memory_address s' = valid_memory_address s"
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp add: single_memory_\<alpha>_def valid_single_memory_address_def)
  done
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp add: single_memory_\<alpha>_def fun_upd_def valid_single_memory_address_def fun_eq_iff allocated_single_memory_address_def split: if_splits)
  done
  done

lemma memory_\<alpha>_free_validity:
  assumes "valid_memory_address s a"
  assumes "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_freed)"
  shows "allocated_memory_address s' = allocated_memory_address s" "valid_memory_address s' = (valid_memory_address s)(a := False)"
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr)
      by (auto simp: single_memory_\<alpha>_def valid_single_memory_address_def split: if_splits)
    done
  subgoal
    apply (rule ext)
    subgoal for addr
      using assms
      apply (cases s; cases s'; cases addr; cases "a = addr")
      by (auto simp: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_upd_def fun_eq_iff split: if_splits)
    done
  done


lemma memory_\<alpha>_distinct_addresses[simp]:
  "memory_\<alpha> s a1 = Some v \<Longrightarrow> memory_\<alpha> s a2 = None \<Longrightarrow> a1 \<noteq> a2"
  by auto




section "memory_\<alpha> operations"

lemma set_memory_\<alpha>:
  assumes "valid_memory_address s a"
  shows "\<exists>s'. set_memory a v s = ok s' \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v))"
  using assms
  by (cases s; cases a; auto simp: single_memory_\<alpha>_def set_single_memory_def valid_single_memory_address_def split: if_splits)

lemma allocate_stack_\<alpha>:
  assumes "allocate_stack s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_stack_def allocate_single_memory_def)

lemma allocate_heap_\<alpha>:
  assumes "allocate_heap s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_heap_def allocate_single_memory_def)

lemma allocate_global_\<alpha>:
  assumes "allocate_global s = (s', a)"
  shows "memory_\<alpha> s' = (memory_\<alpha> s)(a := Some mem_unset)"
  using assms
  by (cases s; cases s'; cases a; auto simp: allocate_global_def allocate_single_memory_def)

lemma free_memory_\<alpha>:
  assumes "valid_memory_address s (haddr a)"
  shows "\<exists>s'. free_memory (haddr a) s = ok s' \<and> memory_\<alpha> s' = (memory_\<alpha> s)((haddr a) := Some mem_freed)"
  using assms
  by (cases s; auto simp: single_memory_\<alpha>_def free_single_memory_def valid_single_memory_address_def split: if_splits)



section "Intro rules"

lemma wp_case_memory_value_intro[wp_intro]:
  assumes "x = mem_unset \<Longrightarrow> wp f Q"
  assumes "\<And>v. x = mem_val v \<Longrightarrow> wp (g v) Q"
  assumes "x = mem_freed \<Longrightarrow> wp h Q"
  shows "wp (case x of mem_unset \<Rightarrow> f | mem_val v \<Rightarrow> g v | mem_freed \<Rightarrow> h) Q"
  using assms
  by (cases x; simp)


lemma wp_get_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a" "single_memory_\<alpha> s a \<noteq> Some mem_unset"
  shows "wp (get_single_memory s a) (\<lambda>x. single_memory_\<alpha> s a = Some (mem_val x))"
  using assms
  unfolding get_single_memory_def valid_single_memory_address_def single_memory_\<alpha>_def
  by (intro wp_intro; simp)

lemma wp_get_memory_intro[THEN consequence, rotated -1, wp_intro]:
  assumes "valid_memory_address s a" "memory_\<alpha> s a \<noteq> Some mem_unset"
  shows "wp (get_memory s a) (\<lambda>x. memory_\<alpha> s a = Some (mem_val x))"
  using assms
  by (cases a; cases s; simp; intro single_memory_intro; simp add: single_memory_\<alpha>_def valid_single_memory_address_def split: if_splits)


lemma wp_set_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a"
  shows "wp (set_single_memory a v s) (\<lambda>s'. single_memory_\<alpha> s' = (single_memory_\<alpha> s)(a := Some (mem_val v)))"
  using assms
  unfolding set_single_memory_def
  by (intro wp_intro wp_return_intro; simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_eq_iff split: if_splits)


lemma wp_set_memory_intro[THEN consequence, rotated -1, wp_intro]:
  assumes "valid_memory_address s a"
  shows "wp (set_memory a v s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (mem_val v)) \<and> register_\<alpha> s = register_\<alpha> s')"
  using assms 
  by (cases a; cases s; simp add: set_single_memory_def; intro wp_intro wp_return_intro; simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def fun_eq_iff split: if_splits; metis register_\<alpha>_eq)


lemma wp_free_single_memory_intro[THEN consequence, rotated -1, single_memory_intro]:
  assumes "valid_single_memory_address s a"
  shows "wp (free_single_memory a s) (\<lambda>s'. (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some mem_freed))"
  using assms
  unfolding free_single_memory_def
  apply (intro wp_intro wp_return_intro)
  by (auto simp: single_memory_\<alpha>_free valid_single_memory_address_def)

lemma wp_free_memory_intro[THEN consequence, rotated -1, wp_intro]:
  assumes "valid_memory_address s (haddr a)"
  shows "wp (free_memory (haddr a) s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)((haddr a) := Some mem_freed) \<and> register_\<alpha> s = register_\<alpha> s')"
  apply (cases s; simp)
  using assms
   apply (intro wp_intro single_memory_intro wp_return_intro, auto) defer
  using assms valid_memory_address.simps apply blast
   apply (rule ext)
  subgoal for _ _ _ _ _ _ _ a' by (cases a'; simp)
  done


lemma wp_allocate_single_memory[THEN consequence, rotated -1, single_memory_intro]:
  "wp (return (allocate_single_memory s)) (\<lambda>(s', a). (single_memory_\<alpha> s') = (single_memory_\<alpha> s)(a := Some mem_unset) \<and> single_memory_\<alpha> s a = None)"
  unfolding allocate_single_memory_def
  apply (intro wp_intro wp_return_intro; auto simp: single_memory_simps)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)


lemma wp_allocate_stack_intro[THEN consequence, rotated -1, wp_intro]:
  "wp (return (allocate_stack s)) (\<lambda>(s', a). (\<exists>a'. a = saddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_stack_def allocate_single_memory_def
  apply (cases s; intro wp_intro wp_return_intro; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)

lemma wp_allocate_heap_intro[THEN consequence, rotated -1, wp_intro]:
  "wp (return (allocate_heap s)) (\<lambda>(s', a). (\<exists>a'. a = haddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_heap_def allocate_single_memory_def
  apply (cases s; intro wp_intro wp_return_intro; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)

lemma wp_allocate_global_intro[THEN consequence, rotated -1, wp_intro]:
  "wp (return (allocate_global s)) (\<lambda>(s', a). (\<exists>a'. a = gaddr a') \<and> (memory_\<alpha> s') = (memory_\<alpha> s)(a := Some mem_unset) \<and> memory_\<alpha> s a = None \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding allocate_global_def allocate_single_memory_def
  apply (cases s; intro wp_intro wp_return_intro; auto)
  by (simp add: single_memory_\<alpha>_def valid_single_memory_address_def allocated_single_memory_address_def)



section "Stack Frames"

definition "mem_op_well_behaved f \<equiv> \<forall>s a. ((memory_\<alpha> s a \<noteq> None \<longrightarrow> memory_\<alpha> (f s) a \<noteq> None) \<and> (memory_\<alpha> s a = Some mem_freed \<longrightarrow> memory_\<alpha> (f s) a = Some mem_freed))"

lemma well_behaved_imp_stack_grows:
  assumes "mem_op_well_behaved f" "(lr',gr',sm',hm',gm') = f (lr,gr,sm,hm,gm)"
  shows "length sm' \<ge> length sm"
  unfolding mem_op_well_behaved_def
proof -
  have "\<And>lr gr sm hm gm a. memory_\<alpha> (lr,gr,sm,hm,gm) (saddr a) \<noteq> None \<Longrightarrow> a < length sm"
    apply simp
    unfolding single_memory_\<alpha>_def allocated_single_memory_address_def
    by (auto split: if_splits)        

  moreover

  have "\<And>a. memory_\<alpha> (lr,gr,sm,hm,gm) a \<noteq> None \<Longrightarrow> memory_\<alpha> (lr',gr',sm',hm',gm') a \<noteq> None"
    using assms mem_op_well_behaved_def
    by simp

  ultimately
  
  show ?thesis
    by (metis allocated_single_memory_address_def memory_\<alpha>.simps(1) nat_le_linear nat_less_le
        single_memory_\<alpha>_not_none_iff)
qed


lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> mem_op_well_behaved f \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>a. memory_\<alpha> s''' (haddr a) = memory_\<alpha> s'' (haddr a)"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)
lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> mem_op_well_behaved f \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>a. memory_\<alpha> s''' (gaddr a) = memory_\<alpha> s'' (gaddr a)"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> mem_op_well_behaved f \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>a. memory_\<alpha> s (saddr a) \<noteq> None \<longleftrightarrow> memory_\<alpha> s''' (saddr a) \<noteq> None"
  apply (cases s; cases s'; cases s''; cases s''')
  subgoal premises prems for lr gr sm hm gm lr' gr' sm' hm' gm' lr'' gr'' sm'' hm'' gm'' lr''' gr''' sm''' hm''' gm'''
  proof -
    obtain n n' n'' n''' where "n = length sm" "n' = length sm'" "n'' = length sm''" "n''' = length sm'''"
      by blast

    have "n''' = length (take n sm'')"
      using \<open>n = length sm\<close> \<open>n''' = length sm'''\<close> prems(4,5,7,8)
      by fastforce

    have "n' = n"
      using \<open>n = length sm\<close> \<open>n' = length sm'\<close> prems(1,5,6)
      by auto

    have "n'' \<ge> n"
      using \<open>n' = length sm'\<close> \<open>n' = n\<close> \<open>n'' = length sm''\<close> prems(2,3,6,7) well_behaved_imp_stack_grows
      by auto

    have "n = n'''" 
      using \<open>n \<le> n''\<close> \<open>n'' = length sm''\<close> \<open>n''' = length (take n sm'')\<close>
      by force

    show ?thesis using \<open>n = n'''\<close> \<open>n = length sm\<close> \<open>n''' = length sm'''\<close>
      by (simp add: single_memory_\<alpha>_def allocated_single_memory_address_def prems(5,8))
  qed
  done

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> mem_op_well_behaved f \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (lid n)) = register_\<alpha> s (reg (lid n))"
  by (cases s; cases s''; fastforce)

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> mem_op_well_behaved f \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (gid n)) = register_\<alpha> s'' (reg (gid n))"
  by (cases s; cases s''; fastforce)



end