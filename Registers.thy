theory Registers
  imports Definitions
begin

section "Simps"

lemma memory_\<alpha>_eq[simp]: "memory_\<alpha> (lr,gr,sm,hm,gm) = memory_\<alpha> (lr',gr',sm,hm,gm)"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma register_\<alpha>_lid_update_eq[simp]:
  "register_\<alpha> (Mapping.update n v lr,gr,sm,hm,gm) = (register_\<alpha> (lr,gr,sm,hm,gm))(reg (lid n) := Some v)"
  apply (auto simp: fun_eq_iff split: llvm_value_ref.split)
  subgoal for x apply (cases x; simp) subgoal for id by (cases id; simp)
  done
  done

lemma register_\<alpha>_val_eq[simp]:
  "register_\<alpha> s (val v) = Some v"
  by (cases s; simp)

lemma register_\<alpha>_update_independent[simp]:
  "(register_\<alpha> s)(x := v) = register_\<alpha> s' \<Longrightarrow> x \<noteq> y \<Longrightarrow> register_\<alpha> s y = register_\<alpha> s' y"
  by (metis fun_upd_other)

lemma register_\<alpha>_eq_get_register:
  "register_\<alpha> s v = Some v' \<longleftrightarrow> dereference s v = ok v'"
  apply (cases s; cases v; auto)
  subgoal for _ _ _ _ _ n by (cases n; simp split: option.splits)
  subgoal for _ _ _ _ _ n by (cases n; simp split: option.splits)
  done


section "register_\<alpha> operation"

lemma set_register_\<alpha>:
  "set_register n v s = ok s' \<Longrightarrow> register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v)"
  apply (cases s; rule ext)
  subgoal for l' g' s' h' x by (cases x; cases n; auto simp: set_single_register_def)
  done



section "Intro rules"

named_theorems register_intro

lemma wp_set_single_register_lid_intro[THEN consequence, register_intro]:
  "wp (return (set_single_register n v lr,gr,sm,hm,gm)) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> (lr,gr,sm,hm,gm))(reg (lid n) := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> (lr,gr,sm,hm,gm))"
  unfolding set_single_register_def
  by (intro wp_intro wp_return_intro; simp)

lemma wp_set_register_intro[THEN consequence, wp_intro]:
  assumes "is_lid n"
  shows "wp (set_register n v s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg n := Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  using assms
  by (cases n; cases s; simp; intro wp_intro register_intro; simp add: set_single_register_def)


lemma wp_get_register_intro[THEN consequence, wp_intro]:        
  assumes "register_\<alpha> s n \<noteq> None"
  shows "wp (dereference s n) (\<lambda>v'. register_\<alpha> s n = Some v')"
  using assms
  apply (cases s; cases n) subgoal for _ _ _ _ _ id by (cases id; simp; intro wp_intro; auto split: option.splits)
  by simp



section "Stack Frames"

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (lid n)) = register_\<alpha> s (reg (lid n))"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)

lemma "s' = push_frame s \<Longrightarrow> s'' = f s' \<Longrightarrow> s''' = pop_frame s s'' \<Longrightarrow> \<forall>n. register_\<alpha> s''' (reg (gid n)) = register_\<alpha> s'' (reg (gid n))"
  by (cases s; cases s'; cases s''; cases s'''; fastforce)



end