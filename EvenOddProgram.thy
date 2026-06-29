theory EvenOddProgram
  imports "HOL-Library.AList_Mapping" "VCG"
begin

section "Even/odd Functions"

definition odd_entry :: "llvm_instruction_block" where
  "odd_entry \<equiv> (
    [],
    [
      alloca (%''n.addr'') i32 (Some 4),
      store i32 (reg %''n'') (reg %''n.addr'') (Some 4),
      load (%''0'') i32 (reg %''n.addr'') (Some 4),
      call (Some %''call'') i1 (@''even'') [(i32, reg %''0'')],
      icmp (%''lnot'') False comp_eq i1 (reg %''call'') (val (vi1 False))
    ],
    ret (Some (i1, (reg %''lnot'')))
  )"

definition odd_func :: "llvm_function" where
  "odd_func \<equiv> func i1 [(%''n'', i32)]
    [
      (%''entry'', odd_entry)
    ]"


definition even_entry :: "llvm_instruction_block" where
  "even_entry \<equiv> (
    [],
    [
      alloca (%''retval'') i1 (Some 1),
      alloca (%''n.addr'') i32 (Some 4),
      store i32 (reg %''n'') (reg %''n.addr'') (Some 4),
      load (%''0'') i32 (reg %''n.addr'') (Some 4),
      icmp (%''cmp'') False comp_eq i32 (reg %''0'') (val (vi32 0))
    ],
    br_i1 (reg %''cmp'') (%''if.then'') (%''if.else'')
  )"
definition even_if :: "llvm_instruction_block" where
  "even_if \<equiv> (
    [],
    [
      store i1 (val (vi1 True)) (reg %''retval'') (Some 1)
    ],
    br_label (%''return'')
  )"
definition even_else :: "llvm_instruction_block" where
  "even_else \<equiv> (
    [],
    [
      load (%''1'') i32 (reg %''n.addr'') (Some 4),
      add (%''sub'') add_nsw i32 (reg %''1'') (val (vi32 (-1))),
      call (Some %''call'') i1 (@''odd'') [(i32, reg %''sub'')],
      store i1 (reg %''call'') (reg %''retval'') (Some 1)
    ],
    br_label (%''return'')
  )"
definition even_return :: "llvm_instruction_block" where
  "even_return \<equiv> (
    [],
    [
      load (%''2'') i32 (reg %''retval'') (Some 4)
    ],
    ret (Some (i1, (reg %''2'')))
  )"

definition even_func :: "llvm_function" where
  "even_func \<equiv> func i1 [(%''n'', i32)]
    [
      (%''entry'', even_entry),
      (%''if.then'', even_if),
      (%''if.else'', even_else),
      (%''return'', even_return)
    ]"

abbreviation even_annots :: "precondition * block_preconditions * postcondition" where
  "even_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg %''n'') = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n b a1 a2. register_\<alpha> s (reg %''n'') = Some (vi32 n)
    \<and> v = Some (vi1 (even n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr a1 := Some (mem_val (vi32 n)), saddr a2 := Some (mem_val (vi1 b)))
    \<and> memory_\<alpha> s (saddr a1) = None
    \<and> memory_\<alpha> s (saddr a2) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg @n) = register_\<alpha> s (reg @n))
    )
  )"
abbreviation odd_annots :: "precondition * block_preconditions * postcondition" where
  "odd_annots \<equiv> (
    (\<lambda>s.
      \<exists>n. register_\<alpha> s (reg %''n'') = Some (vi32 n)
    \<and> 0 \<le>s n
    ),
    [],
    (\<lambda>s s' v.
      \<exists>n ad. register_\<alpha> s (reg %''n'') = Some (vi32 n)
    \<and> v = Some (vi1 (odd n))
    \<and> memory_\<alpha> s' = (memory_\<alpha> s)(saddr ad := Some (mem_val (vi32 n)))
    \<and> memory_\<alpha> s (saddr ad) = None
    \<and> (\<forall>n. register_\<alpha> s' (reg @n) = register_\<alpha> s (reg @n))
    )
  )"

definition even_odd_prog :: "llvm_program" where
  "even_odd_prog \<equiv> [
    (@''even'', even_func),
    (@''odd'',  odd_func)
  ]"

definition even_odd_annots :: "annotations" where
  "even_odd_annots \<equiv> [
    (@''even'', even_annots),
    (@''odd'',  odd_annots)
  ]"

lemma register_\<alpha>_pop_contract [simp]:
  "register_\<alpha> (pop_frame s s') ref = (
     case ref of
       reg (lid n) \<Rightarrow> register_\<alpha> s (reg (lid n))
     | reg (gid n) \<Rightarrow> register_\<alpha> s' (reg (gid n))
     | val v       \<Rightarrow> Some v)"
  by (cases s; cases s'; cases ref; auto split: llvm_value_ref.splits llvm_identifier.splits) 
fun stack_len :: "state \<Rightarrow> nat" where
  "stack_len (lr, gr, sm, hm, gm) = length sm"

lemma memory_\<alpha>_pop_saddr [simp]:
  "memory_\<alpha> (pop_frame s s') (saddr a) = 
     (if memory_\<alpha> s (saddr a) \<noteq> None then memory_\<alpha> s' (saddr a) else None)"
  by (cases s; cases s'; simp add: single_memory_\<alpha>_def allocated_single_memory_address_def)

lemma memory_\<alpha>_pop_haddr [simp]:
  "memory_\<alpha> (pop_frame s s') (haddr a) = memory_\<alpha> s' (haddr a)"
  by (cases s; cases s'; simp)

lemma memory_\<alpha>_pop_gaddr [simp]:
  "memory_\<alpha> (pop_frame s s') (gaddr a) = memory_\<alpha> s' (gaddr a)"
  by (cases s; cases s'; simp)


lemma register_\<alpha>_push_frame [simp]:
  "register_\<alpha> (push_frame s) (reg (lid n)) = None"
  "register_\<alpha> (push_frame s) (reg (gid n)) = register_\<alpha> s (reg (gid n))"
  by (cases s; simp)+

lemma memory_\<alpha>_push_frame [simp]:
  "memory_\<alpha> (push_frame s) = memory_\<alpha> s"
  apply (rule ext) subgoal for ad
    by (cases s; cases ad; simp)
  done





lemma contract_updates_register[simp]:
  assumes trace_link: "\<And>r. register_\<alpha> callee_state (reg @r) = f (reg @r)"
  assumes frame_invariant: "\<And>r name. r = reg @name \<Longrightarrow> f r = register_\<alpha> caller_state r"
  shows "register_\<alpha> (pop_frame caller_state callee_state) = register_\<alpha> caller_state"
  apply (rule ext)
  subgoal for n apply (cases n)
  subgoal for name apply (cases name)
    using assms by (auto )
  by simp done

lemma pop_frame_peel_gaddr [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then (C (gaddr ga \<mapsto> v)) a else None | _ \<Rightarrow> (C (gaddr ga \<mapsto> v)) a) =
   ((\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (gaddr ga \<mapsto> v))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_haddr [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then (C (haddr ha \<mapsto> v)) a else None | _ \<Rightarrow> (C (haddr ha \<mapsto> v)) a) =
   ((\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (haddr ha \<mapsto> v))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_saddr [simp]:
  "(\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then (C (saddr sa \<mapsto> v)) a else None | _ \<Rightarrow> (C (saddr sa \<mapsto> v)) a) =
   (if M (saddr sa) \<noteq> None 
    then ((\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a) (saddr sa \<mapsto> v))
    else (\<lambda>a. case a of saddr sa' \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a))"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_M_drop_saddr [simp]:
  "C (saddr sa') = None \<Longrightarrow>
   (\<lambda>a. case a of saddr sa \<Rightarrow> if (M(saddr sa' \<mapsto> v)) a \<noteq> None then C a else None | _ \<Rightarrow> C a) =
   (\<lambda>a. case a of saddr sa \<Rightarrow> if M a \<noteq> None then C a else None | _ \<Rightarrow> C a)"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma pop_frame_peel_absolute_base [simp]:
  "(\<lambda>a. case a of saddr sa \<Rightarrow> if C a \<noteq> None then C a else None | _ \<Rightarrow> C a) = C"
  apply (rule ext) subgoal for a by (cases a) auto done

lemma memory_pop_frame [simp]:
  assumes "memory_\<alpha> x = X"
  assumes "memory_\<alpha> y = Y"
  shows "memory_\<alpha> (pop_frame x y) = (\<lambda>a. case a of saddr sa \<Rightarrow> if X a \<noteq> None then Y a else None | _ \<Rightarrow> Y a)"
  apply (rule ext) subgoal for a using assms by (cases a) auto done


lemma verify_even_odd:
  "verify_program even_odd_prog even_odd_annots"
  apply (vcg_verify_program prog: even_odd_prog_def annot: even_odd_annots_def)
  apply (unfold_first_label func: even_func_def)
    apply (unfold_first_label func: even_func_def)
    apply (intro allI impI)
  subgoal for s
    apply (vcg_floyd_cond prog: even_odd_prog_def func: even_func_def)
    apply clean_assms
    apply (vcg_steps_execi block: even_entry_def)
    apply vcg_steps_execi
    apply vcg_steps_execi
    apply vcg_steps_execi
    apply vcg_steps_execi
    apply vcg_steps_execi
    subgoal for n rva na s'
      apply (vcg_steps_flowi_branch prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_step prog: even_odd_prog_def func: even_func_def)
      apply (vcg_steps_execi block: even_if_def)
      apply vcg_steps_execi
      apply (vcg_steps_flowi_branch prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_step prog: even_odd_prog_def func: even_func_def)
      apply (vcg_steps_execi block: even_return_def)
      apply vcg_steps_execi
      apply (vcg_steps_flowi_return prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_annotation_holds prog: even_odd_prog_def annot: even_odd_annots_def pre: even_odd_annots_def)
      unfolding even_odd_prog_def
      by (auto split: if_splits)
    subgoal for n rva na s'
      apply (vcg_steps_flowi_branch prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_step prog: even_odd_prog_def func: even_func_def)
      apply (vcg_steps_execi block: even_else_def)
      apply (vcg_steps_execi)
      apply (vcg_steps_execi)
         apply (subst even_odd_prog_def)
         apply simp
        apply (unfold_first_label func: odd_func_def)
       apply (subst even_odd_annots_def)
       apply simp
      apply (simp only: prepare_state.simps)
      apply (subst odd_func_def)
      apply (simp (no_asm) del: assign_params.simps split_paired_All)
      apply (intro wp_assign_params_intro wp_assign_params_empty_intro) apply simp apply simp
      apply (intro conjI)
      apply (smt (verit, del_insts) add.inverse_neutral add_diff_cancel_right' diff_minus_eq_add fun_upd_same signed.nle_le signed_arith_eq_checks_to_ord(1) signed_minus_1
          word_sle_eq)
      apply (intro allI impI)
      apply (elim exE conjE)
      apply (rule wp_restore_state_intro)
        apply blast defer
       apply blast
      apply (intro wp_intro)
        apply fastforce defer
       apply blast
        apply (elim conjE)
  apply simp
  apply (hypsubst_thin)+
  apply (subst (asm) fun_upd_apply[symmetric])+
  apply clean_assms
      apply vcg_steps_execi
      apply vcg_steps_execi
      apply (vcg_steps_flowi_branch prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_step prog: even_odd_prog_def func: even_func_def)
      apply (vcg_steps_execi block: even_return_def)

      apply vcg_steps_execi
      apply (vcg_steps_flowi_return prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_annotation_holds prog: even_odd_prog_def annot: even_odd_annots_def pre: even_odd_annots_def)
      unfolding even_odd_prog_def apply (intro conjI) apply simp apply blast apply (auto split: if_splits)
      by fast
    done
  apply (unfold_first_label func: odd_func_def)
  apply (unfold_first_label func: odd_func_def)
  apply (intro allI impI)
  subgoal for s
    apply (vcg_floyd_cond prog: even_odd_prog_def func: odd_func_def)
    apply clean_assms
    apply (vcg_steps_execi block: odd_entry_def)
    apply vcg_steps_execi
    apply vcg_steps_execi
    apply vcg_steps_execi
         apply (subst even_odd_prog_def)
         apply simp
        apply (unfold_first_label func: even_func_def)
       apply (subst even_odd_annots_def)
       apply simp
      apply (simp only: prepare_state.simps)
      apply (subst even_func_def)
      apply (simp (no_asm) del: assign_params.simps split_paired_All)
      apply (intro wp_assign_params_intro wp_assign_params_empty_intro) apply simp apply simp
    apply (intro conjI)
     apply simp
      apply (intro allI impI)
      apply (elim exE conjE)
      apply (rule wp_restore_state_intro)
        apply blast defer
       apply blast
      apply (intro wp_intro)
        apply fastforce defer
       apply blast
        apply (elim conjE)
  apply simp
  apply (hypsubst_thin)+
  apply (subst (asm) fun_upd_apply[symmetric])+
  apply clean_assms
  apply vcg_steps_execi
  apply vcg_steps_execi
      apply (vcg_steps_flowi_return prog: even_odd_prog_def annot: even_odd_annots_def)
      apply (vcg_annotation_holds prog: even_odd_prog_def annot: even_odd_annots_def pre: even_odd_annots_def)
      unfolding even_odd_prog_def by (auto split: if_splits)
    done  


(*
define dso_local noundef zeroext i1 @odd(int)(i32 noundef %n) {
entry:
  %n.addr = alloca i32, align 4
  store i32 %n, ptr %n.addr, align 4
  %0 = load i32, ptr %n.addr, align 4
  %sub = sub nsw i32 %0, 1
  %call = call noundef zeroext i1 @even(int)(i32 noundef %sub)
  %lnot = xor i1 %call, true
  ret i1 %lnot
}

define dso_local noundef zeroext i1 @even(int)(i32 noundef %n) {
entry:
  %retval = alloca i1, align 1
  %n.addr = alloca i32, align 4
  store i32 %n, ptr %n.addr, align 4
  %0 = load i32, ptr %n.addr, align 4
  %cmp = icmp eq i32 %0, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:
  store i1 true, ptr %retval, align 1
  br label %return

if.else:
  %1 = load i32, ptr %n.addr, align 4
  %call = call noundef zeroext i1 @odd(int)(i32 noundef %1)
  %lnot = xor i1 %call, true
  store i1 %lnot, ptr %retval, align 1
  br label %return

return:
  %2 = load i1, ptr %retval, align 1
  ret i1 %2
}


*)

















end