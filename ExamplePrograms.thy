theory ExamplePrograms
  imports "VCG" "HOL-Library.AList_Mapping"
begin

section "Mult Function"

definition mult_entry :: "llvm_instruction_block" where
  "mult_entry = (
    [],
    [
      alloca (lid ''a.addr'') i32 (Some 4),
      alloca (lid ''b.addr'') i32 (Some 4),
      alloca (lid ''result'') i32 (Some 4),
      alloca (lid ''i'') i32 (Some 4),
      store i32 (reg (lid ''a'')) (reg (lid ''a.addr'')) (Some 4),
      store i32 (reg (lid ''b'')) (reg (lid ''b.addr'')) (Some 4),
      store i32 (val (vi32 0)) (reg (lid ''result'')) (Some 4),
      store i32 (val (vi32 0)) (reg (lid ''i'')) (Some 4)
    ],
    br_label (lid ''for.cond'')
  )"


definition mult_pre :: "precondition" where
  "mult_pre = (\<lambda>s. \<exists>a b.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 b) s
  \<and> - (2 ^ 31) \<le>s a * b
  \<and> a * b <s 2 ^ 31
  \<and> 0 <s b
  )"

(*
2 entry:
3 %a.addr = alloca i32, align 4
4 %b.addr = alloca i32, align 4
5 %result = alloca i32, align 4
6 %i = alloca i32, align 4
7 store i32 %a, ptr %a.addr, align 4
8 store i32 %b, ptr %b.addr, align 4
9 store i32 0, ptr %result, align 4
10 store i32 0, ptr %i, align 4
11 br label %for.cond
*)


definition mult_cond :: "llvm_instruction_block" where
  "mult_cond = (
    [],
    [
      load (lid ''0'') i32 (reg (lid ''i'')) (Some 4),
      load (lid ''1'') i32 (reg (lid ''b.addr'')) (Some 4),
      icmp (lid ''cmp'') False comp_slt i32 (reg (lid ''0'')) (reg (lid ''1''))
    ],
    br_i1 (reg (lid ''cmp'')) (lid ''for.body'') (lid ''for.end'')
  )"

(*
13 for.cond:
14 %0 = load i32, ptr %i, align 4
15 %1 = load i32, ptr %b.addr, align 4
16 %cmp = icmp slt i32 %0, %1
17 br i1 %cmp, label %for.body, label %for.end
*)


definition mult_body :: "llvm_instruction_block" where
  "mult_body = (
    [],
    [
      load (lid ''2'') i32 (reg (lid ''a.addr'')) (Some 4),
      load (lid ''3'') i32 (reg (lid ''result'')) (Some 4),
      add (lid ''add'') add_nsw i32 (reg (lid ''3'')) (reg (lid ''2'')),
      store i32 (reg (lid ''add'')) (reg (lid ''result'')) (Some 4)
    ],
    br_label (lid ''for.inc'')
  )"

definition mult_body_pre :: "precondition" where
  "mult_body_pre = (\<lambda>s. \<exists>a b i.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''a.addr'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''b.addr'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''i'') (vi32 i) s
  \<and> register_contains_address_with_value (lid ''result'') (vi32 (a * i)) s
  \<and> registers_contain_unique_addresses [lid ''a.addr'', lid ''b.addr'', lid ''i'', lid ''result''] s
  \<and> - (2 ^ 31) \<le>s a * b
  \<and> a * b <s 2 ^ 31
  \<and> 0 <s b
  \<and> 0 \<le>s i
  \<and> i <s b
  \<and> i <s 2 ^ 31 - 1
  )"

(*
19 for.body:
20 %2 = load i32, ptr %a.addr, align 4
21 %3 = load i32, ptr %result, align 4
22 %add = add nsw i32 %3, %2
23 store i32 %add, ptr %result, align 4
24 br label %for.inc
*)


definition mult_inc :: "llvm_instruction_block" where
  "mult_inc = (
    [],
    [
      load (lid ''4'') i32 (reg (lid ''i'')) (Some 4),
      add (lid ''inc'') add_nsw i32 (reg (lid ''4'')) (val (vi32 1)),
      store i32 (reg (lid ''inc'')) (reg (lid ''i'')) (Some 4)
    ],
    br_label (lid ''for.cond'')
  )"


(*
26 for.inc:
27 %4 = load i32, ptr %i, align 4
28 %inc = add nsw i32 %4, 1
29 store i32 %inc, ptr %i, align 4
30 br label %for.cond
*)


definition mult_end :: "llvm_instruction_block" where
  "mult_end = (
    [],
    [
      load (lid ''5'') i32 (reg (lid ''result'')) (Some 4)
    ],
    ret i32 (reg (lid ''5''))
  )"

definition mult_end_pre :: "precondition" where
  "mult_end_pre = (\<lambda>s. \<exists>a b i.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''a.addr'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''b.addr'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''i'') (vi32 i) s
  \<and> register_contains_address_with_value (lid ''result'') (vi32 (a * i)) s
  \<and> registers_contain_unique_addresses [lid ''a.addr'', lid ''b.addr'', lid ''i'', lid ''result''] s
  \<and> - (2 ^ 31) \<le>s a * b
  \<and> a * b <s 2 ^ 31
  \<and> 0 <s b
  \<and> i = b
  )"

definition mult_post :: "postcondition" where
  "mult_post = (\<lambda>s v. \<exists>a b.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 a) s
  \<and> v = Some (vi32 (a * b))
  )"

(*
32 for.end:
33 %5 = load i32, ptr %result, align 4
34 ret i32 %5
*)


definition mult_function :: llvm_function where
  "mult_function = (func
    (func_def ''mult'' i32) 
    [
      (lid ''entry'',    mult_entry),
      (lid ''for.cond'', mult_cond),
      (lid ''for.body'', mult_body),
      (lid ''for.inc'',  mult_inc),
      (lid ''for.end'',  mult_end)
    ]
  )"


(*
method wipe_assumptions = ((thin_tac "_ = _")+)?, ((thin_tac "register_contains_value _ _ _")+)?, ((thin_tac "_ <s _")+)?, ((thin_tac "_ \<le>s _")+)?
method vcg_verify_function = rule asm_rl[of "verify_function _ _ _ _"], unfold verify_function_def, unfold first_label_def, intro allI impI, elim conjE
method vcg_wp_steps = rule asm_rl[of "wp_steps _ _ _"], rule wp_steps_intro, blast, simp
method vcg_block uses defs = unfold defs, block_vcg, unfold wp_steps_intro_post_def create_pres_def, simp (no_asm)
*)



lemma
  "floyd_vc
    mult_function
    [
      ((None, lid ''entry''),   mult_pre),
      ((Some (lid ''for.cond''), lid ''for.body''),mult_body_pre),
      ((Some (lid ''for.cond''), lid ''for.end''), mult_end_pre)
    ]
    mult_post"
  unfolding mult_function_def
  apply (rule floyd_vc_intro)
    subgoal
      unfolding first_label_def
      by simp
  apply (simp only: predicate_for_all.simps HOL.simp_thms(21))
    apply (intro conjI allI impI; unfold annotation_holds_def has_annotation_def; simp; unfold floyd_cond_def)
      apply (rule wp_annotated_step_intro)
      apply (rule wp_step_intro) apply force
    unfolding mult_entry_def 
      apply (intro wp_intro)
    subgoal for s
  apply vcg_verify_function
  apply vcg_wp_steps
  apply (vcg_block defs: mult_entry_def mult_pre_def)
  apply vcg_wp_steps
  apply (vcg_block defs: mult_cond_def)
  apply (simp only: if_True)
  apply (intro conjI)
  subgoal unfolding mult_body_pre_def by attempt_endgoal
  apply wipe_assumptions
  apply auto
  apply (unfold mult_body_pre_def)
  apply clean_assms
  apply (rule wp_steps_intro) apply blast apply simp
  unfolding mult_body_def apply block_vcg
  apply (rule wp_intro) apply unfold_shorthands apply clean_assms oops
  
  

                 
lemma "verify_function mult_annotated"
  unfolding mult_annotated_def mult_function_def mult_entry_def mult_cond_def mult_body_def mult_inc_def mult_end_def mult_entry_pre_def mult_body_pre_def mult_end_pre_def mult_post_def
  apply vcg_step (* split into annotated branch-points with proper previous block: entry, for.cond \<rightarrow> for.body, for.cond \<rightarrow> for.end *)
  apply vcg_step (* turn into hoare triple *)
  apply vcg_step (* hoare triple of single block with complex post-condition *)
  apply vcg_step (* wp with pre-condition as assumption *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* finish block execution, branch *)
  apply vcg_step (* case distinction *)
  apply vcg_step (* branched to basic block without annotation \<rightarrow> new hoare triple *)
  apply vcg_step (* hoare triple of single block w/ complex post-condition*)
  apply vcg_step (* wp... *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* end of block, branch based on boolean*)
  apply vcg_step (* case distinction *)
  apply vcg_step (* branched on boolean, undeterminate, so we get extra subgoal for each case: 0 <s a and \<not>0 <s a *)
  (* first subgoal assumes 0 <s a, in which case we branch to for.body, which has a pre-condition we can prove *)
  apply vcg_step (* second subgoal assumed \<not>0 <s a, branch to for.end, which also has a pre-condition we can prove*)
  apply vcg_step (* _all_ executions starting from block entry with its pre-condition holding have been proven*)
  (*continue with execution from for.body*)
  apply vcg_step (* hoare triple with the pre-condition of for.body, executing starting from for.body, with for.cond as previous block *)
  apply vcg_step (* hoare of single block *)
  apply vcg_step (* wp *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* end of block, unconditional branch to for.inc *)
  apply vcg_step (* cases *)
  apply vcg_step (* for.inc has no pre-cond \<rightarrow> new hoare triple *)
  apply vcg_step (* hoare over single block *)
  apply vcg_step (* wp... *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* end of block, unconditional branch to for.cond *)
  apply vcg_step (* cases *)
  apply vcg_step (* for.cond has no pre-cond \<rightarrow> new hoare triple *)
  apply vcg_step (* hoare over single block *)
  apply vcg_step (* wp... *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* conditional branch to for.body or for.end depending on i+1 <s b *)
  apply vcg_step
  apply vcg_step (* new subgoals, one assumes i+1 <s b, branch to for.body which has pre-condition to prove *)
  apply vcg_step (* other assumes \<not>i+1 <s b, branch to for.end, pre-condition to prove *)
  apply vcg_step (* again, all executions starting from for.body have been proven to satisfy all following pre-conditions*)
  (* only execution from for.end remains *)
  apply vcg_step (* hoare triple from for.end with its pre-cond *)
  apply vcg_step (* hoare over single block *)
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step (* end of block, return value from reg %5*)
  apply vcg_step (* cases *)
  apply vcg_step (* return val, so show the post-condition of the function holds for that value *)
  apply vcg_step (* done! all possible executions satisfying the pre-condition of the function have been verified *)
  done

lemma "verify_function mult_annotated"
  unfolding mult_annotated_def mult_function_def 
  apply vcg_step apply simp
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step unfolding mult_entry_pre_def
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step apply simp unfolding register_contains_value_def
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step unfolding mult_body_pre_def
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step
  apply vcg_step

(*
1 define dso_local noundef i32 @mult(int, int)(i32 noundef %a, i32 noundef %b) { llvm
2 entry:
3 %a.addr = alloca i32, align 4
4 %b.addr = alloca i32, align 4
5 %result = alloca i32, align 4
6 %i = alloca i32, align 4
7 store i32 %a, ptr %a.addr, align 4
8 store i32 %b, ptr %b.addr, align 4
9 store i32 0, ptr %result, align 4
10 store i32 0, ptr %i, align 4
11 br label %for.cond
12
13 for.cond:
14 %0 = load i32, ptr %i, align 4
15 %1 = load i32, ptr %b.addr, align 4
16 %cmp = icmp slt i32 %0, %1
17 br i1 %cmp, label %for.body, label %for.end
18
19 for.body:
20 %2 = load i32, ptr %a.addr, align 4
21 %3 = load i32, ptr %result, align 4
22 %add = add nsw i32 %3, %2
23 store i32 %add, ptr %result, align 4
24 br label %for.inc
25
26 for.inc:
27 %4 = load i32, ptr %i, align 4
28 %inc = add nsw i32 %4, 1
29 store i32 %inc, ptr %i, align 4
30 br label %for.cond
31
32 for.end:
33 %5 = load i32, ptr %result, align 4
34 ret i32 %5
35 }
*)


end