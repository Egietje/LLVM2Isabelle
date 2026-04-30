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
  \<and> - (2 ^ 31) \<le> sint a * sint b
  \<and> sint a * sint b \<le> 2 ^ 31 - 1
  \<and> 0 <s b
  \<and> b \<le>s 2 ^ 31 - 1
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
  \<and> register_contains_value (lid ''b'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''a.addr'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''b.addr'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''i'') (vi32 i) s
  \<and> register_contains_address_with_value (lid ''result'') (vi32 (a * i)) s
  \<and> registers_contain_unique_addresses [lid ''a.addr'', lid ''b.addr'', lid ''i'', lid ''result''] s
  \<and> - (2 ^ 31) \<le> sint a * sint b
  \<and> sint a * sint b \<le> 2 ^ 31 - 1
  \<and> 0 <s b
  \<and> 0 \<le>s i
  \<and> i <s b
  \<and> b \<le>s 2 ^ 31 - 1
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
  \<and> register_contains_value (lid ''b'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''a.addr'') (vi32 a) s
  \<and> register_contains_address_with_value (lid ''b.addr'') (vi32 b) s
  \<and> register_contains_address_with_value (lid ''i'') (vi32 i) s
  \<and> register_contains_address_with_value (lid ''result'') (vi32 (a * i)) s
  \<and> registers_contain_unique_addresses [lid ''a.addr'', lid ''b.addr'', lid ''i'', lid ''result''] s
  \<and> - (2 ^ 31) \<le> sint a * sint b
  \<and> sint a * sint b \<le> 2 ^ 31 - 1
  \<and> 0 <s b
  \<and> 0 \<le>s i
  \<and> i <s 2 ^ 31 - 1
  \<and> i = b
  )"

definition mult_post :: "postcondition" where
  "mult_post = (\<lambda>s v. \<exists>a b.
    register_contains_value (lid ''a'') (vi32 a) s
  \<and> register_contains_value (lid ''b'') (vi32 b) s
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

method unfold_floyd_vc uses defs =
  rule asm_rl[of "floyd_vc _ _ _"],
  rule floyd_vc_intro,
  unfold defs,
  (unfold first_label_def; simp; fail)?,
  simp only: predicate_for_all.simps HOL.simp_thms(21),
  (intro conjI allI impI; unfold annotation_holds_def has_annotation_def; simp; unfold floyd_cond_def)

method instantiate_block_def =
  rule asm_rl[of "map_of _ _ = Some _"],
  force

method unfold_wp_step =
  rule asm_rl[of "wp_step _ _ _"],
  rule wp_step_intro,
  instantiate_block_def

method unfold_wp_annotated_step =
  rule asm_rl[of "wp_annotated_step _ _ _ _"],
  rule wp_annotated_step_intro,
  unfold_wp_step


method unfold_endgoal =
  rule asm_rl[of "annotation_holds _ _ _"],
  unfold annotation_holds_def,
  simp (no_asm)


method unfold_wp_steps_until =
  rule asm_rl[of "wp_steps_until _ _ _ _"],
  rule wp_steps_until_intro;
  (unfold has_annotation_def; force; fail)?;
  (thin_tac "\<not>has_annotation _ _" | thin_tac "has_annotation _ _")?;
  (unfold_wp_step | unfold_endgoal)?


lemma i_no_overflow_impl_positive: "0 \<le>s i \<Longrightarrow> (i::word32) <s 2^31 - 1 \<Longrightarrow> 0 \<le>s (i+1)"
  sorry


lemma
  "floyd_vc
    mult_function
    [
      ((None, lid ''entry''),   mult_pre),
      ((Some (lid ''for.cond''), lid ''for.body''),mult_body_pre),
      ((Some (lid ''for.cond''), lid ''for.end''), mult_end_pre)
    ]
    mult_post"
  apply (unfold_floyd_vc defs: mult_function_def)

  subgoal (* entry \<rightarrow> cond \<rightarrow> body *)
    apply (unfold_wp_annotated_step)
    apply (block_vcg defs: mult_entry_def mult_pre_def)
    apply (unfold_wp_steps_until)
    apply (block_vcg defs: mult_cond_def)
    apply (unfold_wp_steps_until)
    apply (unfold mult_body_pre_def)
    apply (unfold_shorthands)
    apply (intro conjI exI) apply auto by (auto split: if_splits)

  subgoal for s (* body \<rightarrow> inc \<rightarrow> cond \<rightarrow> body or end *)
    apply (unfold_wp_annotated_step)
    apply (block_vcg_dbg defs: mult_body_def mult_body_pre_def)
    subgoal sorry
    subgoal sorry
    apply (block_vcg)
    apply (unfold_wp_steps_until)
    apply (block_vcg_dbg defs: mult_inc_def)
    subgoal sorry
    apply block_vcg
    apply (unfold_wp_steps_until)
    apply (block_vcg defs: mult_cond_def)
    subgoal
      apply (rule wp_steps_until_intro)
      defer
      unfolding has_annotation_def apply simp
      unfolding annotation_holds_def
      apply (simp (no_asm)) 
      apply (rule exI) apply (intro conjI) apply simp
      apply (rule exI) apply (intro conjI) apply simp apply simp apply simp
      apply (rule exI) apply (rule conjI, simp)+
      apply (metis distrib_left mult.right_neutral) apply (rule conjI, simp)+ using i_no_overflow_impl_positive by auto
    subgoal for a b i aa ab ac ad ae af ag ah ai aj ak al am an 
      apply (rule wp_steps_until_intro)
      defer
      unfolding has_annotation_def apply simp
      unfolding annotation_holds_def
      apply (simp (no_asm)) unfolding mult_end_pre_def apply unfold_shorthands
      apply (rule exI | rule conjI, simp)+
       apply (metis distrib_left mult.right_neutral) apply (rule conjI, simp)+
      subgoal sorry
      subgoal sorry
      done
    done

  subgoal (* end \<rightarrow> return *)
    apply (unfold_wp_annotated_step)
    apply (block_vcg defs: mult_end_def mult_end_pre_def)
    apply (unfold_wp_steps_until)
    unfolding mult_post_def
    apply unfold_shorthands
    by fastforce

  done



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