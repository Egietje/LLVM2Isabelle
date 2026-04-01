theory ExamplePrograms
  imports "VCG" "HOL-Library.AList_Mapping"
begin

section "Simple Branching"

definition sbmain :: "llvm_instruction_block" where
  "sbmain = ([],[
    alloca ''1'' i32 (Some 4),
    alloca ''2'' i32 (Some 4),
    alloca ''3'' i32 (Some 4),
    alloca ''4'' i32 (Some 4),
    alloca ''5'' i32 (Some 4),
    store i32 (val (vi32 0)) (reg ''1'') (Some 4),
    store i32 (val (vi32 1)) (reg ''2'') (Some 4),
    store i32 (val (vi32 2)) (reg ''3'') (Some 4),
    load ''6'' i32 (reg ''2'') (Some 4),
    add ''7'' add_nsw i32 (reg ''6'') (val (vi32 1)),
    load ''8'' i32 (reg ''3'') (Some 4),
    icmp ''9'' False comp_eq i32 (reg ''7'') (reg ''8'')],
    br_i1 (reg ''9'') ''10'' ''12''
  )"

definition sb10 :: "llvm_instruction_block" where
  "sb10 = ([],[
    store i32 (val (vi32 3)) (reg ''4'') (Some 4),
    load ''11'' i32 (reg ''4'') (Some 4),
    store i32 (reg ''11'') (reg ''3'') (Some 4)],
    br_label ''14''
  )"

definition sb12 :: "llvm_instruction_block" where
  "sb12 = ([],[
    store i32 (val (vi32 4)) (reg ''5'') (Some 4),
    load ''13'' i32 (reg ''5'') (Some 4),
    store i32 (reg ''13'') (reg ''3'') (Some 4)],
    br_label ''14''
  )"

definition sb14 :: "llvm_instruction_block" where
  "sb14 = ([],[
    load ''15'' i32 (reg ''3'') (Some 4)],
    ret i32 (reg ''15'')
  )"

definition simple_branching_main :: "llvm_function" where
  "simple_branching_main = func (func_def ''main'' i32) [(''main'', sbmain), (''10'', sb10), (''12'', sb12), (''14'', sb14)]"

value "execute_function simple_branching_main empty_state"


lemma "verify_function (annotated
      simple_branching_main

      [
        (''14'', (\<lambda>s. \<exists>a v. register_\<alpha> s (reg ''3'') = Some (addr a) \<and> memory_\<alpha> s a = Some (Some (vi32 v)) \<and> (v = 4 \<or> v = 3)))
      ]

      (\<lambda>(v', s'). v' = vi32 3 \<or> v' = vi32 4)
    )"
  unfolding simple_branching_main_def sbmain_def sb10_def sb12_def sb14_def
  by vcg

section "Phi Node"

definition pmain :: "llvm_instruction_block" where
  "pmain = ([],[
    alloca ''1'' i32 (Some 4),
    alloca ''2'' i32 (Some 4),
    alloca ''3'' i32 (Some 4),
    alloca ''4'' i32 (Some 4),
    store i32 (val (vi32 0)) (reg ''1'') (Some 4),
    store i32 (val (vi32 1)) (reg ''2'') (Some 4),
    load ''5'' i32 (reg ''2'') (Some 4),
    icmp ''6'' False comp_ne i32 (reg ''5'') (val (vi32 0))],
    br_i1 (reg ''6'') ''7'' ''9''
  )"

definition p7 :: "llvm_instruction_block" where
  "p7 = ([],[
    store i32 (val (vi32 1)) (reg ''4'') (Some 4),
    load ''8'' i32 (reg ''4'') (Some 4)],
    br_label ''10''
  )"

definition p9 :: "llvm_instruction_block" where
  "p9 = ([],[],
    br_label ''10''
  )"

definition p10 :: "llvm_instruction_block" where
  "p10 = ([phi ''11'' i32 [(''7'', reg ''8''), (''9'', val (vi32 0))]],[
    store i32 (reg ''11'') (reg ''3'') (Some 4),
    load ''12'' i32 (reg ''3'') (Some 4)],
    ret i32 (reg ''12'')
  )"

definition phi_main :: "llvm_function" where
  "phi_main = func (func_def ''main'' i32) [(''main'', pmain), (''7'', p7), (''9'', p9), (''10'', p10)]"


lemma "verify_function (annotated
    phi_main

    [
      (''10'',  (\<lambda>s. \<exists>v a3. register_\<alpha> s (reg ''8'') = Some v \<and> register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 \<noteq> None))
    ]

    (\<lambda>(v, s). v = (the (register_\<alpha> s (reg ''8''))) \<or> v = vi32 0)
  )"
  unfolding phi_main_def pmain_def p7_def p9_def p10_def
  by vcg


(*
int main() {
    int y = 1;
    int x = y?1:0;
    return x;
}

define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  %5 = load i32, ptr %2, align 4
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %7, label %9

7:
  store i32 1, ptr %4, align 4
  %8 = load i32, ptr %4, align 4
  br label %10

9:
  br label %10

10:
  %11 = phi i32 [ %8, %9 ], [ 0, %9 ]
  store i32 %11, ptr %3, align 4
  %12 = load i32, ptr %3, align 4
  ret i32 %12
}
*)

value "execute_function phi_main empty_state"



section "Mult Function"

definition mult_entry :: "llvm_instruction_block" where
  "mult_entry = (
    [],
    [
      alloca ''a.addr'' i32 (Some 4),
      alloca ''b.addr'' i32 (Some 4),
      alloca ''result'' i32 (Some 4),
      alloca ''i'' i32 (Some 4),
      store i32 (reg ''a'') (reg ''a.addr'') (Some 4),
      store i32 (reg ''b'') (reg ''b.addr'') (Some 4),
      store i32 (val (vi32 0)) (reg ''result'') (Some 4),
      store i32 (val (vi32 0)) (reg ''i'') (Some 4)
    ],
    br_label ''for.cond''
  )"

definition mult_entry_pre where
  "mult_entry_pre = (\<lambda>s. \<exists>a b.
    register_\<alpha> s (reg ''a'') = (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b'') = (Some (vi32 b))
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
      load ''0'' i32 (reg ''i'') (Some 4),
      load ''1'' i32 (reg ''b.addr'') (Some 4),
      icmp ''cmp'' False comp_slt i32 (reg ''0'') (reg ''1'')
    ],
    br_i1 (reg ''cmp'') ''for.body'' ''for.end''
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
      load ''2'' i32 (reg ''a.addr'') (Some 4),
      load ''3'' i32 (reg ''result'') (Some 4),
      add ''add'' add_nsw i32 (reg ''3'') (reg ''2''),
      store i32 (reg ''add'') (reg ''result'') (Some 4)
    ],
    br_label ''for.inc''
  )"

definition mult_body_pre where
  "mult_body_pre = (\<lambda>s. \<exists>aa a ab b ai i ar.
    register_\<alpha> s (reg ''a'') = (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b'') = (Some (vi32 b))
  \<and> register_\<alpha> s (reg ''a.addr'') = Some (addr aa) \<and> memory_\<alpha> s aa = Some (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b.addr'') = Some (addr ab) \<and> memory_\<alpha> s ab = Some (Some (vi32 b))
  \<and> register_\<alpha> s (reg ''i'') = Some (addr ai) \<and> memory_\<alpha> s ai = Some (Some (vi32 i))
  \<and> register_\<alpha> s (reg ''result'') = Some (addr ar) \<and> memory_\<alpha> s ar = Some (Some (vi32 (a * i)))
  \<and> - (2 ^ 31) \<le>s a * b
  \<and> a * b <s 2 ^ 31
  \<and> 0 <s b
  \<and> 0 \<le>s i
  \<and> i <s b
  \<and> i <s 2 ^ 31 - 1
  \<and> aa \<noteq> ab
  \<and> aa \<noteq> ai
  \<and> aa \<noteq> ar
  \<and> ab \<noteq> ai
  \<and> ab \<noteq> ar
  \<and> ai \<noteq> ar
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
      load ''4'' i32 (reg ''i'') (Some 4),
      add ''inc'' add_nsw i32 (reg ''4'') (val (vi32 1)),
      store i32 (reg ''inc'') (reg ''i'') (Some 4)
    ],
    br_label ''for.cond''
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
      load ''5'' i32 (reg ''result'') (Some 4)
    ],
    ret i32 (reg ''5'')
  )"

definition mult_end_pre where
  "mult_end_pre = (\<lambda>s. \<exists>aa a ab b ai i ar.
    register_\<alpha> s (reg ''a'') = (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b'') = (Some (vi32 b))
  \<and> register_\<alpha> s (reg ''a.addr'') = Some (addr aa) \<and> memory_\<alpha> s aa = Some (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b.addr'') = Some (addr ab) \<and> memory_\<alpha> s ab = Some (Some (vi32 b))
  \<and> register_\<alpha> s (reg ''i'') = Some (addr ai) \<and> memory_\<alpha> s ai = Some (Some (vi32 i))
  \<and> register_\<alpha> s (reg ''result'') = Some (addr ar) \<and> memory_\<alpha> s ar = Some (Some (vi32 (a * i)))
  \<and> - (2 ^ 31) \<le>s a * b
  \<and> a * b <s 2 ^ 31
  \<and> 0 <s b
  \<and> i = b
  \<and> aa \<noteq> ab
  \<and> aa \<noteq> ai
  \<and> aa \<noteq> ar
  \<and> ab \<noteq> ai
  \<and> ab \<noteq> ar
  \<and> ai \<noteq> ar
  )"

definition mult_post where
  "mult_post = (\<lambda>(r, s). \<exists>a b.
    register_\<alpha> s (reg ''a'') = (Some (vi32 a))
  \<and> register_\<alpha> s (reg ''b'') = (Some (vi32 b))
  \<and> r = vi32 (a * b)
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
      (''entry'',    mult_entry),
      (''for.cond'', mult_cond),
      (''for.body'', mult_body),
      (''for.inc'',  mult_inc),
      (''for.end'',  mult_end)
    ]
  )"

definition mult_annotated :: annotated_function where
  "mult_annotated = annotated
    mult_function
    [
      (''entry'', mult_entry_pre),
      (''for.body'', mult_body_pre),
      (''for.end'', mult_end_pre)
    ]
    mult_post"


lemma "verify_function mult_annotated"
  unfolding mult_annotated_def mult_function_def mult_entry_def mult_cond_def mult_body_def mult_inc_def mult_end_def mult_entry_pre_def mult_body_pre_def mult_end_pre_def mult_post_def
  by vcg

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