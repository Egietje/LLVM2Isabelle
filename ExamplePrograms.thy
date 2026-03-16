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
  "simple_branching_main = func (func_def ''main'' i32) sbmain [(''10'', sb10), (''12'', sb12), (''14'', sb14)]"

lemma hoare_sbmain:
  "hoare

    (\<lambda>_. True)

    (execute_block p sbmain)

    (\<lambda>(s', r).
      r = branch_label ''10''
    \<and> (\<exists>a. register_\<alpha> s' (reg ''3'') = Some (addr a) \<and> memory_\<alpha> s' a \<noteq> None)
    \<and> (\<exists>a. register_\<alpha> s' (reg ''4'') = Some (addr a) \<and> memory_\<alpha> s' a \<noteq> None)
    \<and> (\<exists>a. register_\<alpha> s' (reg ''5'') = Some (addr a) \<and> memory_\<alpha> s' a \<noteq> None)
    )"
  unfolding sbmain_def
  apply vcg
  by auto

lemma hoare_sb10:
  "hoare

    (\<lambda>s.
      register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 \<noteq> None
    \<and> register_\<alpha> s (reg ''4'') = Some (addr a4) \<and> memory_\<alpha> s a4 \<noteq> None
    )

    (execute_block p sb10)

    (\<lambda>(s', r).
      register_\<alpha> s' (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s' a3 = Some (Some (vi32 3))
    \<and> r = branch_label ''14''
    )"
  unfolding sb10_def
  apply vcg
  by auto

lemma hoare_sb12:
  "hoare

    (\<lambda>s.
      (register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 \<noteq> None)
    \<and> (register_\<alpha> s (reg ''5'') = Some (addr a5) \<and> memory_\<alpha> s a5 \<noteq> None)
    )

    (execute_block p sb12)

    (\<lambda>(s', r).
      (register_\<alpha> s' (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s' a3 = Some (Some (vi32 4)))
    \<and> r = branch_label ''14''
    )"
  unfolding sb12_def
  apply vcg
  by auto

lemma hoare_sb14:
  "hoare

    (\<lambda>s. register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 = Some (Some v))

    (execute_block p sb14)

    (\<lambda>(s', r). r = return_value v)"
  unfolding sb14_def
  apply vcg
  by auto

value "execute_function simple_branching_main empty_state"


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
  "phi_main = func (func_def ''main'' i32) pmain [(''7'', p7), (''9'', p9), (''10'', p10)]"


lemma hoare_pmain:
  "hoare

  (\<lambda>_. True)

  (execute_block p pmain)

  (\<lambda>(s', r). Q)"
  unfolding pmain_def
  apply vcg
  oops

lemma hoare_p7:
  "hoare

  (\<lambda>s. (register_\<alpha> s (reg ''4'') = Some (addr a4) \<and> memory_\<alpha> s a4 \<noteq> None))

  (execute_block p p7)

  (\<lambda>(s', r). r = branch_label ''10'' \<and> (\<exists>a. register_\<alpha> s' (reg ''8'') = Some (vi32 1)))"
  unfolding p7_def
  apply vcg
  by auto

lemma hoare_p9:
  "hoare

  (\<lambda>s. True)

  (execute_block p p9)

  (\<lambda>(s', r). r = branch_label ''10'')"
  unfolding p9_def
  apply vcg
  by auto

lemma hoare_p10_7:
  "hoare

  (\<lambda>s. register_\<alpha> s (reg ''8'') = Some v \<and> register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 \<noteq> None)

  (execute_block (Some ''7'') p10)

  (\<lambda>(s', r). r = return_value v)"
  unfolding p10_def
  apply vcg
  by auto

lemma hoare_p10_9:
  "hoare

  (\<lambda>s. register_\<alpha> s (reg ''3'') = Some (addr a3) \<and> memory_\<alpha> s a3 \<noteq> None)

  (execute_block (Some ''9'') p10)

  (\<lambda>(s', r). r = return_value (vi32 0))"
  unfolding p10_def
  apply vcg
  by auto


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

end