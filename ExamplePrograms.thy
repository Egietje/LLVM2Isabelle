theory ExamplePrograms
  imports "Blocks" "HOL-Library.AList_Mapping" "Hoare"
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


lemma alloc_fresh_simp: "(if a=b then Some x else y) = None \<longleftrightarrow> a\<noteq>b \<and> y = None"
  by (auto split: if_split)

method repeat_minus_one methods m =
  ((m; succeeds m; repeat_minus_one m) | succeed)

method thin_tac_reg = thin_tac "register_\<alpha> _ = _"
method clean_registers = repeat_minus_one thin_tac_reg

method thin_tac_mem = thin_tac "memory_\<alpha> _ = _"
method clean_memory = repeat_minus_one thin_tac_mem

method hoare_init = rule hoare_intro

lemma contract_updates:
  assumes "f s'' = (f s)(r1 := v1, r2 := v2) \<Longrightarrow> P"
  shows "f s' = (f s)(r1 := v1) \<Longrightarrow> f s'' = (f s')(r2 := v2) \<Longrightarrow> P"
  using assms
  by simp

lemma False_eq_False:
  assumes "False"
  shows "False"
  by (rule assms)


method clean_assms = ((elim exE conjE)+)?, (simp only: contract_updates)?; clean_registers?; clean_memory?; (simp only: triv_forall_equality)?

method strat_instr methods m = rule wp_intro, m, clean_assms; (simp only: False_eq_False)?

method instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"]; simp
method memory_allocated = rule asm_rl[of "memory_\<alpha> _ _ \<noteq> None"]; simp
method register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"]; simp
method memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (Some _)"]; simp split: if_splits
method add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]); eval
method icmp_same_signs = rule asm_rl[of "if _ then same_signs _ _ else True"]; eval
method map_of_some = rule asm_rl[of "map_of _ _ = Some _"]; simp
method distinct_first = rule asm_rl[of "distinct (map fst _)"]; eval
method some_refl = rule asm_rl[of "Some _ = Some _"]; rule refl

method three_simps = simp, simp, simp

method strat_alloca = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr -
method strat_store  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr \<open>instantiate_register_address, memory_allocated, register_value\<close>
method strat_load   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr \<open>instantiate_register_address, memory_value\<close>
method strat_add    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr \<open>register_value, register_value, add_poison\<close>
method strat_icmp   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr \<open>register_value, register_value, icmp_same_signs\<close>; simp only: compare_values_32.simps compare_values_64.simps

method strat_branch_i1 = rule asm_rl[of "wp (execute_block _ ([], [], br_i1 _ _ _) _ ) _"], (rule wp_intro, register_value); (simp only: False_eq_False)?
method strat_branch_label = rule asm_rl[of "wp (execute_block _ ([], [], br_label _) _ ) _"], rule wp_intro; (simp only: False_eq_False)?
method strat_return = rule asm_rl[of "wp (execute_block _ ([], [], ret _ _) _ ) _"], (rule wp_intro, register_value); (simp only: False_eq_False)?

method unfold_execute_block_phi = rule asm_rl[of "wp (execute_block _ (_#_, _, _) _) _"], rule wp_intro
method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _ _) _"], strat_instr \<open>distinct_first, some_refl, map_of_some, register_value\<close>

method unfold_execute_block_instr = rule asm_rl[of "wp (execute_block _ ([], _#_, _) _) _"], rule wp_intro
method unfold_execute_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_intro

method phi_vcg = (unfold_execute_block_phi | strat_phi)+
method instr_vcg = (unfold_execute_block_instr | unfold_execute_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp)+
method term_vcg = strat_branch_i1 | strat_branch_label | strat_return

method vcg = hoare_init, phi_vcg?, instr_vcg?, term_vcg?

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