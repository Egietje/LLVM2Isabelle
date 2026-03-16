theory VCG
  imports "Blocks"
begin

section "Hoare definition"

definition hoare :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare P c Q \<equiv> (\<forall>x. P x \<longrightarrow> wp (c x) Q)"

lemma hoare_intro:
  assumes "\<And>s. P s \<Longrightarrow> wp (c s) Q"
  shows "hoare P c Q"
  using assms
  unfolding hoare_def
  by simp



section "Useful Lemmas"

lemma contract_updates:
  assumes "f s'' = (f s)(r1 := v1, r2 := v2) \<Longrightarrow> P"
  shows "f s' = (f s)(r1 := v1) \<Longrightarrow> f s'' = (f s')(r2 := v2) \<Longrightarrow> P"
  using assms
  by simp

lemma False_eq_False:
  assumes "False"
  shows "False"
  by (rule assms)



section "VCG Methods"


subsection "Clean Assumptions"

method repeat_minus_one methods m =
  ((m; succeeds m; repeat_minus_one m) | succeed)

method thin_tac_reg = thin_tac "register_\<alpha> _ = _"
method clean_registers = repeat_minus_one thin_tac_reg

method thin_tac_mem = thin_tac "memory_\<alpha> _ = _"
method clean_memory = repeat_minus_one thin_tac_mem

method clean_assms = ((elim exE conjE)+)?, (simp only: contract_updates)?; clean_registers?; clean_memory?; (simp only: triv_forall_equality)?


subsection "Specific Subgoal Methods"

method instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"]; simp
method memory_allocated = rule asm_rl[of "memory_\<alpha> _ _ \<noteq> None"]; simp
method register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"]; simp
method memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (Some _)"]; simp split: if_splits
method add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]); eval
method icmp_same_signs = rule asm_rl[of "if _ then same_signs _ _ else True"]; eval
method map_of_some = rule asm_rl[of "map_of _ _ = Some _"]; simp
method distinct_first = rule asm_rl[of "distinct (map fst _)"]; eval
method some_refl = rule asm_rl[of "Some _ = Some _"]; rule refl


subsection "Instruction Methods"

method strat_instr methods m = rule wp_intro, m, clean_assms; (simp only: False_eq_False)?

method strat_alloca = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr -
method strat_store  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr \<open>instantiate_register_address, memory_allocated, register_value\<close>
method strat_load   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr \<open>instantiate_register_address, memory_value\<close>
method strat_add    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr \<open>register_value, register_value, add_poison\<close>
method strat_icmp   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr \<open>register_value, register_value, icmp_same_signs\<close>; simp only: compare_values_32.simps compare_values_64.simps

method unfold_block_instr = rule asm_rl[of "wp (execute_block _ ([], _#_, _) _) _"], rule wp_intro
method unfold_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_intro

method instr_vcg = (unfold_block_instr | unfold_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp)+


subsection "Phi Node Methods"

method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _ _) _"], strat_instr \<open>distinct_first, some_refl, map_of_some, register_value\<close>

method unfold_block_phi = rule asm_rl[of "wp (execute_block _ (_#_, _, _) _) _"], rule wp_intro

method phi_vcg = (unfold_block_phi | strat_phi)+


subsection "Terminal Instruction Methods"

method strat_branch_i1 = rule asm_rl[of "wp (execute_block _ ([], [], br_i1 _ _ _) _ ) _"], (rule wp_intro, register_value); (simp only: False_eq_False)?
method strat_branch_label = rule asm_rl[of "wp (execute_block _ ([], [], br_label _) _ ) _"], rule wp_intro; (simp only: False_eq_False)?
method strat_return = rule asm_rl[of "wp (execute_block _ ([], [], ret _ _) _ ) _"], (rule wp_intro, register_value); (simp only: False_eq_False)?

method term_vcg = strat_branch_i1 | strat_branch_label | strat_return


subsection "VCG Method"

method vcg = rule hoare_intro, phi_vcg?, instr_vcg?, term_vcg?

end