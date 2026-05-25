theory VCG
  imports "Steps" "HOL-Eisbach.Eisbach"
begin

section "Useful Shorthands"

abbreviation register_contains_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_value n v s \<equiv> register_\<alpha> s (reg n) = Some v"

abbreviation register_contains_allocated_address :: "llvm_identifier \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_allocated_address n s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a \<noteq> None"

abbreviation register_contains_address_with_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_address_with_value n v s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a = Some (Some v)"

fun unique_address :: "llvm_address \<Rightarrow> llvm_address list \<Rightarrow> bool" where
  "unique_address ad (a#as) = ((ad \<noteq> a) \<and> unique_address ad as)"
| "unique_address _ [] = True"

fun unique_addresses :: "llvm_address list \<Rightarrow> bool" where
  "unique_addresses (a#as) = (unique_address a as \<and> unique_addresses as)"
| "unique_addresses [] = True"

fun unique_addresses_rec :: "llvm_identifier list \<Rightarrow> state \<Rightarrow> llvm_address list \<Rightarrow> bool" where
  "unique_addresses_rec (n#ns) s as = (\<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> unique_addresses_rec ns s (a#as))"
| "unique_addresses_rec []     _ as = unique_addresses as"

fun registers_contain_unique_addresses :: "llvm_identifier list \<Rightarrow> state \<Rightarrow> bool" where
  "registers_contain_unique_addresses ns s = unique_addresses_rec ns s []"



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

method clean_registers = repeat_minus_one \<open>thin_tac "register_\<alpha> _ = _"\<close>
method clean_memory = repeat_minus_one \<open>thin_tac "memory_\<alpha> _ = _"\<close>

method clean_assms = ((elim exE conjE)+)?, (simp only: contract_updates)?; clean_registers?; clean_memory?; (simp only: triv_forall_equality)?

method unfold_unique_addresses = simp only: registers_contain_unique_addresses.simps unique_addresses.simps unique_addresses_rec.simps unique_address.simps HOL.simp_thms(21), clean_assms

subsection "Subgoal Solving Methods"

method sub_instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"], (fastforce | simp)?; fail
method sub_memory_allocated = rule asm_rl[of "memory_\<alpha> _ _ \<noteq> None"], (fastforce | simp)?; fail
method sub_register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"], (fastforce | simp)?; fail
method sub_memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (Some _)"], (fastforce | simp split: if_splits)?; fail
method sub_add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]), (fastforce | simp split: if_splits add: word_sless_alt word_sle_eq)?; fail
method sub_icmp_same_signs = (rule asm_rl[of "if _ then same_signs32 _ _ else True"] | rule asm_rl[of "if _ then same_signs64 _ _ else True"]), (fastforce | simp split: if_splits add: word_sless_alt word_sle_eq)?; fail
method sub_map_of_some = rule asm_rl[of "map_of _ _ = Some _"], (fastforce | simp)?; fail
method sub_distinct_first = rule asm_rl[of "distinct (map fst _)"], (fastforce | simp)?; fail
method sub_some_refl = rule asm_rl[of "Some _ = Some _"], (rule refl)?; fail

method solve_subgoal = sub_instantiate_register_address | sub_memory_allocated | sub_register_value
                     | sub_memory_value | sub_add_poison | sub_icmp_same_signs | sub_map_of_some
                     | sub_distinct_first | sub_some_refl


subsection "Instruction Methods"

method strat_instr methods m = rule wp_intro, m, clean_assms; (simp only: False_eq_False)?
method strat_instr_dbg = (rule wp_intro, (solve_subgoal+)?); (rule asm_rl[of "wp _ _"], clean_assms)?; (simp only: False_eq_False)?

method strat_alloca = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr -
method strat_store  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_memory_allocated, sub_register_value\<close>
method strat_load   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_memory_value\<close>
method strat_add    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr \<open>sub_register_value, sub_register_value, sub_add_poison\<close>
method strat_icmp   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr \<open>sub_register_value, sub_register_value, sub_icmp_same_signs\<close>; simp only: compare_values_32.simps compare_values_64.simps

method strat_alloca_dbg = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr_dbg
method strat_store_dbg  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr_dbg
method strat_load_dbg   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr_dbg
method strat_add_dbg    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr_dbg
method strat_icmp_dbg   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr_dbg

method unfold_block_instr = rule asm_rl[of "wp (execute_block _ ([], _#_, _) _) _"], rule wp_intro
method unfold_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_intro

method instr_vcg_step = unfold_block_instr | unfold_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp
method instr_vcg_step_dbg = unfold_block_instr | unfold_instr | strat_alloca_dbg | strat_store_dbg | strat_load_dbg | strat_add_dbg | strat_icmp_dbg


subsection "Phi Node Methods"

method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _) _"], strat_instr \<open>sub_distinct_first, sub_some_refl, sub_map_of_some, sub_register_value\<close>
method strat_phi_dbg = rule asm_rl[of "wp (execute_phi _ _ _) _"], strat_instr_dbg

method unfold_block_phi = rule asm_rl[of "wp (execute_block _ (_#_, _, _) _) _"], rule wp_intro

method phi_vcg_step = unfold_block_phi | strat_phi
method phi_vcg_step_dbg = unfold_block_phi | strat_phi_dbg


subsection "Terminal Instruction Methods"

(*
method strat_branch_i1 = rule asm_rl[of "wp (execute_block _ ([], [], br_i1 _ _ _) _ ) _"], (rule wp_intro, sub_register_value); (simp only: False_eq_False)?
method strat_branch_label = rule asm_rl[of "wp (execute_block _ ([], [], br_label _) _ ) _"], rule wp_intro; (simp only: False_eq_False)?
method strat_return = rule asm_rl[of "wp (execute_block _ ([], [], ret _ _) _ ) _"], (rule wp_intro, sub_register_value); (simp only: False_eq_False)?

method term_vcg_step_dbg = rule asm_rl[of "wp (execute_block _ ([], [], _) _) _"], rule wp_intro, (solve_subgoal+)?; (simp only: False_eq_False)?

method term_vcg_step = strat_branch_i1 | strat_branch_label | strat_return
*)

subsection "Block VCG Methods"

method unfold_wp_instrs = rule asm_rl[of "wp_instrs _ _"], rule wp_instrs_intro

method block_vcg_step = unfold_wp_instrs | phi_vcg_step | instr_vcg_step
method block_vcg_step_dbg = unfold_wp_instrs | phi_vcg_step_dbg | instr_vcg_step_dbg

method block_vcg uses pres blocks = (subst (asm) pres)?, (subst blocks)?, unfold_unique_addresses?, block_vcg_step+, (simp (no_asm))?, \<comment> \<open>branching\<close>(intro conjI impI)?
method block_vcg_dbg uses pres blocks = (subst (asm) pres)?, (subst blocks)?, unfold_unique_addresses?, block_vcg_step_dbg+, (simp (no_asm))?, (intro conjI impI)?


subsection "Multi-Block VCG Methods"

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


method clean_goal' = (simp (no_asm_simp) split: prod.splits del: register_\<alpha>.simps registers_contain_unique_addresses.simps, intro allI conjI impI)
method clean_goal = (match conclusion in "case _ of (s, r) \<Rightarrow> (case r of return_value _ \<Rightarrow> _ | branch_label _ \<Rightarrow> _)" \<Rightarrow> clean_goal')


end