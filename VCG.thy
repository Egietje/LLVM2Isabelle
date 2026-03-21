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



section "Annotations"

type_synonym block_preconditions = "(llvm_label * (state \<Rightarrow> bool)) list"
type_synonym function_postcondition = "(llvm_value * state) \<Rightarrow> bool"
datatype annotated_function = annotated "llvm_function" "block_preconditions" "function_postcondition"

partial_function (tailrec) execute_blocks_from_until :: "annotated_function \<Rightarrow> llvm_label \<Rightarrow> llvm_label option \<Rightarrow> state \<Rightarrow> (state * llvm_block_return) result" where
  "execute_blocks_from_until fun label prev s = (case fun of annotated (func fdef blocks) pre post \<Rightarrow>
    (case map_of blocks label of
      None \<Rightarrow> err unknown_label
    | Some b \<Rightarrow> (case (execute_block prev b s) of
        ok (s', return_value v) \<Rightarrow> ok (s', return_value v)
      | ok (s', branch_label l) \<Rightarrow> (case map_of pre l of
          Some _ \<Rightarrow> ok (s', branch_label l)
        | None \<Rightarrow> execute_blocks_from_until fun l (Some label) s'
        )
      | err e \<Rightarrow> err e
      )
    )
  )"
lemmas [code] = execute_blocks_from_until.simps


lemma hoare_blocks_from_until_intro:
  assumes "map_of blocks label = Some b"
  assumes "hoare
            P
            (execute_block prev b)
            (\<lambda>(s, r). case r of
              return_value v \<Rightarrow> Q (s, r)
            | branch_label l \<Rightarrow> (case map_of pre l of
                Some _ \<Rightarrow> Q (s, r)
              | None \<Rightarrow>
                hoare
                  (\<lambda>s'. s' = s)
                  (execute_blocks_from_until (annotated (func fdef blocks) pre post) l (Some label))
                Q
              )
            )"
  shows "hoare P (execute_blocks_from_until (annotated (func fdef blocks) pre post) label prev) Q"
  apply (rule hoare_intro)
  using assms
  apply (auto simp: execute_blocks_from_until.simps)
  subgoal for r s h
  unfolding hoare_def wp_gen_def
  apply (cases "execute_block prev b (r, s, h)")
  apply auto
  subgoal for r' s' h' ret
    apply (cases ret)
     apply auto apply force
    subgoal for l 
      apply (cases "map_of pre l") apply auto apply force by fastforce
    done
  by fastforce
  done

fun verify_from_with_precond where
  "verify_from_with_precond (annotated (func fdef blocks) pre post) label precond =
    hoare
      precond
      (execute_blocks_from_until (annotated (func fdef blocks) pre post) label None)
      (\<lambda>(s, r). (case r of
        return_value v \<Rightarrow> post (v, s)
      | branch_label l \<Rightarrow> (case map_of pre l of
          Some Q \<Rightarrow> Q s
        | None \<Rightarrow> False
        )
      ))"

fun verify_from where
  "verify_from (annotated f pre post) label = (case map_of pre label of
    Some precond \<Rightarrow> verify_from_with_precond (annotated f pre post) label precond
  | None \<Rightarrow> verify_from_with_precond (annotated f pre post) label (\<lambda>s. True))"


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


subsection "Subgoal Solving Methods"

method sub_instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"]; (fastforce | simp); fail
method sub_memory_allocated = rule asm_rl[of "memory_\<alpha> _ _ \<noteq> None"]; (fastforce | simp); fail
method sub_register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"]; (fastforce | simp); fail
method sub_memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (Some _)"]; (fastforce | simp split: if_splits); fail
method sub_add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]); (fastforce | simp); fail
method sub_icmp_same_signs = rule asm_rl[of "if _ then same_signs _ _ else True"]; (fastforce | simp); fail
method sub_map_of_some = rule asm_rl[of "map_of _ _ = Some _"]; (fastforce | simp); fail
method sub_distinct_first = rule asm_rl[of "distinct (map fst _)"]; (fastforce | simp); fail
method sub_some_refl = rule asm_rl[of "Some _ = Some _"]; rule refl; fail

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
method strat_icmp_dbg   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr_dbg; simp only: compare_values_32.simps compare_values_64.simps

method unfold_block_instr = rule asm_rl[of "wp (execute_block _ ([], _#_, _) _) _"], rule wp_intro
method unfold_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_intro

method instr_vcg_step = unfold_block_instr | unfold_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp
method instr_vcg_step_dbg = unfold_block_instr | unfold_instr | strat_alloca_dbg | strat_store_dbg | strat_load_dbg | strat_add_dbg | strat_icmp_dbg


subsection "Phi Node Methods"

method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _ _) _"], strat_instr \<open>sub_distinct_first, sub_some_refl, sub_map_of_some, sub_register_value\<close>
method strat_phi_dbg = rule asm_rl[of "wp (execute_phi _ _ _ _) _"], strat_instr_dbg

method unfold_block_phi = rule asm_rl[of "wp (execute_block _ (_#_, _, _) _) _"], rule wp_intro

method phi_vcg_step = unfold_block_phi | strat_phi
method phi_vcg_step_dbg = unfold_block_phi | strat_phi_dbg


subsection "Terminal Instruction Methods"

method strat_branch_i1 = rule asm_rl[of "wp (execute_block _ ([], [], br_i1 _ _ _) _ ) _"], (rule wp_intro, sub_register_value); (simp only: False_eq_False)?
method strat_branch_label = rule asm_rl[of "wp (execute_block _ ([], [], br_label _) _ ) _"], rule wp_intro; (simp only: False_eq_False)?
method strat_return = rule asm_rl[of "wp (execute_block _ ([], [], ret _ _) _ ) _"], (rule wp_intro, sub_register_value); (simp only: False_eq_False)?

method term_vcg_step_dbg = rule asm_rl[of "wp (execute_block _ ([], [], _) _) _"], rule wp_intro, (solve_subgoal+)?; (simp only: False_eq_False)?

method term_vcg_step = strat_branch_i1 | strat_branch_label | strat_return


subsection "Block VCG Methods"

method unfold_hoare = rule asm_rl[of "hoare _ (execute_block _ _) _"], rule hoare_intro

method block_vcg_step = unfold_hoare | phi_vcg_step | instr_vcg_step | term_vcg_step
method block_vcg_step_dbg = unfold_hoare | phi_vcg_step_dbg | instr_vcg_step_dbg | term_vcg_step_dbg

method block_vcg = block_vcg_step+
method block_vcg_dbg = block_vcg_step_dbg+


subsection "Multi-Block VCG Methods"

method clean_goal = rule asm_rl[of "case _ of _ \<Rightarrow> (case _ of _ \<Rightarrow> _)"]
                  , auto simp only: split prod.case split: llvm_block_return.splits option.splits if_splits; (simp; fail)?

method unfold_execute_blocks_from_until = rule asm_rl[of "hoare _ (execute_blocks_from_until _ _ _) _"], rule hoare_blocks_from_until_intro, sub_map_of_some
method unfold_verify = rule asm_rl[of "verify_from _ _"], simp

method vcg_step = unfold_verify | unfold_execute_blocks_from_until | block_vcg_step
method vcg_step_dbg = unfold_verify | unfold_execute_blocks_from_until | block_vcg_step_dbg 
method vcg = vcg_step+
method vcg_dbg = vcg_step_dbg+

end