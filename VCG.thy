theory VCG
  imports "Steps" "HOL-Eisbach.Eisbach" "Word_Lib/Word_32" "Word_Lib/Word_64"
begin

section "Useful Shorthands"

abbreviation register_contains_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_value n v s \<equiv> register_\<alpha> s (reg n) = Some v"

abbreviation register_contains_allocated_address :: "llvm_identifier \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_allocated_address n s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a \<noteq> None"

abbreviation register_contains_address_with_value :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> bool" where
  "register_contains_address_with_value n v s \<equiv> \<exists>a. register_\<alpha> s (reg n) = Some (addr a) \<and> memory_\<alpha> s a = Some (mem_val v)"

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

method clean_assms = ((elim exE conjE allE)+)?, (simp only: contract_updates)?; clean_registers?; clean_memory?; (simp only: triv_forall_equality)?
method clean_assms_non_destructive = ((elim exE conjE allE)+)?, (simp only: contract_updates)?; (simp only: triv_forall_equality)?

method unfold_unique_addresses = simp only: registers_contain_unique_addresses.simps unique_addresses.simps unique_addresses_rec.simps unique_address.simps HOL.simp_thms(21), clean_assms

subsection "Subgoal Solving Methods"

method sub_instantiate_register_address = rule asm_rl[of "register_\<alpha> _ _ = Some (addr _)"], (fastforce | simp)?; fail
method sub_memory_valid = rule asm_rl[of "valid_memory_address _ _"], (fastforce | simp)?; fail
method sub_register_value = rule asm_rl[of "register_\<alpha> _ _ = Some _"], (fastforce | simp)?; fail
method sub_memory_value = rule asm_rl[of "memory_\<alpha> _ _ = Some (mem_val _)"], (fastforce | simp split: if_splits)?; fail
method sub_add_poison = (rule asm_rl[of "add_no_poison32 _ _ _"] | rule asm_rl[of "add_no_poison64 _ _ _"]), (simp split: if_splits add: word_sless_alt word_sle_eq signed.leD)?; fail
method sub_icmp_same_signs = (rule asm_rl[of "if _ then same_signs32 _ _ else True"] | rule asm_rl[of "if _ then same_signs1 _ _ else True"] | rule asm_rl[of "if _ then same_signs64 _ _ else True"]), (fastforce | simp split: if_splits add: word_sless_alt word_sle_eq)?; fail
method sub_map_of_some = rule asm_rl[of "map_of _ _ = Some _"], (fastforce | simp)?; fail
method sub_distinct_first = rule asm_rl[of "distinct (map fst _)"], (fastforce | simp)?; fail
method sub_some_refl = rule asm_rl[of "Some _ = Some _"], (rule refl)?; fail
method sub_is_lid = rule asm_rl[of "is_lid _"], (fastforce | simp)?; fail

method solve_subgoal = sub_instantiate_register_address | sub_memory_valid | sub_register_value
                     | sub_memory_value | sub_add_poison | sub_icmp_same_signs | sub_map_of_some
                     | sub_distinct_first | sub_some_refl | sub_is_lid


subsection "Instruction Methods"

method strat_instr methods m = rule wp_intro, m, clean_assms; (simp only: False_eq_False)?
method strat_instr_dbg = (rule wp_intro, (solve_subgoal+)?); (rule asm_rl[of "wp _ _"], clean_assms)?; (simp only: False_eq_False)?

method strat_alloca = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr \<open>sub_is_lid\<close>
method strat_store  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_memory_valid, sub_register_value\<close>
method strat_load   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr \<open>sub_instantiate_register_address, sub_memory_value, sub_is_lid\<close>
method strat_add    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr \<open>sub_register_value, sub_register_value, sub_add_poison, sub_is_lid\<close>
method strat_icmp   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr \<open>sub_register_value, sub_register_value, sub_icmp_same_signs, sub_is_lid\<close>; simp only: compare_values_32.simps compare_values_64.simps compare_values_1.simps

method strat_alloca_dbg = rule asm_rl[of "wp (execute_alloca _ _) _"], strat_instr_dbg
method strat_store_dbg  = rule asm_rl[of "wp (execute_store _ _ _) _"], strat_instr_dbg
method strat_load_dbg   = rule asm_rl[of "wp (execute_load _ _ _) _"], strat_instr_dbg
method strat_add_dbg    = rule asm_rl[of "wp (execute_add _ _ _ _ _) _"], strat_instr_dbg
method strat_icmp_dbg   = rule asm_rl[of "wp (execute_icmp _ _ _ _ _ _) _"], strat_instr_dbg

method unfold_instr = rule asm_rl[of "wp (execute_instruction _ _) _"], rule wp_intro

method vcg_instr = unfold_instr | strat_alloca | strat_store | strat_load | strat_add | strat_icmp
method vcg_instr_dbg = unfold_instr | strat_alloca_dbg | strat_store_dbg | strat_load_dbg | strat_add_dbg | strat_icmp_dbg


subsection "Phi Node Methods"

method strat_phi = rule asm_rl[of "wp (execute_phi _ _ _) _"], strat_instr \<open>sub_distinct_first, sub_some_refl, sub_map_of_some, sub_register_value\<close>
method strat_phi_dbg = rule asm_rl[of "wp (execute_phi _ _ _) _"], strat_instr_dbg



















method vcg_verify_function uses annot =
  subst (3) annot,
  simp del: split_paired_All,
  intro conjI

method vcg_verify_program uses prog annot =
  simp,
  subst prog,
  simp,
  (intro conjI)?; vcg_verify_function annot: annot

method unfold_first_label uses func =
  subst first_label_def,
  subst func,
  simp del: split_paired_All

method vcg_step uses prog func =
  rule wp_step_intro,
  subst prog,
  simp,
  subst func,
  simp

method vcg_floyd_cond uses prog func =
  subst floyd_cond_def,
  rule wp_annotated_step_intro,
  (vcg_step prog: prog func: func)


method vcg_step_instr =
  rule asm_rl[of "wp_rc_step_i _ _ (execi _ ([],_#_,_) _) _"],
  intro wp_step_i_intros;
  force?;
  (thin_tac "\<not>is_call _" | thin_tac "is_call _")?,
  (vcg_instr+)?
method vcg_step_ter =
  rule asm_rl[of "wp_rc_step_i _ _ (execi _ ([],[],_) _) _"],
  intro wp_step_i_intros,
  (simp; fail)?;
  (thin_tac "\<not>is_call _" | thin_tac "is_call _")?

method vcg_steps_execi uses block =
  rule asm_rl[of "wp_rc_steps_i _ _ (execi _ _ _) _"],
  rule wp_rc_steps_i_intro;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  (subst block)?,
  (vcg_step_instr | vcg_step_ter)

method vcg_steps_flowi_branch uses block pre prog annot =
  rule asm_rl[of "wp_rc_steps_i _ _ (flowi _ (branch_label _)) _"],
  rule wp_rc_steps_i_intro;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  simp (no_asm),
  rule wp_steps_until_intro;
  ((subst (asm) has_annotation_def, subst (asm) prog, subst (asm) annot, simp); fail)?,
  (thin_tac "has_annotation _ _ _" | thin_tac "\<not>has_annotation _ _ _")?

method vcg_steps_flowi_return uses block pre prog annot =
  rule asm_rl[of "wp_rc_steps_i _ _ (flowi _ (return_value _)) _"],
  rule wp_rc_steps_i_intro;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  simp (no_asm),
  rule wp_steps_until_intro;
  ((subst (asm) has_annotation_def, subst (asm) prog, subst (asm) annot, simp); fail)?,
  (thin_tac "has_annotation _ _ _" | thin_tac "\<not>has_annotation _ _ _")?

method vcg_steps uses block pre =
  rule wp_rc_steps_i_intro;
  (simp; fail)?;
  (thin_tac "\<not>(_ \<nexists>\<rightarrow>\<^sub>i)" | thin_tac "_ \<nexists>\<rightarrow>\<^sub>i")?,
  (subst block)?,
  (subst (asm) pre)?

method vcg_annotation_holds uses prog annot pre =
  subst annotation_holds_def,
  subst prog,
  subst annot,
  (simp (no_asm) del: split_paired_All)?,
  unfold pre,
  (simp (no_asm) del: split_paired_All)?


method unfold_precond uses pre annot prog =
  (subst (asm) annotation_holds_def,
  subst (asm) annot,
  subst (asm) prog)?,
  (simp (no_asm_use) del: split_paired_All)?,
  subst (asm) pre,
  clean_assms





















section "Word Lemma Bundle"

bundle word_bundle
begin

lemma lt_imp_le: "(i::word32) <s 2 ^ 31 - 1 \<Longrightarrow> i \<le>s 2 ^ 31 - 2"
  by (simp add: word_sle_eq word_sless_alt)


lemma le_imp_lt: "i \<le>s 2 ^ 31 - 2 \<Longrightarrow> (i::word32) <s 2 ^ 31 - 1"
  by (simp add: word_sle_eq word_sless_alt)

lemma lt_inc_nlt_imp_eq[simp]: "(i::word32) <s (b::word32) \<Longrightarrow> \<not> i+1 <s b \<Longrightarrow> i+1 = b"
  apply (simp add: word_sle_eq word_sless_alt)
  by (smt (verit, ccfv_threshold) diff_add_cancel signed_arith_ineq_checks_to_eq_word32(1,2) signed_minus_1
      signed_take_bit_int_eq_self signed_take_bit_int_greater_eq_minus_exp sint_word_ariths(1,8) word_sint.Rep_eqD)

lemma lt_inc_nlt_mult_eq[simp]: "(i::word32) <s (b::word32) \<Longrightarrow> \<not> i+1 <s b \<Longrightarrow> a*i+a = a*b"
  by (metis (no_types, lifting) distrib_left lt_inc_nlt_imp_eq mult_numeral_1_right numeral_One)

lemma i_no_overflow_impl_positive[simp]: "0 \<le>s i \<Longrightarrow> (i::word32) <s 2^31 - 1 \<Longrightarrow> 0 \<le>s (i+1)"
  by (smt (verit, del_insts) add_diff_eq diff_add_cancel diff_numeral_special(10) of_int_eq_id signed_minus_1
      signed_take_bit_int_eq_self signed_take_bit_int_eq_self_iff signed_take_bit_int_greater_eq_minus_exp sint_word_ariths(1,2,8)
      word_sle_eq word_sless_alt)

lemma i_incr_no_overflow_impl_not_negative[simp]: "0 \<le>s (i::word32) \<Longrightarrow> (i::word32) <s 2^31 - 1 \<Longrightarrow> \<not> i + 1 <s 0"
  by (smt (verit, best) i_no_overflow_impl_positive word_sle_eq word_sless_alt)

lemma i_bounds_no_overflow_neg[simp]: "- (2 ^ 31) \<le> sint (a::word32) * sint (b::word32) \<Longrightarrow>
    sint a * sint b \<le> 2 ^ 31 - 1 \<Longrightarrow>
    0 \<le>s (i::word32) \<Longrightarrow>
    i <s b \<Longrightarrow>
    b \<le>s 2 ^ 31 - 1 \<Longrightarrow>
    i <s 2 ^ 31 - 1 \<Longrightarrow>
    a <s 0 \<Longrightarrow> a * i <s 0 \<Longrightarrow> \<not> 0 \<le>s a * i + a"
proof -
  assume bounds: "- (2^31) \<le> sint a * sint b" "sint a * sint b \<le> 2^31 - 1"
  assume hi: "0 \<le>s i" "i <s b" "b \<le>s 2^31 - 1" "i <s 2^31 - 1"
  assume neg: "a <s 0" "a * i <s 0"
  have sa: "sint a < 0"
    using neg(1) 
    by (simp add: word_sless_alt)
  have si: "0 \<le> sint i"
    using hi(1)
    by (simp add: word_sless_alt word_sle_eq)
  have si_lt: "sint i < 2^31 - 1"
    using hi(4) by (simp add: word_sless_alt word_sle_eq)
  have sb_lt: "sint b \<le> 2^31 - 1"
    using hi(3) by (simp add: word_sless_alt word_sle_eq)
  have sai_neg: "sint (a * i) < 0"
    using neg(2) by (simp add: word_sless_alt word_sle_eq)
  have no_ovf_ai: "sint (a * i) = sint a * sint i"
    using sai_neg sa si 
    apply(auto intro: signed_arith_sint simp: sint_word_ariths word_sless_alt word_sle_eq)
    by (smt (verit, del_insts) bounds(1) hi(2) mult_eq_0_iff mult_less_cancel_left_disj signed_take_bit_int_eq_self
        word_sless_alt)
  have no_ovf_sum: "sint (a * i + a) = sint (a * i) + sint a"
    proof -
      have lo: "-(2^31) \<le> sint (a * i) + sint a"
      proof -
        have si_lt_b: "sint i < sint b"
          using hi(2) by (simp add: word_sless_alt)
        have sb_bounds: "-(2^31) \<le> sint b"
          using si si_lt_b by auto
        have key: "sint a * sint b \<le> sint a * (sint i + 1)"
          using sa si_lt_b
          by (simp add: mult_le_cancel_left_neg)
        show ?thesis
          using no_ovf_ai key bounds(1) right_diff_distrib' mult_cancel_left2
          by (smt (verit) )
      qed
      have hi': "sint (a * i) + sint a \<le> 2^31 - 1"
        using sai_neg sa
        by simp
      then show ?thesis
        using lo hi' no_ovf_ai
        by (simp add: sint_word_ariths signed_take_bit_int_eq_self)
    qed
  show "\<not> 0 \<le>s a * i + a"
    unfolding word_sle_def
    using no_ovf_sum sai_neg sa
    by (smt (verit) neg(1) word_sle_def word_sle_eq word_sless_alt)
qed

lemma i_bounds_no_overflow_pos[simp]: "- (2 ^ 31) \<le> sint (a::word32) * sint (b::word32) \<Longrightarrow>
    sint a * sint b \<le> 2 ^ 31 - 1 \<Longrightarrow>
    0 <s b \<Longrightarrow>
    0 \<le>s (i::word32) \<Longrightarrow>
    i <s b \<Longrightarrow>
    b \<le>s 2 ^ 31 - 1 \<Longrightarrow>
    i <s 2 ^ 31 - 1 \<Longrightarrow>
    0 \<le>s a \<Longrightarrow> 0 \<le>s a * i \<Longrightarrow> \<not> a * i + a <s 0"
proof -
  assume bounds: "- (2^31) \<le> sint a * sint b" "sint a * sint b \<le> 2^31 - 1"
  assume hi: "0 \<le>s i" "i <s b" "b \<le>s 2^31 - 1" "i <s 2^31 - 1"
  assume pos: "0 \<le>s a" "0 \<le>s a * i"
  have sa: "sint a \<ge> 0"
    using pos(1)
    by (simp add: word_sle_eq)
  have si: "0 \<le> sint i"
    using hi(1)
    by (simp add: word_sless_alt word_sle_eq)
  have si_lt: "sint i < 2^31 - 1"
    using hi(4) by (simp add: word_sless_alt word_sle_eq)
  have sb_lt: "sint b \<le> 2^31 - 1"
    using hi(3) by (simp add: word_sless_alt word_sle_eq)
  have sai_neg: "sint (a * i) \<ge> 0"
    using pos(2) by (simp add: word_sless_alt word_sle_eq)
  have no_ovf_ai: "sint (a * i) = sint a * sint i"
    using sai_neg sa si 
    apply(auto intro: signed_arith_sint simp: sint_word_ariths word_sless_alt word_sle_eq)
    by (smt (verit, best) bounds(2) hi(2) mult_less_cancel_left_disj signed_take_bit_int_eq_self word_sless_alt
        zero_le_mult_iff)
  have no_ovf_sum: "sint (a * i + a) = sint (a * i) + sint a"
    proof -
      have lo: "-(2^31) \<le> sint (a * i) + sint a"
        using sa sai_neg by force
      have hi': "sint (a * i) + sint a \<le> 2^31 - 1"
      proof -
        have si_lt_b: "sint i < sint b"
          using hi(2) by (simp add: word_sless_alt)
        have sb_bounds: "-(2^31) \<le> sint b"
          using si si_lt_b by auto
        have key: "sint a * sint b \<ge> sint a * (sint i + 1)"
          using sa si_lt_b
          by (smt (verit, best) mult_less_cancel_left_disj)
        show ?thesis
          using no_ovf_ai key bounds(2) right_diff_distrib' mult_cancel_left2
          by (smt (verit, best))
      qed
      then show ?thesis
        using lo hi' no_ovf_ai
        by (simp add: sint_word_ariths signed_take_bit_int_eq_self)
    qed
  show ?thesis
    unfolding word_sle_def
    using no_ovf_sum sai_neg sa 
    by (smt (verit) pos(1) word_sle_def word_sle_eq word_sless_alt)
qed

lemma bounded_inc_no_overflow[simp]: "0 \<le>s i \<Longrightarrow> (b::word32) \<le>s 2^31-1 \<Longrightarrow> (i::word32) <s b \<Longrightarrow> 0 <s i+1"
  using sint_word_ariths word_sle_eq word_sless_alt add_diff_cancel_right' i_incr_no_overflow_impl_not_negative signed_0 signed_minus_1
  by (smt (verit, del_insts))
lemma pos_not_neg[simp]: "0 <s (i::word32)+1 \<Longrightarrow> \<not> i + 1 <s 0" by simp

end








method unfold_wp_instrs_phi = rule asm_rl[of "wp_instrs _ (execi _ (_#_,_,_) _) _"], rule wp_instrs_intro

method phi_vcg_step = unfold_wp_instrs_phi | strat_phi
method phi_vcg_step_dbg = unfold_wp_instrs_phi | strat_phi_dbg


subsection "Terminal Instruction Methods"


method strat_branch_i1 = rule asm_rl[of "wp_instrs _ (execi _ ([], [], br_i1 _ _ _) _) _"], (intro wp_instrs_intro, sub_register_value); (simp only: False_eq_False)?
method strat_branch_label = rule asm_rl[of "wp_instrs _ (execi  _ ([], [], br_label _) _ ) _"], intro wp_instrs_intro; (simp only: False_eq_False)?
method strat_return = rule asm_rl[of "wp_instrs _ (execi _ ([], [], ret _) _ ) _"], (intro wp_instrs_intro, sub_register_value); (simp only: False_eq_False)?

method term_vcg_step = strat_branch_i1 | strat_branch_label | strat_return
method term_vcg_step_dbg = rule asm_rl[of "wp_instrs _ (execi _ ([], [], _) _) _"], intro wp_instrs_intro, (solve_subgoal+)?; (simp only: False_eq_False)?


subsection "Block VCG Methods"

method block_vcg_step = phi_vcg_step | instr_vcg_step | term_vcg_step
method block_vcg_step_dbg = phi_vcg_step_dbg | instr_vcg_step_dbg | term_vcg_step_dbg

method block_vcg uses pres blocks = (subst (asm) pres)?, (subst (2) blocks)?, unfold_unique_addresses?, block_vcg_step+; (simp (no_asm))?, (intro conjI impI)?
method block_vcg_dbg uses pres blocks = (subst (asm) pres)?, (subst (2) blocks)?, unfold_unique_addresses?, block_vcg_step_dbg+, (simp (no_asm))?, (intro conjI impI)?


subsection "Multi-Block VCG Methods"

method unfold_floyd uses prog_def func_def =
  rule asm_rl[of "floyd_vc _ _"],
  rule floyd_vc_intro,
  unfold first_label_def floyd_cond_def annotation_holds_def has_annotation_def,
  (simp add: prog_def),
  intro conjI allI impI;
  (simp add: func_def)?;
  ((thin_tac "_ = Some (lid _)" | thin_tac "_ = None"), simp only: triv_forall_equality)?


method instantiate_block =
  rule asm_rl[of "map_of _ (lid _) = Some _"],
  force
method instantiate_func =
  rule asm_rl[of "map_of _ (gid _) = Some _"],
  force

method unfold_wp_step =
  rule asm_rl[of "wp_step _ _ _"],
  rule wp_step_intro,
  instantiate_func,
  instantiate_block

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
  (thin_tac "\<not>has_annotation _ _ _" | thin_tac "has_annotation _ _ _")?;
  (unfold_wp_step | unfold_endgoal)?


end