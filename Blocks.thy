theory Blocks
  imports "Instructions"
begin

section "Phi nodes"

fun phi_lookup :: "llvm_identifier option \<Rightarrow> (llvm_identifier * llvm_value_ref) list \<Rightarrow> llvm_value_ref result" where
  "phi_lookup l ls = do {
    prev \<leftarrow> some_or_err l phi_no_previous_block;
    assert phi_label_not_distinct (distinct (map fst ls));
    some_or_err (map_of ls prev) phi_label_not_found
  }"

definition execute_phi :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> (llvm_identifier * llvm_value_ref) list \<Rightarrow> state \<Rightarrow> state result" where
  "execute_phi prev name values s = do {
    v \<leftarrow> phi_lookup prev values;
    v' \<leftarrow> get_register s v;
    return (set_register name v' s)
  }"

lemma phi_wp_intro[THEN consequence, wp_intro]:
  assumes "distinct (map fst values)"
  assumes "p = Some p'" "map_of values p' = Some v" "register_\<alpha> s v = Some v'"
  shows "wp (execute_phi p name values s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  apply simp
  using assms
  apply (intro wp_intro; auto) done

print_theorems 

definition "wp_phi prev name values Q s \<equiv> wp (execute_phi prev name values s) Q"

lemma wp_phi_intro:
  assumes "distinct (map fst values)"
  assumes "p = Some p'" "map_of values p' = Some v" "register_\<alpha> s v = Some v'"
  assumes "\<And>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s \<Longrightarrow> Q s'"
  shows "wp_phi p name values Q s"
  unfolding wp_phi_def
  using assms
  by (intro wp_intro; auto)



section "Single block"

fun execute_block :: "llvm_identifier option \<Rightarrow> llvm_instruction_block \<Rightarrow> state \<Rightarrow> (state * llvm_block_return) result" where
  "execute_block previous ((phi name type values)#ps, is, t) s = do {
    s' \<leftarrow> execute_phi previous name values s;
    execute_block previous (ps, is, t) s'
  }"
| "execute_block previous ([], i#is, t) s = do {
    s' \<leftarrow> execute_instruction i s;
    execute_block previous ([], is, t) s'
  }"
| "execute_block previous (_, _, br_i1 v l1 l2) s = do {
    val \<leftarrow> get_register s v;
    label \<leftarrow> (case val of (vi1 b) \<Rightarrow> ok (if b then l1 else l2) | _ \<Rightarrow> err incompatible_types);
    return (s, branch_label label)
  }"
| "execute_block previous (_, _, br_label l) s = return (s, branch_label l)"
| "execute_block previous (_, _, ret t v) s = do {
    res \<leftarrow> get_register s v;
    return (s, return_value res)
  }"

definition "wp_block prev block Q s \<equiv> wp (execute_block prev block s) Q"
named_theorems wp_block_intro

lemma wp_block_phi_intro[wp_block_intro]:
  assumes "wp_phi prev name values (\<lambda>s'. wp_block prev (ps, is, t) Q s') s"
  shows "wp_block prev ((phi name type values)#ps, is, t) Q s"
  using assms
  unfolding wp_block_def wp_phi_def
  apply simp apply (rule wp_intro) by simp

lemma wp_block_instr_intro[wp_block_intro]:
  assumes "wp_instr i (\<lambda>s'. wp_block prev ([], is, t) Q s') s"
  shows "wp_block prev ([], i#is, t) Q s"
  using assms
  unfolding wp_block_def wp_instr_def
  apply simp apply (rule wp_intro) by simp

lemma wp_block_br_i1_intro[wp_block_intro]:
  assumes "register_\<alpha> s value = Some (vi1 b)"
  and "if b then Q (s, branch_label l1) else Q (s, branch_label l2)"
  shows "wp_block prev ([], [], br_i1 value l1 l2) Q s"
  using assms
  unfolding wp_block_def
  by (simp, intro wp_intro, auto; intro wp_intro wp_return_intro; simp)

lemma wp_block_br_label_intro[wp_block_intro]:
  assumes "Q (s, branch_label l)"
  shows "wp_block prev ([], [], br_label l) Q s"
  using assms
  unfolding wp_block_def
  by (simp add: wp_return_intro)

lemma wp_block_ret_intro[wp_block_intro]:
  assumes "register_\<alpha> s value = Some v"
  and "Q (s, return_value v)"
  shows "wp_block prev ([], [], ret type value) Q s"
  using assms
  unfolding wp_block_def
  by (simp; intro wp_intro wp_return_intro; simp)




lemma block_phi_wp_intro[wp_intro]:
  assumes "wp (execute_phi p name values s) (\<lambda>s'. wp (execute_block p (ps, is, t) s') Q)"
  shows "wp (execute_block p ((phi name type values)#ps, is, t) s) Q"
  using assms
  by (simp; rule wp_intro; simp)

lemma block_instr_wp_intro[wp_intro]:
  assumes "wp (execute_instruction i s) (\<lambda>s'. wp (execute_block p ([], is, t) s') Q)"
  shows "wp (execute_block p ([], i#is, t) s) Q"
  using assms
  by (simp; rule wp_intro; simp)

lemma block_ret_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s value = Some v"
  shows "wp (execute_block p ([], [], ret type value) s) (\<lambda>r. r = (s, return_value v))"
  using assms
  by (simp; intro wp_intro wp_return_intro; simp)

lemma block_br_label_wp_intro[THEN consequence, wp_intro]:
  shows "wp (execute_block p ([], [], br_label l) s) (\<lambda>r. r = (s, branch_label l))"
  by (simp; rule wp_return_intro; simp)

lemma block_br_i1_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s value = Some (vi1 b)"
  shows "wp (execute_block p ([], [], br_i1 value l1 l2) s) (\<lambda>r. r = (s, branch_label (if b then l1 else l2)))"
  using assms
  by (auto; intro wp_intro; auto; intro wp_intro wp_return_intro; auto)

















section "Multiple blocks"

partial_function (tailrec) execute_blocks :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> llvm_labeled_blocks \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_blocks prev label blocks state =
    (case map_of blocks label of
      None \<Rightarrow> err unknown_label
    | Some block \<Rightarrow>
      (case execute_block prev block state of
        err e \<Rightarrow> err e
      | ok (s', br) \<Rightarrow>
        (case br of
          return_value v \<Rightarrow> ok (s', Some v)
        | branch_label l \<Rightarrow> execute_blocks (Some label) l blocks s'
        )
      )
    )"

lemmas [code] = execute_blocks.simps

fun execute_function :: "llvm_function \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_function (func _ ((l,b)#ls)) s = execute_blocks None l ((l,b)#ls) s"
| "execute_function _ s = ok (s, None)"

end