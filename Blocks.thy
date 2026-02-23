theory Blocks
  imports "Instructions"
begin

section "Phi nodes"

fun phi_lookup :: "llvm_label option \<Rightarrow> (llvm_label * llvm_value_ref) list \<Rightarrow> llvm_value_ref result" where
  "phi_lookup l ls = do {
    prev \<leftarrow> some_or_err l phi_no_previous_block;
    assert phi_label_not_distinct (distinct (map fst ls));
    some_or_err (map_of ls prev) phi_label_not_found
  }"

definition execute_phi :: "llvm_label option \<Rightarrow> llvm_register_name \<Rightarrow> (llvm_label * llvm_value_ref) list \<Rightarrow> state \<Rightarrow> state result" where
  "execute_phi prev name values s = do {
    v \<leftarrow> phi_lookup prev values;
    v' \<leftarrow> get_register s v;
    return (set_register name v' s)
  }"

lemma phi_wp_intro[THEN consequence, wp_intro]:
  assumes "distinct (map fst values)"
  assumes "\<exists>p' v v'. p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v'"
  shows "wp (execute_phi p name values s) (\<lambda>s'. \<exists>p' v v'. p = Some p' \<and> map_of values p' = Some v \<and> register_\<alpha> s v = Some v' \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  apply simp
  using assms
  apply (intro wp_intro; auto)
  by (metis eq_key_imp_eq_value)



section "Single block"

fun execute_block :: "llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> state \<Rightarrow> (state * llvm_block_return) result" where
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
  assumes "\<exists>v. register_\<alpha> s value = Some v"
  shows "wp (execute_block p ([], [], ret type value) s) (\<lambda>(s', r). s' = s \<and> (\<exists>v. register_\<alpha> s value = Some v \<and> r = return_value v))"
  using assms
  by (simp; intro wp_intro wp_return_intro; simp)

lemma block_br_label_wp_intro[THEN consequence, wp_intro]:
  shows "wp (execute_block p ([], [], br_label l) s) (\<lambda>(s', r). s' = s \<and> r = branch_label l)"
  by (simp; rule wp_return_intro; simp)

lemma block_br_i1_wp_intro[THEN consequence, wp_intro]:
  assumes "\<exists>b. register_\<alpha> s value = Some (vi1 b)"
  shows "wp (execute_block p ([], [], br_i1 value l1 l2) s) (\<lambda>(s', r). s' = s \<and> (\<exists>b. register_\<alpha> s value = Some (vi1 b) \<and> r = branch_label (if b then l1 else l2)))"
  using assms
  by (simp; intro wp_intro; auto; intro wp_intro wp_return_intro; auto)


section "Multiple blocks"

partial_function (tailrec) execute_blocks :: "llvm_label option \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> llvm_labeled_blocks \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_blocks previous current block labeled_blocks state =
    (case execute_block previous block state of
      err e \<Rightarrow> err e
    | ok (s', br) \<Rightarrow>
      (case br of
        return_value v \<Rightarrow> ok (s', Some v)
      | branch_label l \<Rightarrow>
        (case map_of labeled_blocks l of
          None \<Rightarrow> err unknown_label
        | Some b' \<Rightarrow> execute_blocks current (Some l) b' labeled_blocks s'
        )
      )
    )"

lemmas [code] = execute_blocks.simps

fun execute_function :: "llvm_function \<Rightarrow> state \<Rightarrow> (llvm_value option) result" where
  "execute_function (func _ is ls) s = do {
    (_, r) \<leftarrow> execute_blocks None None is ls s;
    return r
  }"


end