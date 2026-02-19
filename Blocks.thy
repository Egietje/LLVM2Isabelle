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

definition execute_phi :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_register_name \<Rightarrow> (llvm_label * llvm_value_ref) list \<Rightarrow> state result" where
  "execute_phi s prev name values = do {
    v \<leftarrow> phi_lookup prev values;
    v' \<leftarrow> get_register s v;
    return (set_register s name v')
  }"

lemma wp_execute_phi_intro[THEN consequence, wp_intro]:
  assumes "distinct (map fst values)"
  assumes "p = Some prev"
  assumes "map_of values prev = Some v"
  assumes "register_\<alpha> s v = Some v'"
  shows "wp (execute_phi s p name values) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  apply simp
  using assms
  by (intro wp_intro; auto)



section "Single block"

fun execute_block :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> (state * llvm_block_return) result" where
  "execute_block s previous ((phi name type values)#ps, is, t) = do {
    s' \<leftarrow> execute_phi s previous name values;
    execute_block s' previous (ps, is, t)
  }"
| "execute_block s previous ([], i#is, t) = do {
    s' \<leftarrow> execute_instruction s i;
    execute_block s' previous ([], is, t)
  }"
| "execute_block s previous (_, _, br_i1 v l1 l2) = do {
    val \<leftarrow> get_register s v;
    label \<leftarrow> (case val of (vi1 b) \<Rightarrow> ok (if b then l1 else l2) | _ \<Rightarrow> err incompatible_types);
    return (s, branch_label label)
  }"
| "execute_block s previous (_, _, br_label l) = return (s, branch_label l)"
| "execute_block s previous (_, _, ret t v) = do {
    res \<leftarrow> get_register s v;
    return (s, return_value res)
  }"

lemma wp_execute_phi_block_intro[wp_intro]:
  assumes "wp (execute_phi s p name values) (\<lambda>s'. wp (execute_block s' p (ps, is, t)) Q)"
  shows "wp (execute_block s p ((phi name type values)#ps, is, t)) Q"
  using assms
  by (simp; rule wp_intro; simp)

lemma wp_execute_intruction_block_intro[wp_intro]:
  assumes "wp (execute_instruction s i) (\<lambda>s'. wp (execute_block s' p ([], is, t)) Q)"
  shows "wp (execute_block s p ([], i#is, t)) Q"
  using assms
  by (simp; rule wp_intro; simp)

lemma wp_execute_return_block_intro[THEN consequence, wp_intro]:
  assumes "\<exists>v. register_\<alpha> s value = Some v"
  shows "wp (execute_block s p ([], [], ret type value)) (\<lambda>(s', r). s' = s \<and> (\<exists>v. register_\<alpha> s value = Some v \<and> r = return_value v))"
  using assms
  by (simp; intro wp_intro wp_return_intro; simp)

lemma wp_execute_branch_label_block_intro[THEN consequence, wp_intro]:
  shows "wp (execute_block s p ([], [], br_label l)) (\<lambda>(s', r). s' = s \<and> r = branch_label l)"
  by (simp; rule wp_return_intro; simp)

lemma wp_execute_branch_i1_block_intro[THEN consequence, wp_intro]:
  assumes "\<exists>b. register_\<alpha> s value = Some (vi1 b)"
  shows "wp (execute_block s p ([], [], br_i1 value l1 l2)) (\<lambda>(s', r). s' = s \<and> (\<exists>b. register_\<alpha> s value = Some (vi1 b) \<and> r = branch_label (if b then l1 else l2)))"
  using assms
  by (simp; intro wp_intro; auto; intro wp_intro wp_return_intro; auto)


section "Multiple blocks"

partial_function (tailrec) execute_blocks :: "state \<Rightarrow> llvm_label option \<Rightarrow> llvm_label option \<Rightarrow> llvm_instruction_block \<Rightarrow> llvm_labeled_blocks \<Rightarrow> (state * llvm_value option) result" where
  "execute_blocks state previous current block labeled_blocks =
    (case execute_block state previous block of
      err e \<Rightarrow> err e
    | ok (s', br) \<Rightarrow>
      (case br of
        return_value v \<Rightarrow> ok (s', Some v)
      | branch_label l \<Rightarrow>
        (case map_of labeled_blocks l of
          None \<Rightarrow> err unknown_label
        | Some b' \<Rightarrow> execute_blocks s' current (Some l) b' labeled_blocks
        )
      )
    )"

lemmas [code] = execute_blocks.simps

fun execute_function :: "state \<Rightarrow> llvm_function \<Rightarrow> (llvm_value option) result" where
  "execute_function s (func _ is ls) = do {
    (_, r) \<leftarrow> execute_blocks s None None is ls;
    return r
  }"


end