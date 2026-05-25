theory Instructions
  imports "Definitions" "Registers" "Memory"
begin

section "Simps"

lemma wp_case_value_addr_intro[wp_intro]:
  assumes "\<And>x. a = addr x \<Longrightarrow> wp_gen (f x) Q E"
  assumes "\<not>(\<exists>x. a = addr x) \<Longrightarrow> wp_gen g Q E"
  shows "wp_gen (case a of addr x \<Rightarrow> f x | _ \<Rightarrow> g) Q E"
  using assms
  unfolding wp_gen_def
  by (cases "a"; auto)



section "Memory instructions"

definition execute_alloca :: "llvm_identifier \<Rightarrow> state \<Rightarrow> state result" where
  "execute_alloca name s = do {
      (s', a) \<leftarrow> return (allocate_stack s);
      return (set_register name (addr a) s')
    }"

lemma alloca_wp_intro[THEN consequence, wp_intro]:
  "wp (execute_alloca name s) (\<lambda>s'. \<exists>a. (register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (addr a)) \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some None) \<and> memory_\<alpha> s a = None))"
  unfolding execute_alloca_def
  by (intro wp_intro; auto)

thm alloca_wp_intro

lemma cons_ex:
  assumes "wp c (\<lambda>s. \<exists>x. P x s)"
  assumes "\<And>s x. P x s \<Longrightarrow> Q s"
  shows "wp c Q"
  oops
  


fun get_address_from_pointer :: "state \<Rightarrow> llvm_pointer \<Rightarrow> llvm_address result" where
  "get_address_from_pointer s p = do {
    a \<leftarrow> get_register s p;
    (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address)
  }"

definition execute_store :: "llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state result" where
  "execute_store v p s = do {
    address \<leftarrow> get_address_from_pointer s p;
    value \<leftarrow> get_register s v;
    set_memory address value s
  }"

lemma store_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s pointer = Some (addr a)" "memory_\<alpha> s a \<noteq> None"
  assumes "register_\<alpha> s value = Some v"
  shows "wp (execute_store value pointer s) (\<lambda>s'. memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (Some v)) \<and> register_\<alpha> s' = register_\<alpha> s)"
  unfolding execute_store_def
  using assms
  apply simp
  by (intro wp_intro; auto)


definition execute_load :: "llvm_identifier \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state result" where
  "execute_load n p s = do {
    a \<leftarrow> get_address_from_pointer s p;
    v \<leftarrow> get_memory s a;
    return (set_register n v s)
  }"

lemma load_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s pointer = Some (addr a)" "memory_\<alpha> s a = Some (Some v)"
  shows "wp (execute_load name pointer s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v))"
  unfolding execute_load_def
  using assms
  apply simp
  by (intro wp_intro; auto)


section "Add instruction"
(* TODO: support pointers *)

fun unsigned_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "unsigned_overflow32 a b = (a + b < a)"

fun signed_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "signed_overflow32 a b = ((a <s 0 \<and> b <s 0 \<and> 0 \<le>s a+b) \<or> (0 \<le>s a \<and> 0 \<le>s b \<and> a+b <s 0))"

(* a and b are negative \<longrightarrow> a + b must be negative *)
(* a and b are positive \<longrightarrow> a + b must be positive *)
(* a and b are different \<longrightarrow> a + b cannot overflow*)

fun unsigned_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "unsigned_overflow64 a b = (a + b < a)"

fun signed_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "signed_overflow64 a b = ((a <s 0 \<and> b <s 0 \<and> 0 \<le>s a+b) \<or> (0 \<le>s a \<and> 0 \<le>s b \<and> a+b <s 0))"

definition add_no_poison32 :: "llvm_add_wrap \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "add_no_poison32 wrap a b = (
      let uov = unsigned_overflow32 a b;
          sov = signed_overflow32 a b
      in case wrap of
           add_default \<Rightarrow> True
         | add_nuw \<Rightarrow> \<not>uov
         | add_nsw \<Rightarrow> \<not>sov
         | add_nuw_nsw \<Rightarrow> \<not>uov \<and> \<not>sov
     )"

declare add_no_poison32_def[simp]

definition add_no_poison64 :: "llvm_add_wrap \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "add_no_poison64 wrap a b = (
      let uov = unsigned_overflow64 a b;
          sov = signed_overflow64 a b
      in case wrap of
           add_default \<Rightarrow> True
         | add_nuw \<Rightarrow> \<not>uov
         | add_nsw \<Rightarrow> \<not>sov
         | add_nuw_nsw \<Rightarrow> \<not>uov \<and> \<not>sov
     )"

declare add_no_poison64_def[simp]


fun add_values :: "llvm_add_wrap \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "add_values wrap (vi32 a) (vi32 b) = (if add_no_poison32 wrap a b then ok (vi32 (a+b)) else ok poison)"
| "add_values wrap (vi64 a) (vi64 b) = (if add_no_poison64 wrap a b then ok (vi64 (a+b)) else ok poison)"
| "add_values _ poison (vi32 _) = ok poison"
| "add_values _ (vi32 _) poison = ok poison"
| "add_values _ poison (vi64 _) = ok poison"
| "add_values _ (vi64 _) poison = ok poison"
| "add_values _ poison poison = ok poison"
| "add_values _ _ _ = err incompatible_types"


definition execute_add :: "llvm_identifier \<Rightarrow> llvm_add_wrap \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state result" where
  "execute_add name wrap v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> add_values wrap v1' v2';
    return (set_register name res s)
  }"


lemma add32_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s v1 = Some (vi32 v1')" "register_\<alpha> s v2 = Some (vi32 v2')" "add_no_poison32 wrap v1' v2'"
  shows "wp (execute_add name wrap v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi32 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_intro; simp; auto; intro wp_intro; simp)

lemma add64_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s v1 = Some (vi64 v1')" "register_\<alpha> s v2 = Some (vi64 v2')" "add_no_poison64 wrap v1' v2'"
  shows "wp (execute_add name wrap v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi64 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_intro; simp; auto; intro wp_intro; simp)



section "Compare instruction"

fun compare_values_32 :: "llvm_compare_condition \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> llvm_value" where
  "compare_values_32 comp_eq a b = vi1 (a = b)"
| "compare_values_32 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_32 comp_ugt a b = vi1 (a > b)"
| "compare_values_32 comp_uge a b = vi1 (a \<ge> b)"
| "compare_values_32 comp_ult a b = vi1 (a < b)"
| "compare_values_32 comp_ule a b = vi1 (a \<le> b)"
| "compare_values_32 comp_sgt a b = vi1 (b <s a)"
| "compare_values_32 comp_sge a b = vi1 (b \<le>s a)"
| "compare_values_32 comp_slt a b = vi1 (a <s b)"
| "compare_values_32 comp_sle a b = vi1 (a \<le>s b)"

fun compare_values_64 :: "llvm_compare_condition \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> llvm_value" where
  "compare_values_64 comp_eq a b = vi1 (a = b)"
| "compare_values_64 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_64 comp_ugt a b = vi1 (a > b)"
| "compare_values_64 comp_uge a b = vi1 (a \<ge> b)"
| "compare_values_64 comp_ult a b = vi1 (a < b)"
| "compare_values_64 comp_ule a b = vi1 (a \<le> b)"
| "compare_values_64 comp_sgt a b = vi1 (b <s a)"
| "compare_values_64 comp_sge a b = vi1 (b \<le>s a)"
| "compare_values_64 comp_slt a b = vi1 (a <s b)"
| "compare_values_64 comp_sle a b = vi1 (a \<le>s b)"

(* TODO: support pointers *)
fun compare_values :: "llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values c (vi32 a) (vi32 b) = ok (compare_values_32 c a b)"
| "compare_values c (vi64 a) (vi64 b) = ok (compare_values_64 c a b)"
| "compare_values _ _ _ = err incompatible_types"

fun same_signs32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "same_signs32 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"
fun same_signs64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "same_signs64 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if same_signs32 a b then compare_values c (vi32 a) (vi32 b) else ok poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if same_signs64 a b then compare_values c (vi64 a) (vi64 b) else ok poison)"
| "compare_values_sign True c _ _ = err incompatible_types"

definition execute_icmp :: "llvm_identifier \<Rightarrow> llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state result" where
  "execute_icmp name same_sign cond v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    return (set_register name res s)
  }"

lemma icmp32_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s v1 = Some (vi32 v1')" "register_\<alpha> s v2 = Some (vi32 v2')" "(if ss then same_signs32 v1' v2' else True)"
  shows "wp (execute_icmp name ss cond v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_32 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_intro; auto; intro wp_intro; auto)

lemma icmp64_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s v1 = Some (vi64 v1')" "register_\<alpha> s v2 = Some (vi64 v2')" "(if ss then same_signs64 v1' v2' else True)"
  shows "wp (execute_icmp name ss cond v1 v2 s) (\<lambda>s'. memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_64 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_intro; auto; intro wp_intro; auto)



section "Instruction wrapper"

fun execute_instruction :: "llvm_instruction \<Rightarrow> state \<Rightarrow> state result" where
  (* Allocate new memory value on the stack, and set the specified register to its address. *)
  "execute_instruction (alloca name type align) s = execute_alloca name s"
  (* Read address from pointer and store value in the stack or the heap. *)
| "execute_instruction (store type value pointer align) s = execute_store value pointer s"
  (* Read address from pointer and load value from either the stack or the heap. *)
| "execute_instruction (load name type pointer align) s = execute_load name pointer s"
  (* Get values, add according to wrap option (or poison), and store in register. *)
| "execute_instruction (add name wrap type v1 v2) s = execute_add name wrap v1 v2 s"
  (* Get values, do comparison, and store in register. *)
| "execute_instruction (icmp name same_sign cond type v1 v2) s = execute_icmp name same_sign cond v1 v2 s"

lemma [wp_intro]: "wp (execute_alloca name s) Q \<Longrightarrow> wp (execute_instruction (alloca name type align) s) Q"
  by simp
lemma [wp_intro]: "wp (execute_store value pointer s) Q \<Longrightarrow> wp (execute_instruction (store type value pointer align) s) Q"
  by simp
lemma [wp_intro]: "wp (execute_load name pointer s) Q \<Longrightarrow> wp (execute_instruction (load name type pointer align) s) Q"
  by simp
lemma [wp_intro]: "wp (execute_add name wrap v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (add name wrap type v1 v2) s) Q"
  by simp
lemma [wp_intro]: "wp (execute_icmp name same_sign cond v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (icmp name same_sign cond type v1 v2) s) Q"
  by simp


section "Phi nodes"

fun phi_lookup :: "llvm_identifier option \<Rightarrow> (llvm_identifier * llvm_value_ref) list \<Rightarrow> llvm_value_ref result" where
  "phi_lookup l ls = do {
    prev \<leftarrow> some_or_err l phi_no_previous_block;
    assert phi_label_not_distinct (distinct (map fst ls));
    some_or_err (map_of ls prev) phi_label_not_found
  }"

definition execute_phi :: "llvm_identifier option \<Rightarrow> llvm_phi_node \<Rightarrow> state \<Rightarrow> state result" where
  "execute_phi prev p s = (case p of phi name type values \<Rightarrow> do {
    v \<leftarrow> phi_lookup prev values;
    v' \<leftarrow> get_register s v;
    return (set_register name v' s)
  })"

lemma phi_wp_intro[THEN consequence, wp_intro]:
  assumes "p = phi name t values"
  assumes "distinct (map fst values)"
  assumes "pre = Some pre'" "map_of values pre' = Some v" "register_\<alpha> s v = Some v'"
  shows "wp (execute_phi pre p s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  using assms
  by (simp; intro wp_intro; simp)


fun execute_block :: "llvm_identifier option \<Rightarrow> llvm_instruction_block \<Rightarrow> state \<Rightarrow> (state * llvm_block_return) result" where
  "execute_block previous (p#ps, is, t) s = do {
    s' \<leftarrow> execute_phi previous p s;
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
| "execute_block previous (_, _, ret (Some (t, v))) s = do {
    res \<leftarrow> get_register s v;
    return (s, return_value (Some res))
  }"
| "execute_block previous (_, _, ret None) s = do {
    return (s, return_value None)
  }"




datatype instruction_state = execi "llvm_identifier option" llvm_instruction_block state
  | flowi state llvm_block_return
  | is_erri: erri
                                                    
inductive step_i :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>i" 50) where
  "step_i (execi pre ([],[],br_label l) s) (flowi s (branch_label l))"

| "get_register s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. get_register s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i erri"

| "(execi pre ([],[],ret None) s) \<rightarrow>\<^sub>i (flowi s (return_value None))"

| "get_register s v = ok v' \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i (flowi s (return_value (Some v')))"
| "get_register s v = err _ \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i erri"

| "execute_instruction i s = ok s' \<Longrightarrow>
    (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i (execi pre ([],is,t) s')"
| "execute_instruction i s = err _ \<Longrightarrow>
    (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i erri"

| "execute_phi pre p s = ok s' \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i erri"

abbreviation steps_i (infix "\<rightarrow>\<^sub>i*" 50) where
  "s \<rightarrow>\<^sub>i* s' \<equiv> step_i\<^sup>*\<^sup>* s s'"


fun n_steps_i :: "instruction_state \<Rightarrow> nat \<Rightarrow> instruction_state \<Rightarrow> bool" where
  "n_steps_i s 0 s'  = (s = s')"
| "n_steps_i s (Suc n) s' = (\<exists>x. s \<rightarrow>\<^sub>i x \<and> n_steps_i x n s')"

notation n_steps_i ("(_ \<rightarrow>\<^sub>i^_ _)" [51, 0, 51] 50)


lemma steps_i_exists_n_steps_i[simp]:
  assumes "fs \<rightarrow>\<^sub>i* fs'"
  shows "\<exists>n. fs \<rightarrow>\<^sub>i^n fs'"
  using assms n_steps_i.simps
  by (induction rule: converse_rtranclp_induct; blast)


definition terminal_state_i where
  "terminal_state_i s \<equiv> \<nexists>s'. s \<rightarrow>\<^sub>i s'"
notation terminal_state_i ("_ \<nexists>\<rightarrow>\<^sub>i" 50)

lemma term_state_i_simps[simp]:
  "\<And>pre b s. \<not> ((execi pre b s) \<nexists>\<rightarrow>\<^sub>i)"
  "\<And>s br. (flowi s br) \<nexists>\<rightarrow>\<^sub>i"
  "erri \<nexists>\<rightarrow>\<^sub>i"
  apply clarsimp
  subgoal for pre phis instrs ter l g s h
    unfolding terminal_state_i_def
    apply (cases phis; cases instrs; cases ter)
    subgoal for x apply (cases x) using step_i.intros apply blast
      subgoal for r apply (cases r) using result.exhaust step_i.intros by meson
      done
    using step_i.intros result.exhaust by meson+
  unfolding terminal_state_i_def using step_i.cases apply blast
  unfolding terminal_state_i_def using step_i.cases by blast


lemma steps_model_exec:
  assumes "execute_block pre b s = ok (s', br)"
  shows "(execi pre b s) \<rightarrow>\<^sub>i* (flowi s' br)"
proof (cases b)
  case (fields phis instrs ter)

  then show ?thesis
    apply (subst fields)
    using assms
    proof (induction phis arbitrary: b s)
      case Nil

      then show ?case
        proof (induction instrs arbitrary: b s)
          case Nil

          then show ?case
            apply (cases ter)
            subgoal for r by (cases r; auto simp: r_into_rtranclp step_i.intros)
              apply (auto simp: r_into_rtranclp step_i.intros)
            apply (auto split: llvm_value.splits)
             apply (rule r_into_rtranclp)
            using step_i.intros apply presburger 
            apply (rule r_into_rtranclp)
            using step_i.intros by presburger

        next
          case (Cons i ins)

          obtain is' where nextstate: "execute_instruction i s = ok is'"
            using Cons
            by auto

          then have "(execi pre ([],ins,ter) is')  \<rightarrow>\<^sub>i* (flowi s' br)"
            using Cons
            by auto

          then show ?case 
            using nextstate converse_rtranclp_into_rtranclp step_i.intros
            by meson
        qed
      next
        case (Cons p ps)

        obtain ps' where nextstate: "execute_phi pre p s = ok ps'"
          using Cons
          by auto

        then have "(execi pre (ps,instrs,ter) ps')  \<rightarrow>\<^sub>i* (flowi s' br)"
          using Cons
          by auto

        then show ?case
          using nextstate converse_rtranclp_into_rtranclp step_i.intros
          by meson
      qed
    qed



lemma single_step_eq_exec_step:
  assumes "(execi pre b s)  \<rightarrow>\<^sub>i (execi pre b' s')"
  assumes "execute_block pre b' s' = ok (s'', br)"
  shows "execute_block pre b s = ok (s'', br)"
  using assms step_i.cases
  by fastforce


lemma step_i_deterministic[simp]:
  assumes "s \<rightarrow>\<^sub>i s1"
  assumes "s \<rightarrow>\<^sub>i s2"
  shows "s1 = s2"
proof -
  show ?thesis
    using assms
    apply (cases s)
    apply (smt (verit) Pair_inject instruction_state.inject(1) list.discI
        llvm_terminator_instruction.distinct(3,5) llvm_terminator_instruction.inject(3)
        step_i.cases)
    
    apply (smt (verit) instruction_state.inject(1) list.discI llvm_terminator_instruction.distinct(1,5)
        llvm_terminator_instruction.inject(2) llvm_value.inject(1) prod.inject result.inject(1)
        step_i.cases)

    apply (smt (verit) Pair_inject instruction_state.inject list.discI
        llvm_terminator_instruction.distinct llvm_terminator_instruction.inject
        step_i.cases)
    
    apply (smt (verit, ccfv_SIG) Pair_inject instruction_state.inject(1) list.discI
        llvm_terminator_instruction.distinct(1,3) llvm_terminator_instruction.inject(1) option.distinct(1)
        step_i.cases)

    defer
         defer
    apply (smt (verit, ccfv_SIG) fst_conv instruction_state.sel(1,2,3) list.discI list.inject
        result.distinct(1) result.inject(1) snd_conv step_i.cases)
    apply (smt (verit, ccfv_SIG) fst_conv instruction_state.sel(1,2,3) list.discI list.inject
        result.distinct(1) result.inject(1) snd_conv step_i.cases)
    apply (smt (verit, ccfv_SIG) fst_conv instruction_state.sel(1,2,3) list.discI list.inject
        result.distinct(1) result.inject(1) snd_conv step_i.cases)
    apply (smt (verit, ccfv_SIG) fst_conv instruction_state.sel(1,2,3) list.discI list.inject
        result.distinct(1) result.inject(1) snd_conv step_i.cases)
    subgoal premises prems for stat v v' pre t
    proof (cases s2)
      case (execi x11 x12 x13)
      then show ?thesis
        using prems
        by (smt (verit) instruction_state.distinct(1,4) instruction_state.sel(2) list.discI prod.inject
          step_i.cases)
    next
      case (flowi st br)

      then obtain val where brdef: "br = return_value (Some val)"
        using prems Pair_inject instruction_state.distinct(1,6) instruction_state.inject(1,2)
            llvm_terminator_instruction.distinct(1,3) step_i.cases
        by (smt (verit, ccfv_SIG) llvm_terminator_instruction.inject(1) option.distinct(1))

      then have "get_register stat v = ok val"
        using prems flowi step_i.cases
        by blast

      then show ?thesis                        
        using brdef flowi prems(1,2,3,4) step_i.cases by auto
    next
      case erri
      have "\<forall>e. get_register stat v \<noteq> err e" using prems by simp
      then have "\<not>s \<rightarrow>\<^sub>i erri" using prems step_i.cases by blast
      then show ?thesis using prems erri by blast
    qed
  subgoal premises prems for stat v v' pre t
    proof (cases s2)
      case (execi x11 x12 x13)
      then show ?thesis
        using prems
        by (smt (verit) instruction_state.distinct(1,4) instruction_state.sel(2) list.discI prod.inject
          step_i.cases)
    next
      case (flowi st br)

      then obtain val where brdef: "br = return_value (Some val)"
        using prems Pair_inject instruction_state.distinct(1,6) instruction_state.inject(1,2)
            llvm_terminator_instruction.distinct(1,3) step_i.cases
        by (smt (verit, ccfv_SIG) llvm_terminator_instruction.inject(1) option.distinct(1))

      then have "get_register stat v = ok val"
        using prems flowi step_i.cases
        by blast

      then show ?thesis                        
        using brdef flowi prems(1,2,3,4) step_i.cases by auto
    next
      case erri
      have "\<forall>e. get_register stat v \<noteq> ok e" using prems by simp
      then show ?thesis using prems erri by blast
    qed
    done
qed


definition "wp_instrs s Q \<equiv> \<forall>s'. s \<rightarrow>\<^sub>i* s' \<and> terminal_state_i s' \<longrightarrow> \<not>is_erri s' \<and> Q s'"

lemma wp_impl_ok:
  assumes "wp x Q"
  shows "\<exists>v. x = ok v"
  using assms
  unfolding wp_gen_def
  by (cases x; simp)


named_theorems wp_instrs_intro

lemma instrs_phi_intro[wp_instrs_intro]:
  assumes "wp (execute_phi pre p s) (\<lambda>s'. wp_instrs (execi pre (ps, is, t) s') Q)"
  shows "wp_instrs (execi pre (p#ps, is, t) s) Q"
proof -
  obtain s' where nextstate: "execute_phi pre p s = ok s'"
    using assms wp_impl_ok
    by blast

  show ?thesis using nextstate assms converse_rtranclpE fst_conv instruction_state.sel(1,2,3) list.discI 
      list.inject result.distinct(1) result.simps(5) snd_conv step_i.cases term_state_i_simps(1)
    unfolding wp_gen_def wp_instrs_def
    by (smt (verit))
qed

lemma instrs_instr_intro[wp_instrs_intro]:
  assumes "wp (execute_instruction i s) (\<lambda>s'. wp_instrs (execi pre ([], is, t) s') Q)"
  shows "wp_instrs (execi pre ([], i#is, t) s) Q"
proof -
  obtain s' where nextstate: "execute_instruction i s = ok s'"
    using assms wp_impl_ok
    by blast

  show ?thesis using nextstate assms converse_rtranclpE fst_conv instruction_state.sel(1,2,3) list.discI 
      list.inject result.distinct(1) result.simps(5) snd_conv step_i.cases term_state_i_simps(1)
    unfolding wp_gen_def wp_instrs_def
    by (smt (verit))
qed

lemma block_ret_Some_wp_intro[wp_instrs_intro]:
  assumes "register_\<alpha> s value = Some v"
  assumes "Q (flowi s (return_value (Some v)))"
  shows "wp_instrs (execi pre ([], [], ret (Some (type, value))) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  subgoal premises prems for s'
    proof -
      have "(execi pre ([], [], ret (Some (type, value))) s) \<rightarrow>\<^sub>i (flowi s (return_value (Some v)))"
        using prems step_i.intros register_\<alpha>_eq_get_register
        by auto

        then show ?thesis using step_i_deterministic
          by (smt (verit, ccfv_SIG)
              converse_rtranclpE instruction_state.distinct(6) is_erri_def prems(2,3,4) step_i.cases
              term_state_i_simps(1,2))
    qed
  done

lemma block_ret_None_wp_intro[wp_instrs_intro]:
  assumes "Q (flowi s (return_value None))"
  shows "wp_instrs (execi pre ([], [], ret None) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  subgoal premises prems for s'
    proof -
      have "step_i (execi pre ([], [], ret None) s) (flowi s (return_value None))"
        using prems step_i.intros
        by auto

        then show ?thesis using step_i_deterministic
          by (smt (verit, ccfv_SIG)
              converse_rtranclpE instruction_state.distinct(6) is_erri_def prems step_i.cases
              term_state_i_simps(1,2))
    qed
  done


lemma block_br_label_wp_intro[wp_instrs_intro]:
  assumes "Q (flowi s (branch_label l))"
  shows "wp_instrs (execi pre ([], [], br_label l) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  by (smt (verit) converse_rtranclpE instruction_state.disc instruction_state.inject list.discI
      llvm_terminator_instruction.distinct llvm_terminator_instruction.inject prod.inject
      result.distinct(1) result.inject(1) step_i.cases term_state_i_simps(1,2))

lemma block_br_i1_wp_intro[wp_instrs_intro]:
  assumes "register_\<alpha> s value = Some (vi1 b)"
  assumes "b \<Longrightarrow> Q (flowi s (branch_label l1))"
  assumes "\<not>b \<Longrightarrow> Q (flowi s (branch_label l2))"
  shows "wp_instrs (execi pre ([], [], br_i1 value l1 l2) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  by (smt (verit) converse_rtranclpE instruction_state.disc(8) instruction_state.inject(1) list.discI
      llvm_terminator_instruction.distinct(1,5) llvm_terminator_instruction.inject(2) llvm_value.inject(1)
      prod.inject result.inject(1) step_i.cases term_state_i_simps(1,2) register_\<alpha>_eq_get_register)



end