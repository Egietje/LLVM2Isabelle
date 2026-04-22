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


definition "wp_blocks prev label blocks Q s = wp (execute_blocks prev label blocks s) Q"

lemma wp_blocks_intro:
  assumes "map_of blocks label = Some block"
  assumes "wp_block prev block (\<lambda>(s',r). case r of
    branch_label l \<Rightarrow> wp_blocks (Some label) l blocks Q s'
  | return_value v \<Rightarrow> Q (s', Some v)) s"
  shows "wp_blocks prev label blocks Q s"
  using assms
  unfolding wp_blocks_def wp_block_def
  apply (simp add: execute_blocks.simps)
  apply (cases "execute_block prev block s"; simp)
  subgoal for x apply (cases x; simp)
    subgoal for s' r apply (cases r; simp)
       apply (intro wp_intro) unfolding wp_gen_def apply simp apply simp subgoal for l' apply (cases "map_of blocks l'") apply simp subgoal for block apply (cases "execute_block (Some label) block s'"; simp add: execute_blocks.simps)
          done done done done unfolding wp_gen_def by simp

lemmas [code] = execute_blocks.simps

fun execute_function :: "llvm_function \<Rightarrow> state \<Rightarrow> (state * llvm_value option) result" where
  "execute_function (func _ ((l,b)#ls)) s = execute_blocks None l ((l,b)#ls) s"
| "execute_function _ s = ok (s, None)"



datatype (discs_sels) blocks_state = 
    is_berr: berr 
    | bret (state: state) (ret_value: "llvm_value option") 
    | bbranch (state: state) "llvm_identifier option" "llvm_identifier"


context fixes program :: "llvm_function"
begin

fun branch_step :: "blocks_state \<Rightarrow> blocks_state" where
  "branch_step (berr) = berr"
| "branch_step (bret s v) = bret s v"
| "branch_step (bbranch s prev lab) = ((case map_of (llvm_function.blocks program) lab of 
        None \<Rightarrow> berr 
      | Some block \<Rightarrow> (case execute_block prev block s of 
          err _ \<Rightarrow> berr 
        | ok (s', return_value v) \<Rightarrow> bret s' (Some v)
        | ok (s', branch_label l) \<Rightarrow> bbranch s' (Some lab) l))
  )"

definition "step s s' \<equiv> is_bbranch s \<and> s' = branch_step s"


definition "terminal_state s \<equiv> \<nexists>s'. step s s'"

lemma terminal_state_simps[simp]: 
  "terminal_state berr"
  "terminal_state (bret s v)"
  "\<not>terminal_state (bbranch s prev lab)"
  unfolding terminal_state_def step_def
  by (auto)

lemma terminal_steps_refl[simp]: "terminal_state s \<Longrightarrow> step\<^sup>*\<^sup>* s s' \<longleftrightarrow> s'=s"
  unfolding terminal_state_def
  by (auto elim: converse_rtranclpE)

lemma terminal_non_err[simp]: "terminal_state s \<and> \<not>is_berr s \<longleftrightarrow> is_bret s"
  by (cases s; auto)



lemma step_eq_exec_blocks:
  assumes "step\<^sup>*\<^sup>* bs bs'"
  assumes "terminal_state bs'"
  assumes "bs = bbranch s prev lab"
  assumes "\<not> is_berr bs'"
  shows
    "execute_blocks prev lab (llvm_function.blocks program) s = ok (state bs', ret_value bs')"
  using assms
proof (induction arbitrary: s prev lab rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case
    by (subst execute_blocks.simps; auto split: option.splits result.splits llvm_block_return.splits simp: step_def)
qed

lemma bla:
  assumes "step\<^sup>*\<^sup>* x (bbranch s p l)" "precond s"
  assumes "\<And>s. precond s \<longrightarrow> step\<^sup>*\<^sup>* (bbranch s p l) y"
  shows "step\<^sup>*\<^sup>* x y"
  using assms
  by fastforce

lemma
  assumes "step\<^sup>*\<^sup>* bs (bbranch s' p l)" "precond s'"
  assumes "bs = bbranch s prev lab"
  assumes "\<And>s. precond s \<longrightarrow> step\<^sup>*\<^sup>* (bbranch s p l) bs'"
  assumes "\<not> is_berr bs'"
  assumes "terminal_state bs'"
  shows "execute_blocks prev lab (llvm_function.blocks program) s = ok (state bs', ret_value bs')"
  using assms bla step_eq_exec_blocks by metis


definition "wp_steps bs Q \<equiv> \<forall>s' v. step\<^sup>*\<^sup>* bs (bret s' v) \<longrightarrow> Q s' v"

lemma branch_step_exists[simp]:
  "is_bbranch bs \<Longrightarrow> \<exists>bs'. step bs bs'"
  unfolding step_def by simp
lemma branch_step_unique[simp]:
  "is_bbranch bs \<Longrightarrow> \<nexists>bs' bs''. step bs bs' \<and> step bs bs'' \<and> bs' \<noteq> bs''"
  unfolding step_def by simp

lemma execute_and_step[simp]:
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "execute_block p b s = ok (s', br)"
  assumes "bs' = (case br of branch_label l' \<Rightarrow> bbranch s' (Some l) l' | return_value v \<Rightarrow> bret s' (Some v))"
  shows "step (bbranch s p l) bs'"
  using assms
  unfolding step_def by simp

lemma step_branch_ret_intermediate[simp]:
  assumes "step\<^sup>*\<^sup>* (bbranch s p l) (bret s' v)"
  shows "\<exists>bs. step (bbranch s p l) bs \<and> step\<^sup>*\<^sup>* bs (bret s' v)"
  using assms converse_rtranclpE
  by fastforce

lemma testasd[simp]:
  assumes "local.step (bbranch s p l) (bbranch (a, aa, b) x32 x33)"
  assumes "local.step\<^sup>*\<^sup>* (bbranch s p l) (bret (r', s', h') v)"
  shows "local.step\<^sup>*\<^sup>* (bbranch (a, aa, b) x32 x33)  (bret (r', s', h') v)"
  using assms step_branch_ret_intermediate step_def by auto

lemma step_branch_prev_label[simp]:
  assumes "local.step (bbranch s p l) (bbranch s' p' l')"
  shows "p' = Some l"
  using assms
  unfolding step_def
  by (auto split: option.splits result.splits llvm_block_return.splits)

lemma blaskd:
  assumes "\<exists>bs. step (bbranch s p l) bs \<and> \<not>is_berr bs"
  assumes BRANCH:
    "\<And>s' l'. step (bbranch s p l) (bbranch s' (Some l) l')
       \<Longrightarrow> wp_steps (bbranch s' (Some l) l') Q"
  assumes RETURN:
    "\<And>s' v. step (bbranch s p l) (bret s' v)
       \<Longrightarrow> Q s' v"
  shows "wp_steps (bbranch s p l) Q"
  using assms
  apply (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits)
  subgoal for bs
    apply (cases bs)
    subgoal
      by (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits)
    subgoal
      unfolding wp_steps_def
      apply (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits)
      by (metis step_branch_ret_intermediate step_def terminal_state_simps(2) terminal_steps_refl)
    unfolding wp_steps_def
    apply (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits)
    subgoal for a b c d e f g h i
      apply (cases "d = Some l")
      by (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits)
    done
  done

lemma ahsjdihasudhs:
  "map_of (llvm_function.blocks program) l = Some b \<Longrightarrow> execute_block p b s = ok (s', branch_label l') \<Longrightarrow> step (bbranch s p l) (bbranch s' (Some l) l')"
  unfolding step_def
  by (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits option.splits simp: step_def)
lemma ahsjdihasudha:
  "map_of (llvm_function.blocks program) l = Some b \<Longrightarrow> execute_block p b s = ok (s', return_value v) \<Longrightarrow> step (bbranch s p l) (bret s' (Some v))"
  unfolding step_def
  by (auto split: result.splits llvm_block_return.splits blocks_state.splits prod.splits option.splits simp: step_def)
lemma heloks:
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "\<exists>x. execute_block p b s = ok x"
  shows "\<exists>bs. step (bbranch s p l) bs \<and> \<not>is_berr bs"
  using assms
  unfolding step_def
  by (auto split: llvm_block_return.splits)

lemma asdsakmd:
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "\<exists>x. execute_block p b s = ok x"
  assumes
    "\<And>s' l'. execute_block p b s = ok (s', branch_label l')
       \<Longrightarrow> wp_steps (bbranch s' (Some l) l') Q"
  shows
    "\<And>s' l'. step (bbranch s p l) (bbranch s' (Some l) l')
       \<Longrightarrow> wp_steps (bbranch s' (Some l) l') Q"
  using assms unfolding step_def by (auto split: llvm_block_return.splits)

lemma intro_helper:
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "\<exists>x. execute_block p b s = ok x"
  assumes BRANCH:
    "\<And>s' l'. execute_block p b s = ok (s', branch_label l')
       \<Longrightarrow> wp_steps (bbranch s' (Some l) l') Q"
  assumes RETURN:
    "\<And>s' v. execute_block p b s = ok (s', return_value v)
       \<Longrightarrow> Q s' (Some v)"
  shows "wp_steps (bbranch s p l) Q"
  using assms apply (elim exE) subgoal for r
    apply (cases r) subgoal for s' br apply (cases br)
      subgoal for v
        apply (simp)
        unfolding wp_steps_def apply auto
        by (metis Blocks.ahsjdihasudha Blocks.terminal_steps_refl blocks_state.inject(1) step_branch_ret_intermediate
            step_def terminal_state_simps(2))
      subgoal for l'
        apply simp
        unfolding wp_steps_def
        apply auto
        by (metis Blocks.ahsjdihasudhs step_branch_ret_intermediate
            step_def)
      done
    done
  done

lemma wp_steps_intro_basic:
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "wp (execute_block p b s) (\<lambda>(s', br). case br of 
      return_value v \<Rightarrow> Q s' (Some v) 
    | branch_label l' \<Rightarrow> wp_steps (bbranch s' (Some l) l') Q)"
  shows "wp_steps (bbranch s p l) Q"
  using assms 
  unfolding wp_gen_def
  apply (cases "execute_block p b s"; simp)
  subgoal for r
    apply (cases r)
    subgoal for s' br
      apply (cases br; simp)
      apply (rule intro_helper) apply simp apply fast apply simp apply simp 
      apply (rule intro_helper) apply simp apply fast apply simp apply simp
      done
    done
  done

type_synonym precondition  = "state \<Rightarrow> bool"
type_synonym preconditions = "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> precondition option"
type_synonym postcondition = "state \<Rightarrow> llvm_value option \<Rightarrow> bool"

definition "first_label \<equiv> (case llvm_function.blocks program of ((l,b)#bs) \<Rightarrow> l | [] \<Rightarrow> undefined)"

definition PRECONDS :: "preconditions \<Rightarrow> bool" where "PRECONDS pres \<equiv> True"

definition verify_function :: "precondition \<Rightarrow> preconditions \<Rightarrow> postcondition \<Rightarrow> bool" where
  "verify_function pre pres post \<equiv> (\<forall>s. PRECONDS pres \<and> pre s \<longrightarrow> wp_steps (bbranch s None first_label) post)"
definition wp_steps_intro_post where
  "wp_steps_intro_post Q pres l \<equiv> (\<lambda>(s', br).
          case br of
            return_value v \<Rightarrow> Q s' (Some v)
          | branch_label l' \<Rightarrow>
              (case pres (Some l) l' of
                Some precond \<Rightarrow> precond s' \<and> (\<forall>s. precond s \<longrightarrow> wp_steps (bbranch s (Some l) l') Q)
              | None \<Rightarrow> wp_steps (bbranch s' (Some l) l') Q
              )
          )"

lemma wp_steps_intro:
  assumes "PRECONDS pres"
  assumes "map_of (llvm_function.blocks program) l = Some b"
  assumes "wp (execute_block p b s) (wp_steps_intro_post Q pres l)"
  shows "wp_steps (bbranch s p l) Q"
  using assms
  unfolding wp_gen_def wp_steps_intro_post_def
  apply (cases "execute_block p b s"; simp)
  subgoal for r
    apply (cases r)
    subgoal for s' br
      apply (cases br)
      using wp_steps_intro_basic apply simp
      subgoal for l'
        apply (cases "pres (Some l) l'")
        using wp_steps_intro_basic apply simp
        apply (rule wp_steps_intro_basic) apply fast
        unfolding wp_gen_def apply simp
          by (metis set_register.elims)
      done
    done
  done



end








end