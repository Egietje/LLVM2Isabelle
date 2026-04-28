theory Steps
  imports Blocks
begin

datatype (discs_sels) flow_state = 
    is_berr: berr 
    | bret (state: state) (ret_value: "llvm_value option") 
    | bbranch (state: state) "llvm_identifier option" "llvm_identifier"


context fixes f :: "llvm_function"
begin

definition "first_label \<equiv> (case llvm_function.blocks f of ((l,b)#fs) \<Rightarrow> l)"

fun branch_step :: "flow_state \<Rightarrow> flow_state" where
  "branch_step (berr) = berr"
| "branch_step (bret s v) = bret s v"
| "branch_step (bbranch s prev lab) = ((case map_of (llvm_function.blocks f) lab of 
        None \<Rightarrow> berr 
      | Some block \<Rightarrow> (case execute_block prev block s of 
          err _ \<Rightarrow> berr 
        | ok (s', return_value v) \<Rightarrow> bret s' (Some v)
        | ok (s', branch_label l) \<Rightarrow> bbranch s' (Some lab) l))
  )"

definition step :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<rightarrow>" 50) where
  "step s s' \<equiv> is_bbranch s \<and> s' = branch_step s"

abbreviation steps :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<rightarrow>*" 50) where
  "s \<rightarrow>* s' \<equiv> step\<^sup>*\<^sup>* s s'"

fun n_steps :: "flow_state \<Rightarrow> nat \<Rightarrow> flow_state \<Rightarrow> bool" where
  "n_steps s 0 s'  = (s = s')"
| "n_steps s (Suc n) s' = (\<exists>x. s \<rightarrow> x \<and> n_steps x n s')"

notation n_steps ("(_ \<rightarrow>^_ _)" [51, 0, 51] 50)

lemma steps_exists_n_steps:
  assumes "fs \<rightarrow>* fs'"
  shows "\<exists>n. fs \<rightarrow>^n fs'"
  using assms n_steps.simps
  by (induction rule: converse_rtranclp_induct; blast)


definition "terminal_state s \<equiv> \<nexists>s'. s \<rightarrow> s'"

lemma terminal_state_simps[simp]: 
  "terminal_state berr"
  "terminal_state (bret s v)"
  "\<not>terminal_state (bbranch s prev lab)"
  unfolding terminal_state_def step_def
  by (auto)

lemma terminal_steps_refl[simp]:
  "terminal_state s \<Longrightarrow> s \<rightarrow>* s' \<longleftrightarrow> s'=s"
  unfolding terminal_state_def
  by (auto elim: converse_rtranclpE)

lemma terminal_non_err[simp]:
  "terminal_state s \<and> \<not>is_berr s \<longleftrightarrow> is_bret s"
  by (cases s; auto)

lemma step_deterministic[simp]:
  "is_bbranch fs \<Longrightarrow> \<exists>fs'. step fs fs'"
  "is_bbranch fs \<Longrightarrow> \<nexists>fs' fs''. step fs fs' \<and> step fs fs'' \<and> fs' \<noteq> fs''"
  unfolding step_def by simp+

lemma step_models_execute_blocks_ok:
  assumes "fs \<rightarrow>* fs'"
  assumes "terminal_state fs'"
  assumes "fs = bbranch s prev lab"
  assumes "\<not> is_berr fs'"
  shows   "execute_blocks prev lab (llvm_function.blocks f) s = ok (state fs', ret_value fs')"
  using assms
  apply (induction arbitrary: s prev lab rule: converse_rtranclp_induct)
  apply simp
  by (subst execute_blocks.simps; auto split: option.splits result.splits llvm_block_return.splits simp: step_def)

lemma step_models_execute_blocks_err:
  assumes "fs \<rightarrow>* fs'"
  assumes "terminal_state fs'"
  assumes "fs = bbranch s prev lab"
  assumes "is_berr fs'"
  shows   "\<exists>e. execute_blocks prev lab (llvm_function.blocks f) s = err e"
  using assms
  apply (induction arbitrary: s prev lab rule: converse_rtranclp_induct)
  apply simp
  by (subst execute_blocks.simps; auto split: option.splits result.splits llvm_block_return.splits simp: step_def)


definition "wp_steps fs Q \<equiv> \<forall>fs'. fs \<rightarrow>* fs' \<and> terminal_state fs' \<longrightarrow> \<not>is_berr fs' \<and> Q (state fs') (ret_value fs')"


type_synonym precondition  = "state \<Rightarrow> bool"
type_synonym preconditions = "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> precondition option"
type_synonym postcondition = "state \<Rightarrow> llvm_value option \<Rightarrow> bool"


context
  fixes annotations :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> precondition option"
  fixes post :: "postcondition"
begin



lemma
  assumes "\<forall>fs'. fs \<rightarrow>* fs' \<and> terminal_state fs' \<longrightarrow> \<not>is_berr fs' \<and> post (state fs') (ret_value fs')"
  shows "wp_steps fs post"
  unfolding wp_steps_def using assms by blast


definition "has_annotation fs \<equiv>
  (case fs of
    berr \<Rightarrow> False
  | bret _ _ \<Rightarrow> True
  | bbranch _ p l \<Rightarrow> (annotations p l) \<noteq> None
  )"

definition "annotation_holds fs \<equiv>
  (case fs of
    berr \<Rightarrow> False
  | bret s v \<Rightarrow> post s v
  | bbranch s p l \<Rightarrow> has_annotation fs \<and>
    (case (annotations p l) of
      None \<Rightarrow> False
    | Some annot \<Rightarrow> annot s
    )
  )"

definition step_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "step_until fs fs' \<equiv> step fs fs' \<and> \<not>has_annotation fs"
abbreviation steps_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "fs \<Rightarrow>* fs' \<equiv> step_until\<^sup>*\<^sup>* fs fs'"

fun n_steps_until :: "flow_state \<Rightarrow> nat \<Rightarrow> flow_state \<Rightarrow> bool" where
  "n_steps_until s 0 s'  = (s = s')"
| "n_steps_until s (Suc n) s' = (\<exists>x. s \<Rightarrow> x \<and> n_steps_until x n s')"

notation n_steps_until ("(_ \<Rightarrow>^_ _)" [51, 0, 51] 50)

definition keep_stepping_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*a" 50) where
  "keep_stepping_until s s' \<equiv> (\<exists>x. s \<rightarrow> x \<and> x \<Rightarrow>* s') \<and> (has_annotation s')"
abbreviation keep_stepping_until_closure :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*a*" 50) where
  "fs \<Rightarrow>*a* fs' \<equiv> keep_stepping_until\<^sup>*\<^sup>* fs fs'"


lemma annotation_simps[simp]:
  "\<nexists>fs'. step_until fs fs' \<Longrightarrow> \<not>is_berr fs \<Longrightarrow> has_annotation fs"
  "annotations p l \<noteq> None \<Longrightarrow> \<forall>s. has_annotation (bbranch s p l)"
  unfolding step_until_def has_annotation_def step_def
  by (auto split: flow_state.splits)

lemma step_until_single[simp]:
  "\<nexists>fs' fs''. step_until fs fs' \<and> step_until fs fs'' \<and> fs' \<noteq> fs''"
  unfolding step_until_def step_def by blast

lemma steps_until_models_steps:
  assumes "fs \<Rightarrow>* fs'"
  shows "fs \<rightarrow>* fs'"
  using assms
  unfolding step_until_def
  apply (induction rule: rtranclp_induct)
  by auto

lemma keep_stepping_until_models_steps:
  assumes "fs \<Rightarrow>*a fs'"
  shows "fs \<rightarrow>* fs'"
  using assms steps_until_models_steps
  unfolding keep_stepping_until_def
  by fastforce

lemma keep_stepping_impl_has_annotation:
  assumes "fs \<Rightarrow>*a fs'"
  shows "has_annotation fs'"
  using assms
  unfolding keep_stepping_until_def
  by blast


definition "floyd_cond s p l \<equiv> \<forall>fs'.
    (bbranch s p l) \<Rightarrow>*a fs'
    \<longrightarrow> \<not>is_berr fs' \<and> annotation_holds fs'"

definition floyd_vc :: "bool" where
  "floyd_vc \<equiv>
    annotations None first_label \<noteq> None
    \<and> (\<exists>s. annotation_holds (bbranch s None first_label))
    \<and> (\<forall>p l. annotations p l \<noteq> None \<longrightarrow> (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l))"


lemma floyd_vc_impl_annotation_holds:
  assumes "floyd_vc"
  shows "\<forall>fs fs'. annotation_holds fs \<and> fs \<Rightarrow>*a fs' \<longrightarrow> annotation_holds fs'"
  using assms
  apply (intro allI impI) subgoal for fs
  unfolding floyd_vc_def floyd_cond_def has_annotation_def keep_stepping_until_def annotation_holds_def has_annotation_def step_def
  by (cases fs; fastforce)
  done

lemma floyd_vc_impl_post_cond:
  assumes "floyd_vc"
  shows "\<forall>fs s v. annotation_holds fs \<and> fs \<Rightarrow>*a bret s v \<longrightarrow> post s v"
  using assms
  apply (intro allI impI) subgoal for fs
  unfolding floyd_vc_def floyd_cond_def has_annotation_def keep_stepping_until_def annotation_holds_def has_annotation_def step_def
  by (cases fs; fastforce)
  done

lemma floyd_vc_impl_annotation_holds_for_closure_helper:
  assumes "fs \<Rightarrow>*a* fs'"
  assumes "annotation_holds fs"
  assumes "floyd_vc"
  shows "annotation_holds fs'"
  using assms floyd_vc_impl_annotation_holds
  by (induction rule: rtranclp_induct; blast)

lemma floyd_vc_impl_annotation_holds_for_closure:
  assumes "floyd_vc"
  shows "\<forall>fs fs'. annotation_holds fs \<and> fs \<Rightarrow>*a* fs' \<longrightarrow> annotation_holds fs'"
  using assms floyd_vc_impl_annotation_holds_for_closure_helper
  by blast

lemma
  "fs \<Rightarrow>*a* fs' \<Longrightarrow> fs \<rightarrow>* fs'"
    apply (induction rule: converse_rtranclp_induct)
    apply fast
    using keep_stepping_until_models_steps
    by force 

lemma floyd_vc_impl_wp_step:
  assumes "floyd_vc"
  assumes "fs = bbranch s None first_label"
  assumes "annotation_holds fs"
  shows "wp_steps fs post"
  using assms
proof (-)

  show ?thesis using floyd_vc_impl_post_cond floyd_vc_impl_annotation_holds unfolding wp_steps_def
    oops
qed
  


end


end



end