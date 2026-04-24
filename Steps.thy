theory Steps
  imports Blocks
begin

datatype (discs_sels) flow_state = 
    is_berr: berr 
    | bret (state: state) (ret_value: "llvm_value option") 
    | bbranch (state: state) "llvm_identifier option" "llvm_identifier"


context fixes f :: "llvm_function"
begin

definition "first_label \<equiv> (case llvm_function.blocks f of ((l,b)#bs) \<Rightarrow> l)"

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
  assumes "bs \<rightarrow>* bs'"
  shows "\<exists>n. bs \<rightarrow>^n bs'"
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
  "is_bbranch bs \<Longrightarrow> \<exists>bs'. step bs bs'"
  "is_bbranch bs \<Longrightarrow> \<nexists>bs' bs''. step bs bs' \<and> step bs bs'' \<and> bs' \<noteq> bs''"
  unfolding step_def by simp+

lemma step_models_execute_blocks_ok:
  assumes "bs \<rightarrow>* bs'"
  assumes "terminal_state bs'"
  assumes "bs = bbranch s prev lab"
  assumes "\<not> is_berr bs'"
  shows   "execute_blocks prev lab (llvm_function.blocks f) s = ok (state bs', ret_value bs')"
  using assms
  apply (induction arbitrary: s prev lab rule: converse_rtranclp_induct)
  apply simp
  by (subst execute_blocks.simps; auto split: option.splits result.splits llvm_block_return.splits simp: step_def)

lemma step_models_execute_blocks_err:
  assumes "bs \<rightarrow>* bs'"
  assumes "terminal_state bs'"
  assumes "bs = bbranch s prev lab"
  assumes "is_berr bs'"
  shows   "\<exists>e. execute_blocks prev lab (llvm_function.blocks f) s = err e"
  using assms
  apply (induction arbitrary: s prev lab rule: converse_rtranclp_induct)
  apply simp
  by (subst execute_blocks.simps; auto split: option.splits result.splits llvm_block_return.splits simp: step_def)


definition "wp_steps bs Q \<equiv> \<forall>bs'. bs \<rightarrow>* bs' \<and> terminal_state bs' \<longrightarrow> \<not>is_berr bs' \<and> Q (state bs') (ret_value bs')"


type_synonym precondition  = "state \<Rightarrow> bool"
type_synonym preconditions = "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> precondition option"
type_synonym postcondition = "state \<Rightarrow> llvm_value option \<Rightarrow> bool"


context
  fixes annotations :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> precondition option"
  fixes post :: "postcondition"
begin



lemma
  assumes "\<forall>bs'. bs \<rightarrow>* bs' \<and> terminal_state bs' \<longrightarrow> \<not>is_berr bs' \<and> post (state bs') (ret_value bs')"
  shows "wp_steps bs post"
  unfolding wp_steps_def using assms by blast


definition "has_annotation bs \<equiv>
  (case bs of
    berr \<Rightarrow> False
  | bret _ _ \<Rightarrow> True
  | bbranch _ p l \<Rightarrow> (annotations p l) \<noteq> None
  )"

definition "annotation_holds bs \<equiv>
  (case bs of
    berr \<Rightarrow> False
  | bret s v \<Rightarrow> post s v
  | bbranch s p l \<Rightarrow> has_annotation bs \<and>
    (case (annotations p l) of
      None \<Rightarrow> False
    | Some annot \<Rightarrow> annot s
    )
  )"

definition step_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "step_until bs bs' \<equiv> step bs bs' \<and> \<not>has_annotation bs"
abbreviation steps_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "bs \<Rightarrow>* bs' \<equiv> step_until\<^sup>*\<^sup>* bs bs'"

fun n_steps_until :: "flow_state \<Rightarrow> nat \<Rightarrow> flow_state \<Rightarrow> bool" where
  "n_steps_until s 0 s'  = (s = s')"
| "n_steps_until s (Suc n) s' = (\<exists>x. s \<Rightarrow> x \<and> n_steps_until x n s')"

notation n_steps_until ("(_ \<Rightarrow>^_ _)" [51, 0, 51] 50)

definition keep_stepping_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*a" 50) where
  "keep_stepping_until s s' \<equiv> (\<exists>x. s \<rightarrow> x \<and> x \<Rightarrow>* s') \<and> (has_annotation s')"


lemma annotation_simps[simp]:
  "\<nexists>bs'. step_until bs bs' \<Longrightarrow> \<not>is_berr bs \<Longrightarrow> has_annotation bs"
  "annotations p l \<noteq> None \<Longrightarrow> \<forall>s. has_annotation (bbranch s p l)"
  unfolding step_until_def has_annotation_def step_def
  by (auto split: flow_state.splits)

lemma step_until_single[simp]:
  "\<nexists>bs' bs''. step_until bs bs' \<and> step_until bs bs'' \<and> bs' \<noteq> bs''"
  unfolding step_until_def step_def by blast


lemma steps_until_models_steps:
  assumes "bs \<Rightarrow>* bs'"
  shows "bs \<rightarrow>* bs'"
  using assms
  unfolding step_until_def
  apply (induction rule: rtranclp_induct)
  by auto

lemma step_then_steps_until_models_steps:
  assumes "\<And>x. bs \<rightarrow> x \<and> x \<Rightarrow>* bs'"
  shows "bs \<rightarrow>* bs'"
  using assms steps_until_models_steps
  by blast


definition "floyd_cond s p l \<equiv> \<forall>bs'.
    (bbranch s p l) \<Rightarrow>*a bs'
    \<longrightarrow> \<not>is_berr bs' \<and> annotation_holds bs'"


definition floyd_vc :: "bool" where
  "floyd_vc \<equiv>
    annotations None first_label \<noteq> None
    \<and> (\<exists>s. annotation_holds (bbranch s None first_label))
    \<and> (\<forall>p l. annotations p l \<noteq> None \<longrightarrow> (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l))"


lemma floyd_vc_impl_annotation_holds:
  assumes "floyd_vc"
  assumes "\<And>x bs. annotation_holds bs \<longrightarrow> bs \<Rightarrow>*a bs'"
  shows "annotation_holds bs'"
  using assms
  unfolding floyd_vc_def floyd_cond_def has_annotation_def keep_stepping_until_def
  by fast

lemma floyd_vc_impl_post_cond:
  assumes "floyd_vc"
  assumes "\<And>bs x. annotation_holds bs \<longrightarrow> bs \<Rightarrow>*a bret s v"
  shows "post s v"
  using assms 
  unfolding floyd_vc_def floyd_cond_def has_annotation_def annotation_holds_def keep_stepping_until_def
  by force

lemma steps_until_glue_to_steps:
  assumes "bs \<rightarrow>* bs'"
  shows "\<exists>"

lemma floyd_vc_induct:
  assumes BASE: "\<exists>s. annotation_holds (bbranch s None first_label)"
  assumes STEP: "\<And>bs x bs'. annotation_holds bs \<and> bs \<rightarrow> x \<and> x \<Rightarrow>* bs' \<and> has_annotation bs' \<longrightarrow> annotation_holds bs'"
  assumes END: "\<exists>bs s' v. annotation_holds bs \<longrightarrow> bs \<rightarrow> x \<and> x \<Rightarrow>* bret s' v"
  shows ""



lemma floyd_vc_impl_wp_step:
  assumes "floyd_vc"
  assumes "bs = bbranch s None first_label"
  assumes "annotation_holds bs"
  shows "wp_steps bs post"
  using assms
proof (-)

  show ?thesis using floyd_vc_impl_post_cond floyd_vc_impl_annotation_holds unfolding wp_steps_def
    oops
qed
  


end


end



end