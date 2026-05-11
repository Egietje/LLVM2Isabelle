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

find_consts name: tranc

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
  assumes "fs \<rightarrow>* fs'"
  assumes "terminal_state fs'"
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


definition "wp_steps fs Q \<equiv> \<forall>fs'. fs \<rightarrow>* fs' \<and> terminal_state fs' \<longrightarrow> (\<not>is_berr fs') \<and> (Q (state fs') (ret_value fs'))"


type_synonym precondition  = "state \<Rightarrow> bool"
type_synonym preconditions = "((llvm_identifier option * llvm_identifier) * precondition) list"
type_synonym postcondition = "state \<Rightarrow> llvm_value option \<Rightarrow> bool"

fun predicate_for_all where
  "predicate_for_all P [] = True"
| "predicate_for_all P (((p,l),pre)#pres) = (P p l \<and> predicate_for_all P pres)"

context
  fixes annotations :: "preconditions"
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
  | bbranch _ p l \<Rightarrow> map_of annotations (p,l) \<noteq> None
  )"

definition "annotation_holds fs \<equiv>
  (case fs of
    berr \<Rightarrow> False
  | bret s v \<Rightarrow> post s v
  | bbranch s p l \<Rightarrow> 
    (case map_of annotations (p,l) of
      None \<Rightarrow> False
    | Some annot \<Rightarrow> annot s
    )
  )"


definition step_until :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" where
  "step_until fs fs' \<equiv> step fs fs' \<and> \<not>has_annotation fs"

definition annotated_step :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "annotated_step s s' \<equiv> (\<exists>x. s \<rightarrow> x \<and> step_until\<^sup>*\<^sup>* x s') \<and> (has_annotation s' \<or> is_berr s')"
abbreviation annotated_steps :: "flow_state \<Rightarrow> flow_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "fs \<Rightarrow>* fs' \<equiv> annotated_step\<^sup>*\<^sup>* fs fs'"



definition wp_step where
  "wp_step fs Q \<equiv> (\<forall>fs'. step fs fs' \<longrightarrow> \<not>is_berr fs' \<and> Q fs')"

definition wp_steps_until where
  "wp_steps_until fs Q \<equiv> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> \<not>is_berr fs \<longrightarrow> \<not>is_berr fs') \<and> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> has_annotation fs' \<longrightarrow> Q fs')"

definition wp_annotated_step where
  "wp_annotated_step fs Q \<equiv> (\<forall>fs'. annotated_step fs fs' \<longrightarrow> \<not>is_berr fs' \<and> Q fs')"

lemma wp_step_intro:
  assumes "map_of (llvm_function.blocks f) l = Some b"
  assumes "wp (execute_block p b s) (\<lambda>(s', r). case r of branch_label l' \<Rightarrow> Q (bbranch s' (Some l) l') | return_value v \<Rightarrow> Q (bret s' (Some v)))"
  shows "wp_step (bbranch s p l) Q"
  using assms
  unfolding wp_step_def wp_gen_def step_def
  by (auto split: result.splits llvm_block_return.splits)

lemma wp_steps_until_intro:
  assumes "has_annotation fs \<Longrightarrow> Q fs"
  assumes "\<not>has_annotation fs \<Longrightarrow> wp_step  fs (\<lambda>fs'. wp_steps_until fs' Q)"
  shows "wp_steps_until fs Q"
  using assms converse_rtranclpE step_until_def
  unfolding wp_steps_until_def wp_step_def
  by metis

lemma wp_annotated_step_intro:
  assumes "wp_step fs (\<lambda>fs'. wp_steps_until fs' Q)"
  shows "wp_annotated_step fs Q"
  using assms
  unfolding wp_annotated_step_def wp_step_def annotated_step_def wp_steps_until_def
  by blast



definition "floyd_cond s p l \<equiv> wp_annotated_step (bbranch s p l) (\<lambda>fs'. annotation_holds fs')"


definition floyd_vc :: "bool" where
  "floyd_vc \<equiv>
    map_of annotations (None, first_label) \<noteq> None
    \<and> (\<forall>p l. map_of annotations (p,l) \<noteq> None \<longrightarrow> (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l))"

lemma predicate_for_all_impl_for_all_map_of:
  assumes "predicate_for_all (\<lambda>p l. (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l)) a"
  shows "(\<forall>p l. map_of a (p,l) \<noteq> None \<longrightarrow> (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l))"
  using assms
  apply (induction a)
  subgoal by force
  subgoal for annot annots
    apply (intro allI impI)
    subgoal for p l s
      apply (cases "annot")
      subgoal for br pre
        apply (cases "br = (p,l)")
        subgoal
          by (metis (no_types, lifting) predicate_for_all.simps(2))
        subgoal premises prems
        proof -
          have "predicate_for_all (\<lambda>p l. (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l)) annots" using prems
            using predicate_for_all.elims(2) by blast 
          then show ?thesis
            by (metis map_of_Cons_code(2) prems(1,3,4,5,6))
        qed
        done
      done
    done
  done

lemma floyd_vc_intro:
  assumes "map_of annotations (None, first_label) \<noteq> None"
  assumes "predicate_for_all (\<lambda>p l. (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l)) annotations"
  shows "floyd_vc"
  unfolding floyd_vc_def
  using predicate_for_all_impl_for_all_map_of assms
  by blast

lemma floyd_vc_impl_annotation_holds:
  assumes "floyd_vc"
  shows "\<forall>fs fs'. annotation_holds fs \<and> fs \<Rightarrow> fs' \<longrightarrow> annotation_holds fs'"
  using assms
  unfolding floyd_vc_def floyd_cond_def wp_annotated_step_def has_annotation_def annotated_step_def annotation_holds_def has_annotation_def step_def
  apply (auto split: flow_state.splits) by force+
  


lemma floyd_vc_impl_annotated_steps_hold:
  assumes "fs \<Rightarrow>* fs'"
  assumes "floyd_vc"
  assumes "annotation_holds fs"
  shows "annotation_holds fs'"
  using assms floyd_vc_impl_annotation_holds
  by (induction rule: converse_rtranclp_induct; blast)

lemma exists_first_cutpoint:
  assumes "fs \<rightarrow>^n fs'"
  assumes "is_berr fs' \<or> has_annotation fs'"
  shows "\<exists>fsp m. step_until\<^sup>*\<^sup>* fs fsp \<and> (is_berr fsp \<or> has_annotation fsp) \<and> fsp \<rightarrow>^m fs' \<and> m \<le> n"
  using assms
  proof (induction n arbitrary: fs)
    case 0
    
    then show ?case
      by force
  next
    case (Suc n)
  
    then show ?case
      by (smt (verit, ccfv_threshold) n_steps.elims(1) nat.inject nat_le_linear not_less_eq_eq
          r_into_rtranclp rtranclp.rtrancl_refl rtranclp_trans step_until_def)
  qed


lemma steps_to_annotation_impl_annotated_steps:
  assumes path: "fs \<rightarrow>* fs'"
  assumes annot: "has_annotation fs' \<or> is_berr fs'"
  shows "fs \<Rightarrow>* fs'"
proof -
  obtain n where ndef: "fs \<rightarrow>^n fs'" using path steps_exists_n_steps by blast
  
  then show ?thesis
  proof (induction n arbitrary: fs rule: less_induct)
    case (less n)

    then show ?case
      proof (cases "n")
        case 0
        then show ?thesis
        using less by fastforce
      next
        case (Suc n')
        then obtain fs1 where fs1def1: "fs \<rightarrow> fs1" and fs1def: "fs1 \<rightarrow>^n' fs'"
          using less ndef
          by auto

        obtain fsa m where "step_until\<^sup>*\<^sup>* fs1 fsa" "has_annotation fsa \<or> is_berr fsa" "fsa \<rightarrow>^m fs'" "m \<le> n'"
          using fs1def exists_first_cutpoint annot
          by blast

      then have "fs \<Rightarrow> fsa" using fs1def1 unfolding annotated_step_def by blast

      also from less.IH[OF _ \<open>fsa \<rightarrow>^m fs'\<close>] \<open>m \<le> n'\<close> Suc annot have "fsa \<Rightarrow>* fs'" by force
      
      finally show ?thesis .
      qed
    qed
  qed


lemma floyd_vc_impl_wp_step:
  assumes "floyd_vc"
  assumes "annotation_holds fs"
  assumes "fs = bbranch s None first_label"
  shows "wp_steps fs post"
  using assms 
  unfolding floyd_vc_def floyd_cond_def wp_steps_def
  by (metis (no_types, lifting) Steps.annotation_holds_def Steps.has_annotation_def assms(1)
      flow_state.case_eq_if floyd_vc_impl_annotated_steps_hold steps_to_annotation_impl_annotated_steps
      terminal_non_err)

end


end



end