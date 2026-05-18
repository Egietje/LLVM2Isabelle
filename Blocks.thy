theory Blocks
  imports "Instructions"
begin







fun get_parameter_values :: "(llvm_type * llvm_value_ref) list \<Rightarrow> state \<Rightarrow> (llvm_value list) result" where
  "get_parameter_values ((_, i)#ps) s = do {
    v \<leftarrow> get_register s i;
    vs \<leftarrow> get_parameter_values ps s;
    return (v#vs)
  }"
| "get_parameter_values [] _ = return []"

fun first_block :: "llvm_function \<Rightarrow> llvm_identifier option" where
  "first_block f = (case llvm_function.blocks f of ((l,_)#_) \<Rightarrow> Some l | _ \<Rightarrow> None)"


context                 
  fixes program :: llvm_program
begin

datatype step_state = sinstructions "llvm_identifier option" "llvm_identifier" (state: state) llvm_instruction_block llvm_labeled_blocks "(state \<Rightarrow> llvm_value option \<Rightarrow> step_state) option"
  | sbranch (state: state) "llvm_identifier option" llvm_identifier llvm_labeled_blocks "(state \<Rightarrow> llvm_value option \<Rightarrow> step_state) option"
  | sreturn (state: state) (retval: "llvm_value option") "(state \<Rightarrow> llvm_value option \<Rightarrow> step_state) option"
  | sfunc (state: state) llvm_identifier "llvm_value list" "(state \<Rightarrow> llvm_value option \<Rightarrow> step_state) option"
  | srestore (state: state) "llvm_identifier option" "llvm_value option" "llvm_identifier option" llvm_identifier llvm_instruction_block llvm_labeled_blocks "(state \<Rightarrow> llvm_value option \<Rightarrow> step_state) option"
  | is_err: serr

definition step :: "step_state \<Rightarrow> step_state \<Rightarrow> bool" (infix "\<rightarrow>" 51) where
  "step s s' \<equiv> (case s of
    sinstructions pre cur s ((phi name type values)#ps,is,t) lbs ss \<Rightarrow>
      (case execute_phi pre name values s of
        ok s \<Rightarrow> s' = sinstructions pre cur s (ps,is,t) lbs ss
      | _    \<Rightarrow> s' = serr
      )
  | sinstructions pre cur s ([],(call n ty f p)#is,t) lbs ss \<Rightarrow>
      (case get_parameter_values p s of
        ok ps \<Rightarrow> s' = sfunc s f ps (Some (\<lambda>s v. srestore s n v pre cur ([],is,t) lbs ss))
      | _     \<Rightarrow> s' = serr
      )
  | sinstructions pre cur s ([],i#is,t) lbs ss \<Rightarrow>
      (case execute_instruction i s of
        ok stat \<Rightarrow> s' = sinstructions pre cur stat ([],is,t) lbs ss
      | _       \<Rightarrow> s' = serr
      )
  | sinstructions pre cur s ([],[],br_label l) lbs ss \<Rightarrow>
      (s' = sbranch s (Some cur) l lbs ss)
  | sinstructions pre cur s ([],[],br_i1 b l1 l2) lbs ss \<Rightarrow>
      (case get_register s b of
        ok (vi1 b) \<Rightarrow> s' = sbranch s (Some cur) (if b then l1 else l2) lbs ss
      | _          \<Rightarrow> s' = serr
      )
  | sinstructions pre cur s ([],[],ret t v) lbs ss \<Rightarrow>
      (case get_register s v of
        ok v \<Rightarrow> s' = sreturn s (Some v) ss
      | _    \<Rightarrow> s' = serr
      )
  | sbranch s from to lbs ss \<Rightarrow>
      (case map_of lbs to of
        Some b \<Rightarrow> s' = sinstructions from to s b lbs ss
      | _      \<Rightarrow> s' = serr
      )
  | sreturn s v ss \<Rightarrow>
      (case ss of
        Some ss \<Rightarrow> s' = ss s v
      | None \<Rightarrow> False
      )
  | srestore s n v pre cur b lbs ss \<Rightarrow>
      (case n of \<comment> \<open> TODO restore stack to original size and restore local registers \<close>
        Some n \<Rightarrow>
          (case v of
            Some v \<Rightarrow> s' = sinstructions pre cur (set_register n v s) b lbs ss
          | None \<Rightarrow> s' = serr
          )
      | None \<Rightarrow> s' = sinstructions pre cur s b lbs ss
      )
  | sfunc s f p ss \<Rightarrow> 
    (case map_of (funcs program) f of \<comment> \<open> TODO store original stack and local registers \<close>
      Some f \<Rightarrow>
      (case first_block f of
        Some l \<Rightarrow> s' = sbranch s None l (llvm_function.blocks f) ss
      | None \<Rightarrow> s' = serr
      )
    | None \<Rightarrow> s' = serr
    )
  | serr \<Rightarrow> False
  )"

definition terminal_state where
  "terminal_state s \<equiv> \<nexists>s'. s \<rightarrow> s'"


abbreviation steps :: "step_state \<Rightarrow> step_state \<Rightarrow> bool" (infix "\<rightarrow>*" 50) where
  "s \<rightarrow>* s' \<equiv> step\<^sup>*\<^sup>* s s'"

fun n_steps :: "step_state \<Rightarrow> nat \<Rightarrow> step_state \<Rightarrow> bool" where
  "n_steps s 0 s'  = (s = s')"
| "n_steps s (Suc n) s' = (\<exists>x. s \<rightarrow> x \<and> n_steps x n s')"

notation n_steps ("(_ \<rightarrow>^_ _)" [51, 0, 51] 50)


lemma terminal_state_simps[simp]:
  "terminal_state serr"
  "terminal_state (sreturn s v None)"
  "\<not>terminal_state (sreturn s v (Some x))"
  "\<not>terminal_state (sinstructions pre cur s b lbs ss)"
  "\<not>terminal_state (sbranch s from to lbs ss)"
  "\<not>terminal_state (srestore s n v pre cur b lbs ss)"
  "\<not>terminal_state (sfunc s f p ss)"
    apply auto
    subgoal
      unfolding terminal_state_def step_def by simp
    subgoal 
      unfolding terminal_state_def step_def by simp
    subgoal 
      unfolding terminal_state_def step_def by simp
    subgoal
      unfolding terminal_state_def step_def
      apply (cases b)
      subgoal for p i t
        apply (cases p; simp)
         apply (cases i; simp)
          apply (cases t; simp)
           apply (split result.splits; metis result.exhaust)
      subgoal for bool
        apply (cases "get_register s bool"; simp)
        subgoal for v
          by (cases v; simp; blast)
        done
      subgoal for instr instrs
        apply (cases instr; simp del: execute_instruction.simps)
        by (split result.splits; metis result.exhaust)+
    subgoal for ph 
      apply (cases ph; simp)
      subgoal for x y z
        by (split result.splits, metis result.exhaust)
      done
    done
  done
  subgoal
    unfolding terminal_state_def step_def
    by (auto split: option.splits, metis)
  subgoal
    unfolding terminal_state_def step_def
    by (auto split: option.splits, metis)
  subgoal
    unfolding terminal_state_def step_def
    by (auto split: option.splits; metis) 
  done

lemma terminal_steps_refl[simp]: "terminal_state s \<Longrightarrow> s \<rightarrow>* s' \<Longrightarrow> s = s'"
  unfolding terminal_state_def
  by (erule converse_rtranclpE; blast)


lemma terminal_state_non_err_impl_ret:
  "terminal_state s \<Longrightarrow> \<not>is_err s \<Longrightarrow> \<exists>stat val. s = sreturn stat val None"
  unfolding is_err_def apply simp
  apply (cases s; simp)
  using not_Some_eq apply fastforce
  oops

definition wp_steps where
  "wp_steps s Q \<equiv> \<forall>s'. s \<rightarrow>* s' \<and> terminal_state s' \<longrightarrow> \<not>is_err s' \<and> Q (state s') (retval s')"

lemma step_deterministic[simp]: "s \<rightarrow> s' \<Longrightarrow> s \<rightarrow> s'' \<Longrightarrow> s' = s''"
  unfolding step_def apply (cases s) apply auto
      defer
  apply (metis (mono_tags, lifting) option.case_eq_if)
  apply (smt (verit, best) option.case_eq_if)
  apply (metis (mono_tags, lifting) option.case_eq_if)
  apply (metis (mono_tags, lifting) option.case_eq_if)
  subgoal for a b c d e f g h i j k
    apply (cases g; cases h; cases i; simp)
    apply (split result.splits; simp)
    subgoal for x y z
      apply (cases "get_register (c, d, e, f) x")
      apply auto subgoal for v by (cases v; simp)
      done
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    subgoal for i
      by (cases i; simp split: result.splits)
    done
  done


lemma obtain_step:
  "s \<rightarrow>* s' \<Longrightarrow> \<not>terminal_state s \<Longrightarrow> s \<noteq> s' \<Longrightarrow> \<exists>s''. s \<rightarrow> s'' \<and> s'' \<rightarrow>* s'"
  by (induction rule: converse_rtranclp_induct; blast)


lemma wp_steps_phi_intro:
  assumes "wp (execute_phi pre name values s) (\<lambda>s'. wp_steps (sinstructions pre cur s' (ps,i,ter) lbs ss) Q)"
  shows "wp_steps (sinstructions pre cur s ((phi name type values)#ps,i,ter) lbs ss) Q"
proof -
  obtain stat where statdef: "execute_phi pre name values s = ok stat"
    using assms
    unfolding wp_gen_def
    by (cases "execute_phi pre name values s"; simp)

  then have "(sinstructions pre cur s ((phi name type values)#ps,i,ter) lbs ss) \<rightarrow> (sinstructions pre cur stat (ps,i,ter) lbs ss)"
    unfolding step_def by simp

  moreover

  have "wp_steps (sinstructions pre cur stat (ps,i,ter) lbs ss) Q"
    using assms statdef unfolding wp_gen_def by simp

  ultimately
  
  show ?thesis
    unfolding wp_steps_def
    using obtain_step step_deterministic terminal_state_simps(4)
    by blast
qed

(*
      (case get_parameter_values p s of
        ok ps \<Rightarrow> s' = sfunc s f ps (Some (\<lambda>s v. srestore s n v pre cur ([],is,t) lbs ss))
      | _     \<Rightarrow> s' = serr
      
*)
lemma wp_steps_instr_intro:
  assumes "\<And>n t f p. i = call n t f p \<longrightarrow> (get_parameter_values p s = ok ps \<and> wp_steps (sfunc s f ps (Some (\<lambda>s v. srestore s n v pre cur ([],is,ter) lbs ss))) Q)"
  assumes "\<And>n t f p. i \<noteq> call n t f p \<longrightarrow> wp (execute_instruction i s) (\<lambda>s'. wp_steps (sinstructions pre cur s' ([],is,ter) lbs ss) Q)"
  shows "wp_steps (sinstructions pre cur s ([],i#is,ter) lbs ss) Q"
proof (cases "\<exists>n t f p. i = call n t f p")
  case True

  obtain n t f p where calldef: "i = call n t f p" using True by blast

  have params: "get_parameter_values p s = ok ps"
    using assms True calldef
    by blast
  
  moreover

  obtain s' where s'def: "s' = sfunc s f ps (Some (\<lambda>s v. srestore s n v pre cur ([],is,ter) lbs ss))"
    by blast
      
  have wpsteps: "wp_steps s' Q"
    using assms True calldef s'def
    by blast

  ultimately

  have "sinstructions pre cur s ([],i#is,ter) lbs ss \<rightarrow> s'"
    unfolding step_def
    using True calldef s'def
    by auto

  then show ?thesis
    using s'def wpsteps obtain_step step_deterministic calldef params 
    unfolding wp_steps_def
    by (metis terminal_state_simps(4))
next
  case False

  have wpassm: "wp (execute_instruction i s) (\<lambda>s'. wp_steps (sinstructions pre cur s' ([],is,ter) lbs ss) Q)"
    using assms False
    by blast

  obtain s' where s'def: "execute_instruction i s = ok s'"
    using wpassm
    unfolding wp_gen_def
    by (simp split: result.splits)

  obtain ss' where ss'def: "ss' = sinstructions pre cur s' ([],is,ter) lbs ss"
    by blast

  then have "wp_steps ss' Q"
    using wpassm s'def
    unfolding wp_gen_def
    by fastforce

  moreover
  
  have "sinstructions pre cur s ([],i#is,ter) lbs ss \<rightarrow> ss'"
    unfolding step_def
    using False ss'def s'def 
    by (cases i; auto split: result.splits)

  ultimately
  
  show ?thesis
    unfolding wp_steps_def
    using obtain_step step_deterministic terminal_state_simps(4)
    by metis
qed

  


datatype executor_state = exec_instr llvm_instruction state
  | exec_instrs "llvm_instruction list" state
  | exec_block "llvm_identifier option" llvm_instruction_block state
  | exec_blocks "llvm_identifier option" llvm_identifier llvm_labeled_blocks state
  | exec_func llvm_identifier "llvm_value list" state

datatype executor_return = state_only (state: state)
  | ctrl_flow (state: state) llvm_block_return
  | func_ret (state: state) "llvm_value option"

fun stack_size :: "state \<Rightarrow> nat" where
  "stack_size (l,g,s,h) = length s"
fun restore_stack :: "state \<Rightarrow> nat \<Rightarrow> state" where
  "restore_stack (l,g,s,h) n = (l,g,take n s,h)"
fun local_registers :: "state \<Rightarrow> (llvm_register_model * state)" where
  "local_registers (l,g,s,h) = (l, (Mapping.empty,g,s,h))"
fun restore_registers :: "state \<Rightarrow> llvm_register_model \<Rightarrow> state" where
  "restore_registers (_,g,s,h) l = (l,g,s,h)"

fun store_parameters :: "llvm_identifier list \<Rightarrow> llvm_value list \<Rightarrow> state \<Rightarrow> state result" where
  "store_parameters (i#is) (v#vs) s = store_parameters is vs (set_register i v s)"
| "store_parameters [] [] s = ok s"
| "store_parameters _ _ _ = err inconsistent_parameters"







end