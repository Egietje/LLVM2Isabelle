theory Steps
  imports Blocks
begin


context fixes program :: "llvm_program"
begin


datatype instruction_state = execi "llvm_identifier option" llvm_instruction_block state
  | flowi state llvm_block_return
  | is_erri: erri

datatype (discs_sels) function_state = branchf (state: state) "llvm_identifier option" "llvm_identifier" llvm_function
  | retf (state: state) (ret_value: "llvm_value option")
  | is_errf: errf 


inductive
  step_i :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>i" 50)
and
  step_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f" 50)
where
"(execi pre ([],[],br_label l) s) \<rightarrow>\<^sub>i (flowi s (branch_label l))"

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

| "map_of (llvm_function.blocks f) lab = Some b \<Longrightarrow>
   step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f branchf s' (Some lab) l f"
| "map_of (llvm_function.blocks f) lab = Some b \<Longrightarrow>
   step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f retf s' v"

| "map_of (llvm_function.blocks f) lab = Some b \<Longrightarrow>
   step_i\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"
| "map_of (llvm_function.blocks f) lab = None \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"


abbreviation steps_i (infix "\<rightarrow>\<^sub>i*" 50) where
  "s \<rightarrow>\<^sub>i* s' \<equiv> step_i\<^sup>*\<^sup>* s s'"
abbreviation steps_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f*" 50) where
  "s \<rightarrow>\<^sub>f* s' \<equiv> step_f\<^sup>*\<^sup>* s s'"

fun n_steps_i :: "instruction_state \<Rightarrow> nat \<Rightarrow> instruction_state \<Rightarrow> bool" where
  "n_steps_i s 0 s'  = (s = s')"
| "n_steps_i s (Suc n) s' = (\<exists>x. s \<rightarrow>\<^sub>i x \<and> n_steps_i x n s')"
fun n_steps_f :: "function_state \<Rightarrow> nat \<Rightarrow> function_state \<Rightarrow> bool" where
  "n_steps_f s 0 s'  = (s = s')"
| "n_steps_f s (Suc n) s' = (\<exists>x. s \<rightarrow>\<^sub>f x \<and> n_steps_f x n s')"

notation n_steps_i ("(_ \<rightarrow>\<^sub>i^_ _)" [51, 0, 51] 50)
notation n_steps_f ("(_ \<rightarrow>\<^sub>f^_ _)" [51, 0, 51] 50)

lemma steps_i_exists_n_steps[simp]:
  assumes "fs \<rightarrow>\<^sub>i* fs'"
  shows "\<exists>n. fs \<rightarrow>\<^sub>i^n fs'"
  using assms n_steps_i.simps
  by (induction rule: converse_rtranclp_induct; blast)

lemma steps_f_exists_n_steps[simp]:
  assumes "fs \<rightarrow>\<^sub>f* fs'"
  shows "\<exists>n. fs \<rightarrow>\<^sub>f^n fs'"
  using assms n_steps_f.simps
  by (induction rule: converse_rtranclp_induct; blast)


definition terminal_state_i where
  "terminal_state_i s \<equiv> \<nexists>s'. s \<rightarrow>\<^sub>i s'"
definition terminal_state_f where
  "terminal_state_f s \<equiv> \<nexists>s'. s \<rightarrow>\<^sub>f s'"

notation terminal_state_i ("_ \<nexists>\<rightarrow>\<^sub>i" 50)
notation terminal_state_f ("_ \<nexists>\<rightarrow>\<^sub>f" 50)


definition "first_label f \<equiv> (case llvm_function.blocks f of ((l,b)#fs) \<Rightarrow> Some l | _ \<Rightarrow> None)"


lemma term_state_i_simps[simp]:
  "\<not> ((execi pre b s) \<nexists>\<rightarrow>\<^sub>i)"
  "(flowi s br) \<nexists>\<rightarrow>\<^sub>i"
  "erri \<nexists>\<rightarrow>\<^sub>i"
    apply clarsimp
  apply (cases b; cases s)
  subgoal for phis instrs ter l g s h
    unfolding terminal_state_i_def
    apply (cases phis; cases instrs; cases ter)
    subgoal for x apply (cases x) using step_i_step_f.intros apply blast
      subgoal for r apply (cases r) using result.exhaust step_i_step_f.intros by meson
      done
    using step_i_step_f.intros result.exhaust by meson+
  unfolding terminal_state_i_def using step_i.cases apply blast
  unfolding terminal_state_i_def using step_i.cases by blast

lemma step_i_reaches_term_state:
  "\<exists>s'. execi pre b s \<rightarrow>\<^sub>i* s' \<and> (s' \<nexists>\<rightarrow>\<^sub>i)"
  apply (cases b)
  subgoal for phis instrs ter
  proof (induction phis arbitrary: pre b s)
    case Nil
    then show ?case
    proof (induction instrs arbitrary: pre b s)
      case Nil
      then show ?case 
        by (smt (verit) fst_conv instruction_state.sel(2) list.discI rtranclp.rtrancl_into_rtrancl
           rtranclp.rtrancl_refl snd_conv step_i.cases term_state_i_simps(2,3) terminal_state_i_def)
    next
      case (Cons a instrs)

      show ?case
      proof (cases "execi pre ([],a#instrs,ter) s \<rightarrow>\<^sub>i erri")
        case True
        then show ?thesis 
          using Cons.prems term_state_i_simps(3) by blast
      next
        case False

        have "\<exists>s'. execi pre ([],a#instrs,ter) s \<rightarrow>\<^sub>i execi pre ([],instrs,ter) s' \<or> execi pre ([],a#instrs,ter) s \<rightarrow>\<^sub>i erri"
          by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject step_i.cases
              term_state_i_simps(1) terminal_state_i_def)

        then obtain s' where "execi pre ([],a#instrs,ter) s \<rightarrow>\<^sub>i execi pre ([],instrs,ter) s'"
          using False by blast

        then show ?thesis using Cons False Nil
          by (metis rtranclp_idemp rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
      qed
    qed
  next
    case (Cons a phis)
    obtain s' where nextstate: "execi pre b s \<rightarrow>\<^sub>i s'"
      using term_state_i_simps(1) terminal_state_i_def by blast
    then show ?case
    proof (cases "execi pre (a#phis,instrs,ter) s \<rightarrow>\<^sub>i erri")
      case True
      then show ?thesis
          using Cons.prems term_state_i_simps(3) by blast
    next
      case False
      have "\<exists>s'. execi pre (a#phis,instrs,ter) s \<rightarrow>\<^sub>i execi pre (phis,instrs,ter) s' \<or> execi pre (a#phis,instrs,ter) s \<rightarrow>\<^sub>i erri"
          by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject step_i.cases
              term_state_i_simps(1) terminal_state_i_def)
      then obtain s' where "execi pre (a#phis,instrs,ter) s \<rightarrow>\<^sub>i execi pre (phis,instrs,ter) s'"
          using False by blast

      then show ?thesis using Cons
        by (metis rtranclp_idemp rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
    qed

  qed
  done

lemma term_state_f_simps[simp]:
  "errf \<nexists>\<rightarrow>\<^sub>f"
  "retf s v \<nexists>\<rightarrow>\<^sub>f"
  "\<not> ((branchf s prev lab f) \<nexists>\<rightarrow>\<^sub>f)"
  unfolding terminal_state_f_def
    apply simp
  using step_f.cases apply blast
  using step_f.cases apply blast
  apply (cases "map_of (llvm_function.blocks f) lab")
  using step_i_step_f.intros(14) apply blast
  subgoal premises prems for b
  proof (cases "execi prev b s \<rightarrow>\<^sub>i*  erri")
    case True
    then show ?thesis
      using step_i_step_f.intros(13) prems
      by blast
  next
    case False

    then obtain ts where "execi prev b s \<rightarrow>\<^sub>i* ts \<and> ts \<nexists>\<rightarrow>\<^sub>i"
      using step_i_reaches_term_state
      by blast
    
    then obtain s' br where "execi prev b s \<rightarrow>\<^sub>i* flowi s' br"
      by (metis False instruction_state.collapse(3) instruction_state.exhaust_disc is_execi_def is_flowi_def
          term_state_i_simps(1))
      
    then show ?thesis
      using prems step_i_step_f.intros
      by (cases br; meson)
  qed
  done



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
            subgoal for r by (cases r; auto simp: r_into_rtranclp step_i_step_f.intros)
              apply (auto simp: r_into_rtranclp step_i_step_f.intros)
            apply (auto split: llvm_value.splits)
             apply (rule r_into_rtranclp)
            using step_i_step_f.intros apply presburger 
            apply (rule r_into_rtranclp)
            using step_i_step_f.intros by presburger

        next
          case (Cons i ins)

          obtain is' where nextstate: "execute_instruction i s = ok is'"
            using Cons
            by auto

          then have "(execi pre ([],ins,ter) is')  \<rightarrow>\<^sub>i* (flowi s' br)"
            using Cons
            by auto

          then show ?case 
            using nextstate converse_rtranclp_into_rtranclp step_i_step_f.intros
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
          using nextstate converse_rtranclp_into_rtranclp step_i_step_f.intros
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

lemma step_f_deterministic[simp]:
  assumes "s \<rightarrow>\<^sub>f s1"
  assumes "s \<rightarrow>\<^sub>f s2"
  shows "s1 = s2"
proof (cases s)
  case (branchf s prev lab f)
  then show ?thesis sorry
next
  case (retf x21 x22)
  then show ?thesis
    using assms
    by (metis term_state_f_simps(2) terminal_state_f_def)
next
  case errf
  then show ?thesis
    using assms
    by (metis term_state_f_simps(1) terminal_state_f_def)
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




lemma terminal_state_simps[simp]: 
  "terminal_state berr"
  "terminal_state (bret s v)"
  "\<not>terminal_state (bbranch s prev lab)"
  unfolding terminal_state_def
    apply auto apply (cases "map_of (llvm_function.blocks f) lab"; simp)
  subgoal for b
    apply (cases b)
    subgoal premises prems for phis instrs ter
      using prems(2)
    proof (induction phis arbitrary: b s)
      case phinil: Nil
      then show ?case
      proof (induction instrs arbitrary: b s)
        case insnil: Nil
        then show ?case
        proof(cases ter)
          case (ret x1)
          then show ?thesis
          proof (cases x1)
            case None
            then show ?thesis by (metis (mono_tags, lifting) ret instruction_state.simps(10) llvm_block_return.simps(5) insnil r_into_rtranclp
                step_i.intros(4) term_state_i_simps(2))
          next
            case (Some v)
            then obtain s' where "execi prev ([],[],ter) s \<rightarrow>\<^sub>i s'"
              using term_state_i_simps unfolding terminal_state_i_def by meson
            then have "s' = erri \<or> (\<exists>s'' v'. s' = flowi s'' v')"
              by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject
                  step_i.cases)
            then have "\<exists>ss' ss. step_i\<^sup>*\<^sup>* s' ss \<and> terminal_state_i ss \<and>
            (case ss of flowi stat (return_value v) \<Rightarrow> ss' = bret stat v
              | flowi stat (branch_label l) \<Rightarrow> ss' = bbranch stat (Some lab) l | erri \<Rightarrow> ss' = berr)"
                using prems phinil insnil ret Some
                by (metis (mono_tags, lifting) instruction_state.simps(10,11) llvm_block_return.exhaust llvm_block_return.simps(5,6)
                    rtranclp.simps term_state_i_simps(2,3))

            then show ?thesis using prems phinil insnil ret Some
              by (metis (no_types, lifting) \<open>execi prev ([], [], ter) s \<rightarrow>\<^sub>i s'\<close> converse_rtranclp_into_rtranclp)
          qed
        next
          case (br_i1 x21 x22 x23)
            then obtain s' where "execi prev ([],[],ter) s \<rightarrow>\<^sub>i s'"
              using term_state_i_simps unfolding terminal_state_i_def by meson
            then have "s' = erri \<or> (\<exists>s'' v'. s' = flowi s'' v')"
              by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject
                  step_i.cases)
            then have "\<exists>ss' ss. step_i\<^sup>*\<^sup>* s' ss \<and> terminal_state_i ss \<and>
            (case ss of flowi stat (return_value v) \<Rightarrow> ss' = bret stat v
              | flowi stat (branch_label l) \<Rightarrow> ss' = bbranch stat (Some lab) l | erri \<Rightarrow> ss' = berr)"
                using prems phinil insnil br_i1
                by (metis (mono_tags, lifting) instruction_state.simps(10,11) llvm_block_return.exhaust llvm_block_return.simps(5,6)
                    rtranclp.simps term_state_i_simps(2,3))
          then show ?thesis using prems phinil insnil
              by (metis (no_types, lifting) \<open>execi prev ([], [], ter) s \<rightarrow>\<^sub>i s'\<close> converse_rtranclp_into_rtranclp)
        next
          case (br_label x3)
            then obtain s' where "execi prev ([],[],ter) s \<rightarrow>\<^sub>i s'"
              using term_state_i_simps unfolding terminal_state_i_def by meson
            then have "s' = erri \<or> (\<exists>s'' v'. s' = flowi s'' v')"
              by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject
                  step_i.cases)
            then have "\<exists>ss' ss. step_i\<^sup>*\<^sup>* s' ss \<and> terminal_state_i ss \<and>
            (case ss of flowi stat (return_value v) \<Rightarrow> ss' = bret stat v
              | flowi stat (branch_label l) \<Rightarrow> ss' = bbranch stat (Some lab) l | erri \<Rightarrow> ss' = berr)"
                using prems phinil insnil br_label
                by (metis (mono_tags, lifting) instruction_state.simps(10,11) llvm_block_return.exhaust llvm_block_return.simps(5,6)
                    rtranclp.simps term_state_i_simps(2,3))
          then show ?thesis using prems phinil insnil
              by (metis (no_types, lifting) \<open>execi prev ([], [], ter) s \<rightarrow>\<^sub>i s'\<close> converse_rtranclp_into_rtranclp)
        qed
      next
        case (Cons i ins)

        then obtain s' where "execi prev ([],i#ins,ter) s \<rightarrow>\<^sub>i s'"
          using term_state_i_simps unfolding terminal_state_i_def by meson

        then have "s'= erri \<or> (\<exists>st. s' = execi prev ([],ins,ter) st)"
          by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject
            step_i.cases)
      then have "\<exists>ss' ss. step_i\<^sup>*\<^sup>* s' ss \<and> terminal_state_i ss \<and>
       (case ss of flowi stat (return_value v) \<Rightarrow> ss' = bret stat v
        | flowi stat (branch_label l) \<Rightarrow> ss' = bbranch stat (Some lab) l | erri \<Rightarrow> ss' = berr)"
        using prems Cons Nil by fastforce

        then show ?case using prems Cons.IH
          by (metis (no_types, lifting) Cons.prems \<open>execi prev ([], i # ins, ter) s \<rightarrow>\<^sub>i s'\<close> converse_rtranclp_into_rtranclp)
      qed
        
    next
      case (Cons p ps b s)
      
      then obtain s' where "(execi prev (p#ps,instrs,ter) s) \<rightarrow>\<^sub>i s'"
        using term_state_i_simps unfolding terminal_state_i_def by meson

      then have "s' = erri \<or> (\<exists>st. s' = execi prev (ps,instrs,ter) st)"
        by (smt (verit) instruction_state.inject(1) list.discI list.inject prod.inject
            step_i.cases)
        

      then have "\<exists>ss' ss. step_i\<^sup>*\<^sup>* s' ss \<and> terminal_state_i ss \<and>
       (case ss of flowi stat (return_value v) \<Rightarrow> ss' = bret stat v
        | flowi stat (branch_label l) \<Rightarrow> ss' = bbranch stat (Some lab) l | erri \<Rightarrow> ss' = berr)"
        using prems Cons by fastforce

      then show ?case using prems Cons.IH
        by (metis (no_types, lifting) Cons.prems \<open>step_i (execi prev (p # ps, instrs, ter) s) s'\<close>
            converse_rtranclp_into_rtranclp)
      qed
          done done 

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
  apply auto
  using terminal_non_err terminal_state_def apply blast
  apply (cases fs)
    apply simp_all
  subgoal for fs' fs'' s prev l
    apply (cases "map_of (llvm_function.blocks f) l")
     apply simp_all
      apply (elim exE conjE)
    subgoal premises prems for b ss' ss''
    proof -
      obtain n where ndef: "execi prev b s \<rightarrow>\<^sub>i^n ss'"
        using prems
        by fastforce

      moreover

      obtain m where mdef: "execi prev b s \<rightarrow>\<^sub>i^m ss''"
        using prems
        by fastforce

      ultimately

      show ?thesis
      proof (induction n arbitrary: prev b s m)
        case 0
        then show ?case using prems by auto
      next
        case nsuc: (Suc n')
        then show ?case
        proof (induction m arbitrary: prev b s)
          case 0
          then show ?case using prems by auto
        next
          case (Suc m')
          
          obtain s' where nextstate: "execi prev b s \<rightarrow>\<^sub>i s'"
            using term_state_i_simps(1) terminal_state_i_def by blast

          have nextmsteps: "s' \<rightarrow>\<^sub>i^m' ss''" using nextstate Suc
            by (metis n_steps_i.simps(2) step_i_deterministic)

          moreover

          have nextnsteps: "s' \<rightarrow>\<^sub>i^n' ss'" using nextstate Suc
            by (metis n_steps_i.simps(2) step_i_deterministic)

          ultimately
          
          show ?case
          proof(cases s')
            case (execi x11 x12 x13)
            then show ?thesis using nextmsteps nextnsteps nextstate Suc nsuc by blast  
          next
            case (flowi x21 x22)

            have "m' = 0" using nextmsteps flowi
              by (meson n_steps_i.elims(1) term_state_i_simps(2) terminal_state_i_def)

            moreover

            have "n' = 0" using nextnsteps flowi 
              by (meson n_steps_i.elims(1) term_state_i_simps(2) terminal_state_i_def)

            ultimately

            have "ss' = ss''"using nextmsteps nextnsteps nextstate flowi prems Suc nsuc by simp
            
            then show ?thesis
              using prems(6) prems(7) prems(8)
              by (auto split: instruction_state.splits llvm_block_return.splits)
          next
            case erri
            then show ?thesis
              by (metis (mono_tags, lifting) instruction_state.simps(11) n_steps_i.elims(2) nextmsteps nextnsteps prems(6,8) term_state_i_simps(3) terminal_state_i_def)
          qed
        qed
      qed
    qed
    done
  done


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
  assumes "wp_instrs
    (execi p b s)
    (\<lambda>s'.
      (case s' of
        (flowi s'' br) \<Rightarrow>
          (case br of
            branch_label l' \<Rightarrow> Q (bbranch s'' (Some l) l')
          | return_value v  \<Rightarrow> Q (bret s'' v)
          )
      )
    )"
  shows "wp_step (bbranch s p l) Q"
    unfolding wp_step_def
    using assms(1)
    apply clarsimp
    subgoal premises prems for fs' s'
    proof (cases s')
      case (execi x11 x12 x13)
      then show ?thesis using prems by simp
    next
      case (flowi x21 x22)
      then show ?thesis
        using prems apply (auto split: llvm_block_return.splits) using assms(2) unfolding wp_instrs_def by auto  
        
    next
      case erri
      then show ?thesis using prems assms
        using instruction_state.disc(9) wp_instrs_def by blast
    qed
    done

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
    \<and> (\<forall>p l. map_of annotations (p,l) \<noteq> None \<longrightarrow>
        (\<forall>s. annotation_holds (bbranch s p l) \<longrightarrow> floyd_cond s p l))"

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
  unfolding floyd_vc_def floyd_cond_def 
  apply (auto split: flow_state.splits)
  subgoal for fs fs' a
    unfolding annotation_holds_def annotated_step_def
  apply (cases fs)
    apply force apply force
    by (metis (no_types, lifting) Steps.floyd_cond_def Steps.floyd_vc_def annotated_step_def
        annotation_holds_def assms flow_state.case_eq_if flow_state.disc(6) flow_state.sel(4,5) option.simps(4)
        wp_annotated_step_def)
  done


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