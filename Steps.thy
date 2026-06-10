theory Steps
  imports Blocks
begin


context fixes program :: "llvm_program"
begin


datatype instruction_state = execi "llvm_identifier option" llvm_instruction_block state
  | flowi state llvm_block_return
  | is_erri: erri

datatype (discs_sels) function_state = branchf (state: state) "llvm_identifier option" llvm_identifier llvm_identifier
  | retf (state: state) (ret_value: "llvm_value option") llvm_identifier
  | is_errf: errf


definition "first_label f \<equiv> (case llvm_function.blocks f of ((l,b)#fs) \<Rightarrow> Some l | _ \<Rightarrow> None)"







inductive
  step_i :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>i" 50)
and
  step_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f" 50)
where
(* Control flow *)
"(execi pre ([],[],br_label l) s) \<rightarrow>\<^sub>i (flowi s (branch_label l))"

| "dereference s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. dereference s b = ok (vi1 b') \<Longrightarrow>
    (execi pre ([],[],br_i1 b l1 l2) s) \<rightarrow>\<^sub>i erri"

| "(execi pre ([],[],ret None) s) \<rightarrow>\<^sub>i (flowi s (return_value None))"

| "dereference s v = ok v' \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i (flowi s (return_value (Some v')))"
| "dereference s v = err _ \<Longrightarrow>
    (execi pre ([],[],ret (Some (t, v))) s) \<rightarrow>\<^sub>i erri"

(* Function calls *)
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> step_f\<^sup>*\<^sup>* (branchf (push_frame s) None b f) (retf s' v' f)
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i (execi pre ([],is,t) (pop_frame s s'))"
| "map_of (funcs program) f = None
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> step_f\<^sup>*\<^sup>* (branchf (push_frame s) None b f) errf
  \<Longrightarrow> (execi pre ([],(call n ty f p)#is,t) s) \<rightarrow>\<^sub>i erri"

(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> (execi pre ([],i#is,t) s) \<rightarrow>\<^sub>i erri"

(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    (execi pre (p#ps,is,t) s) \<rightarrow>\<^sub>i erri"

(* Blocks *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>                                                          
    branchf s prev lab f \<rightarrow>\<^sub>f branchf s' (Some lab) l f"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
    branchf s prev lab f \<rightarrow>\<^sub>f retf s' v f"

(* Block errors *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
    branchf s prev lab f \<rightarrow>\<^sub>f errf"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"
| "map_of (funcs program) f = None \<Longrightarrow>
     branchf s prev lab f \<rightarrow>\<^sub>f errf"


inductive trans_closure_n where
  "trans_closure_n R s n s"
| "trans_closure_n R s' m s'' \<Longrightarrow> R s n s' \<Longrightarrow> trans_closure_n R s (m+n) s''"

lemma trans_closure_n_mono [mono]:
  assumes "(\<And>s n s'. A s n s' \<longrightarrow> B s n s')"
  shows "trans_closure_n A s n s' \<longrightarrow> trans_closure_n B s n s'" 
  apply (rule impI)
  using assms apply -
  by (induction rule: trans_closure_n.induct; simp add: trans_closure_n.intros)


inductive
  step_i_n :: "instruction_state \<Rightarrow> nat \<Rightarrow> instruction_state \<Rightarrow> bool"
and
  step_f_n :: "function_state \<Rightarrow> nat \<Rightarrow> function_state \<Rightarrow> bool"
where
(* Control flow *)
"step_i_n (execi pre ([],[],br_label l) s) n (flowi s (branch_label l))"

| "dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_n (execi pre ([],[],br_i1 b l1 l2) s) n (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_n (execi pre ([],[],br_i1 b l1 l2) s) n erri"

| "step_i_n (execi pre ([],[],ret None) s) n (flowi s (return_value None))"

| "dereference s v = ok v' \<Longrightarrow>
    step_i_n (execi pre ([],[],ret (Some (t, v))) s) n (flowi s (return_value (Some v')))"
| "dereference s v = err _ \<Longrightarrow>
    step_i_n (execi pre ([],[],ret (Some (t, v))) s) n erri"


(* Function calls *)
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> trans_closure_n (step_f_n) (branchf (push_frame s) None b f) n (retf s' v' f)
  \<Longrightarrow> step_i_n (execi pre ([],(call na ty f p)#is,t) s) (n+1) (execi pre ([],is,t) (pop_frame s s'))"

| "map_of (funcs program) f = None
  \<Longrightarrow> step_i_n (execi pre ([],(call na ty f p)#is,t) s) n erri"
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> step_i_n (execi pre ([],(call na ty f p)#is,t) s) n erri"

| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> trans_closure_n (step_f_n) (branchf (push_frame s) None b f) n errf
  \<Longrightarrow> step_i_n (execi pre ([],(call na ty f p)#is,t) s) (n+1) erri"


(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_n (execi pre ([],i#is,t) s) n (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_n (execi pre ([],i#is,t) s) n erri"


(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    step_i_n (execi pre (p#ps,is,t) s) n (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    step_i_n (execi pre (p#ps,is,t) s) n erri"


(* Blocks *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    trans_closure_n (step_i_n) (execi prev b s) n (flowi s' (branch_label l)) \<Longrightarrow>                                                          
    step_f_n (branchf s prev lab f) n (branchf s' (Some lab) l f)"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    trans_closure_n (step_i_n) (execi prev b s) n (flowi s' (return_value v)) \<Longrightarrow>
    step_f_n (branchf s prev lab f) n (retf s' v f)"


(* Block errors *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    trans_closure_n (step_i_n) (execi prev b s) n erri \<Longrightarrow>
    step_f_n (branchf s prev lab f) n errf"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     step_f_n (branchf s prev lab f) n errf"
| "map_of (funcs program) f = None \<Longrightarrow>
     step_f_n (branchf s prev lab f) n errf"



lemma rtranclp_impl_exists_trans_closure_n:
  assumes "R\<^sup>*\<^sup>* s s'"
  assumes "(\<And>s s'. R s s' \<Longrightarrow> \<exists>n. R' s n s')"
  shows "\<exists>n. trans_closure_n R' s n s'"
  using assms trans_closure_n.intros
  by (induction rule: converse_rtranclp_induct, force, fastforce)

lemma trans_closure_n_impl_rtranclp:
  assumes "trans_closure_n R' s n s'"
  assumes "(\<And>s s' n. R' s n s' \<Longrightarrow> R s s')"
  shows "R\<^sup>*\<^sup>* s s'"
  using assms trans_closure_n.intros converse_rtranclp_into_rtranclp
  by (induction rule: trans_closure_n.induct, blast, smt)


lemma n_step_impl_step:
  "step_i_n si n si' \<Longrightarrow> step_i si si'"
  "step_f_n sf n sf' \<Longrightarrow> step_f sf sf'"
   apply (induction rule: step_i_n_step_f_n.inducts)
  using step_i_step_f.intros trans_closure_n_impl_rtranclp
  by (metis (no_types, lifting))+

lemma step_impl_exists_n_step:
  "step_i si si' \<Longrightarrow> \<exists>n. step_i_n si n si'"
  "step_f sf sf' \<Longrightarrow> \<exists>n. step_f_n sf n sf'"
  apply (induction rule: step_i_step_f.inducts)
  apply (simp add: step_i_n_step_f_n.intros)+
  subgoal premises prems for f fu b s s' v' pre n ty p ins t
  proof -
    obtain n where "trans_closure_n (step_f_n) (branchf (push_frame s) None b f) n (retf s' v' f)"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (simp add: trans_closure_n.intros(1))
      by (meson trans_closure_n.intros(2))

    then show ?thesis
      using prems step_i_n_step_f_n.intros(7)
      by blast
  qed
  apply (simp add: step_i_n_step_f_n.intros)+
  subgoal premises prems for f fu b s pre n ty p ins t
  proof -
    obtain n where "trans_closure_n (step_f_n) (branchf (push_frame s) None b f) n errf"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (simp add: trans_closure_n.intros(1))
      by (meson trans_closure_n.intros(2))

    then show ?thesis
      using prems step_i_n_step_f_n.intros(10)
      by blast
  qed
  apply (simp add: step_i_n_step_f_n.intros)+
  subgoal premises prems for f fu lab b prev s s' l
  proof -
    obtain n where "trans_closure_n (step_i_n) (execi prev b s) n (flowi s' (branch_label l))"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (simp add: trans_closure_n.intros(1))
      by (meson trans_closure_n.intros(2))

    then show ?thesis
      using prems step_i_n_step_f_n.intros(15)
      by blast
  qed
  subgoal premises prems for f fu lab b prev s s' v
  proof -
    obtain n where "trans_closure_n (step_i_n) (execi prev b s) n (flowi s' (return_value v))"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (simp add: trans_closure_n.intros(1))
      by (meson trans_closure_n.intros(2))

    then show ?thesis
      using prems step_i_n_step_f_n.intros(16)
      by blast
  qed
  subgoal premises prems for f fu lab b prev s
  proof -
    obtain n where "trans_closure_n (step_i_n) (execi prev b s) n erri"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (simp add: trans_closure_n.intros(1))
      by (meson trans_closure_n.intros(2))

    then show ?thesis
      using prems step_i_n_step_f_n.intros(17)
      by blast
  qed
  by (simp add: step_i_n_step_f_n.intros)+

lemma steps_impl_exists_n_steps:
  "step_i\<^sup>*\<^sup>* si si' \<Longrightarrow> \<exists>n. trans_closure_n (step_i_n) si n si'"
  "step_f\<^sup>*\<^sup>* sf sf' \<Longrightarrow> \<exists>n. trans_closure_n (step_f_n) sf n sf'"
  using rtranclp_impl_exists_trans_closure_n step_impl_exists_n_step
  by metis+

lemma n_steps_impl_steps:
  "trans_closure_n (step_i_n) si n si' \<Longrightarrow> step_i\<^sup>*\<^sup>* si si'"
  "trans_closure_n (step_f_n) sf n sf' \<Longrightarrow> step_f\<^sup>*\<^sup>* sf sf'"
  using n_step_impl_step trans_closure_n_impl_rtranclp
  by metis+


abbreviation steps_i (infix "\<rightarrow>\<^sub>i*" 50) where
  "s \<rightarrow>\<^sub>i* s' \<equiv> step_i\<^sup>*\<^sup>* s s'"
abbreviation steps_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f*" 50) where
  "s \<rightarrow>\<^sub>f* s' \<equiv> step_f\<^sup>*\<^sup>* s s'"




definition terminal_i where
  "terminal_i s \<equiv> (case s of flowi _ _ \<Rightarrow> True | erri \<Rightarrow> True | _ \<Rightarrow> False)"
definition terminal_f where
  "terminal_f s \<equiv> (case s of retf _ _ _ \<Rightarrow> True | errf \<Rightarrow> True | _ \<Rightarrow> False)"

notation terminal_i ("_ \<nexists>\<rightarrow>\<^sub>i" 50)
notation terminal_f ("_ \<nexists>\<rightarrow>\<^sub>f" 50)

abbreviation terminates_to_i where
  "terminates_to_i s s' \<equiv> s \<rightarrow>\<^sub>i* s' \<and> (s' \<nexists>\<rightarrow>\<^sub>i)"
abbreviation terminates_to_f where
  "terminates_to_f s s' \<equiv> s \<rightarrow>\<^sub>f* s' \<and> (s' \<nexists>\<rightarrow>\<^sub>f)"

lemma terminal_state_simps[simp]:
  "flowi s br \<nexists>\<rightarrow>\<^sub>i"
  "erri \<nexists>\<rightarrow>\<^sub>i"
  "\<not>(execi pre b s \<nexists>\<rightarrow>\<^sub>i)"
  "errf \<nexists>\<rightarrow>\<^sub>f"
  "retf s v f \<nexists>\<rightarrow>\<^sub>f"
  "\<not>(branchf s p l f \<nexists>\<rightarrow>\<^sub>f)"
  unfolding terminal_i_def terminal_f_def
  by auto


lemma terminates_impl_exists_next_state:
  "terminates_to_i si si' \<Longrightarrow> \<not>terminal_i si \<Longrightarrow> \<exists>si'. si \<rightarrow>\<^sub>i si'"
  "terminates_to_f sf sf' \<Longrightarrow> \<not>terminal_f sf \<Longrightarrow> \<exists>sf'. sf \<rightarrow>\<^sub>f sf'"
  by (elim conjE, rotate_tac, induction rule: converse_rtranclp_induct; blast)+

lemma terminal_impl_no_next_state[simp]:
  "terminal_i si \<Longrightarrow> \<nexists>si'. si \<rightarrow>\<^sub>i si'"
  "terminal_f sf \<Longrightarrow> \<nexists>sf'. sf \<rightarrow>\<^sub>f sf'"
  apply (cases si, simp)
  using step_i.cases apply fast
  using step_i.cases apply fast
  apply (cases sf, simp)
  using step_f.cases apply fast
  using step_f.cases apply fast
  done

lemma terminal_steps_refl[simp]:
  "si \<nexists>\<rightarrow>\<^sub>i \<Longrightarrow> si \<rightarrow>\<^sub>i* si' \<longleftrightarrow> si'=si"
  "sf \<nexists>\<rightarrow>\<^sub>f \<Longrightarrow> sf \<rightarrow>\<^sub>f* sf' \<longleftrightarrow> sf'=sf"
  apply (auto elim: converse_rtranclpE; metis converse_rtranclpE terminal_impl_no_next_state(1))
  apply (auto elim: converse_rtranclpE; metis converse_rtranclpE terminal_impl_no_next_state(2))
  done

lemma step_deterministic[simp]:
  "si \<rightarrow>\<^sub>i si' \<Longrightarrow> \<forall>s'. si \<rightarrow>\<^sub>i s' \<longrightarrow> s' = si'"
  "sf \<rightarrow>\<^sub>f sf' \<Longrightarrow> \<forall>s'. sf \<rightarrow>\<^sub>f s' \<longrightarrow> s' = sf'"
   apply (induction arbitrary: rule: step_i_step_f.inducts)
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu b s s' v' pre na ty p ins t
  proof -
    have "branchf (push_frame s) None b f \<rightarrow>\<^sub>f* retf s' v' f"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    then have "\<And>s'' v'' f'. branchf (push_frame s) None b f \<rightarrow>\<^sub>f* retf s'' v'' f' \<longrightarrow> (s'' = s' \<and> v'' = v' \<and> f' = f)"
      using prems(3) 
      apply (induction rule: converse_rtranclp_induct)
      apply (metis function_state.inject(2) terminal_impl_no_next_state(2) converse_rtranclpE terminal_state_simps(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct(1) step_f.cases)

    moreover

    have "\<not>(branchf (push_frame s) None b f) \<rightarrow>\<^sub>f* errf"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(2) terminal_state_simps(5) converse_rtranclpE function_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct step_f.cases)

    ultimately

    show ?thesis
      using prems step_i.simps
      by auto
  qed
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu b s pre na ty p ins t
  proof -
    have "branchf (push_frame s) None b f \<rightarrow>\<^sub>f* errf"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    moreover

    have "\<And>s' v' f'. \<not>(branchf (push_frame s) None b f) \<rightarrow>\<^sub>f* retf s' v' f'"
      using prems(3)
      apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(2) terminal_state_simps(4) converse_rtranclpE function_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE function_state.distinct step_f.cases)

    ultimately

    show ?thesis
      using step_i.simps prems
      by auto
  qed
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  using step_i.simps apply fastforce
  subgoal premises prems for f fu lab b prev s s' l
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* flowi s' (branch_label l)"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    then have "\<And>s'' br. execi prev b s \<rightarrow>\<^sub>i* flowi s'' br \<longrightarrow> (s'' = s' \<and> br = branch_label l)"
      using prems(3) 
      apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) instruction_state.inject(2) converse_rtranclpE terminal_state_simps(1))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct(1) step_i.cases)

    moreover

    have "\<not>execi prev b s \<rightarrow>\<^sub>i* erri"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(1) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  subgoal premises prems for f fu lab b prev s s' v
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* flowi s' (return_value v)"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    then have "\<And>s'' br. execi prev b s \<rightarrow>\<^sub>i* flowi s'' br \<longrightarrow> (s'' = s' \<and> br = return_value v)"
      using prems(3) 
      apply (induction rule: converse_rtranclp_induct)
      apply (metis instruction_state.inject(2) terminal_impl_no_next_state(1) converse_rtranclpE Steps.terminal_state_simps(1))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct(1) step_i.cases)

    moreover

    have "\<not>execi prev b s \<rightarrow>\<^sub>i* erri"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(1) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  subgoal premises prems for f fu lab b prev s
  proof -
    have "execi prev b s \<rightarrow>\<^sub>i* erri"
      by (metis (no_types, lifting) mono_rtranclp prems(3))

    moreover

    have "\<And>s' br. \<not>execi prev b s \<rightarrow>\<^sub>i* flowi s' br"
      using prems(3) apply (induction rule: converse_rtranclp_induct)
      apply (metis terminal_impl_no_next_state(1) terminal_state_simps(2) converse_rtranclpE instruction_state.distinct(5))
      by (smt (verit, best) converse_rtranclpE instruction_state.distinct step_i.cases)

    ultimately

    show ?thesis
      using prems step_f.simps
      by fastforce
  qed
  using step_f.cases apply fastforce
  using step_f.cases by fastforce



















definition "wp_steps_i s Q \<equiv> \<forall>s'. terminates_to_i s s' \<longrightarrow> \<not>is_erri s' \<and> Q s'"

definition "wp_steps_f_post s p s' Q \<equiv> (\<not>is_errf s') \<and> (Q (state s) p (state s') (ret_value s'))"
definition "wp_steps_f s p Q \<equiv> \<forall>s'. terminates_to_f s s' \<longrightarrow> wp_steps_f_post s p s' Q"








section "Instruction Step Intro Rules"

named_theorems wp_instrs_intro
(*
lemma instrs_phi_intro[wp_instrs_intro]:
  assumes "wp (execute_phi pre p s) (\<lambda>s'. wp_instrs (execi pre (ps, is, t) s') Q)"
  shows "wp_instrs (execi pre (p#ps, is, t) s) Q"
proof -
  obtain s' where nextstate: "execute_phi pre p s = ok s'"
    using assms wp_impl_ok
    by blast

  show ?thesis
    using nextstate assms converse_rtranclpE fst_conv instruction_state.sel list.discI Steps.step_deterministic
      list.inject result.distinct result.simps snd_conv step_i.cases terminal_state_simps local.step_i_step_f.intros
      result.inject(1)
    unfolding wp_gen_def wp_instrs_def terminal_i_def
    by (smt (verit, del_insts))
qed

lemma instrs_instr_intro[wp_instrs_intro]:
  assumes "\<not>is_call i"
  assumes "wp (execute_instruction i s) (\<lambda>s'. wp_instrs (execi pre ([], is, t) s') Q)"
  shows "wp_instrs (execi pre ([], i#is, t) s) Q"
proof -
  obtain s' where nextstate: "execute_instruction i s = ok s'"
    using assms wp_impl_ok
    by blast

  show ?thesis
    using nextstate assms converse_rtranclpE fst_conv instruction_state.sel list.discI Steps.step_deterministic
      list.inject result.distinct result.simps snd_conv step_i.cases terminal_state_simps local.step_i_step_f.intros
      result.inject(1)
    unfolding wp_gen_def wp_instrs_def terminal_i_def
    by (smt (verit, del_insts))
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
        using prems step_i_step_f.intros register_\<alpha>_eq_dereference
        by auto

        then show ?thesis using step_deterministic
          by (metis terminal_impl_no_next_state(1) converse_rtranclpE is_erri_def local.instruction_state.distinct(6)
              terminal_state_simps(1) prems(2,3,4))
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
        using prems step_i_step_f.intros
        by auto

        then show ?thesis using step_deterministic
          by (metis terminal_impl_no_next_state(1) converse_rtranclpE is_erri_def local.instruction_state.distinct(6)
              terminal_state_simps(1) prems)
    qed
  done


lemma block_br_label_wp_intro[wp_instrs_intro]:
  assumes "Q (flowi s (branch_label l))"
  shows "wp_instrs (execi pre ([], [], br_label l) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  by (metis terminal_impl_no_next_state(1) converse_rtranclpE instruction_state.disc(8) local.step_deterministic(1)
      local.step_i_step_f.intros(1) terminal_state_simps(1))

lemma block_br_i1_wp_intro[wp_instrs_intro]:
  assumes "register_\<alpha> s value = Some (vi1 b)"
  assumes "b \<Longrightarrow> Q (flowi s (branch_label l1))"
  assumes "\<not>b \<Longrightarrow> Q (flowi s (branch_label l2))"
  shows "wp_instrs (execi pre ([], [], br_i1 value l1 l2) s) Q"
  unfolding wp_instrs_def
  using assms
  apply (intro impI allI) apply (elim conjE)
  by (smt (verit) terminal_impl_no_next_state converse_rtranclpE instruction_state.collapse(3)
      instruction_state.distinct(1) local.instruction_state.distinct(6) local.step_deterministic(1) local.step_i.cases
      local.step_i_step_f.intros(2) register_\<alpha>_eq_dereference)


*)




















type_synonym function_precondition = "state \<Rightarrow> llvm_value list \<Rightarrow> bool"
type_synonym function_postcondition = "state \<Rightarrow> llvm_value list \<Rightarrow> state \<Rightarrow> llvm_value option \<Rightarrow> bool"

type_synonym block_precondition = "state \<Rightarrow> bool"
type_synonym block_preconditions = "((llvm_identifier option * llvm_identifier) * block_precondition) list"

type_synonym annotations = "(llvm_identifier * (function_precondition * block_preconditions * function_postcondition)) list"



context
  fixes annotations :: "annotations"
begin


inductive
  step_i_replaced_calls :: "instruction_state \<Rightarrow> instruction_state \<Rightarrow> bool"
and
  step_f_replaced_calls :: "function_state \<Rightarrow> function_state \<Rightarrow> bool"
where
(* Control flow *)
"step_i_replaced_calls (execi pre ([],[],br_label l) s) (flowi s (branch_label l))"

| "dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],br_i1 b l1 l2) s) (flowi s (branch_label (if b' then l1 else l2)))"
| "\<nexists>b'. dereference s b = ok (vi1 b') \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],br_i1 b l1 l2) s) erri"

| "step_i_replaced_calls (execi pre ([],[],ret None) s) (flowi s (return_value None))"

| "dereference s v = ok v' \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],ret (Some (t, v))) s) (flowi s (return_value (Some v')))"
| "dereference s v = err _ \<Longrightarrow>
    step_i_replaced_calls (execi pre ([],[],ret (Some (t, v))) s) erri"


(* Function calls *)
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> fpre (push_frame s) []
  \<Longrightarrow> fpost (push_frame s) [] s' v'
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) (execi pre ([],is,t) (pop_frame s s'))"

| "map_of (funcs program) f = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"

| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> \<not>fpre s []
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) erri"


(* Normal instructions *)
| "execute_instruction i s = ok s'
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],i#is,t) s) (execi pre ([],is,t) s')"
| "execute_instruction i s = err _
  \<Longrightarrow> \<not>is_call i
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],i#is,t) s) erri"


(* Phi nodes *)
| "execute_phi pre p s = ok s' \<Longrightarrow>
    step_i_replaced_calls (execi pre (p#ps,is,t) s) (execi pre (ps,is,t) s')"
| "execute_phi pre p s = err _ \<Longrightarrow>
    step_i_replaced_calls (execi pre (p#ps,is,t) s) erri"


(* Blocks *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) (flowi s' (branch_label l)) \<Longrightarrow>                                                          
    step_f_replaced_calls (branchf s prev lab f) (branchf s' (Some lab) l f)"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) (flowi s' (return_value v)) \<Longrightarrow>
    step_f_replaced_calls (branchf s prev lab f) (retf s' v f)"


(* Block errors *)
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = Some b \<Longrightarrow>
    step_i_replaced_calls\<^sup>*\<^sup>* (execi prev b s) erri \<Longrightarrow>
    step_f_replaced_calls (branchf s prev lab f) errf"
| "map_of (funcs program) f = Some fu \<Longrightarrow>
    map_of (llvm_function.blocks fu) lab = None \<Longrightarrow>
     step_f_replaced_calls (branchf s prev lab f) errf"
| "map_of (funcs program) f = None \<Longrightarrow>
     step_f_replaced_calls (branchf s prev lab f) errf"



definition "wp_func_replaced_calls s p Q \<equiv> \<forall>s'. (step_f_replaced_calls\<^sup>*\<^sup>* s s' \<and> (s' \<nexists>\<rightarrow>\<^sub>f)) \<longrightarrow> wp_steps_f_post s p s' Q"

definition "call_verification_condition \<equiv>
  \<forall>f. map_of (funcs program) f \<noteq> None \<comment> \<open>For all functions in the program\<close>
    \<longrightarrow> (map_of annotations f \<noteq> None \<comment> \<open>They are annotated\<close>
    \<and> (\<forall>fpre bpres fpost fu. map_of annotations f = Some (fpre, bpres, fpost) \<and> map_of (funcs program) f = Some fu \<comment> \<open>And for their annotations and the function body\<close>
      \<longrightarrow> (first_label fu \<noteq> None \<comment> \<open>There is a first block label\<close>
          \<and> (\<forall>l s. first_label fu = Some l \<and> fpre s [] \<comment> \<open>And for the first block label and all states that satisfy the precondition\<close>
            \<longrightarrow> wp_func_replaced_calls (branchf s None l f) [] fpost \<comment> \<open>Will satisfy the postcondition of the function with calls replaced\<close>
            )
          )
      )
    )"

lemma unfolded_wp_vc:
  assumes "call_verification_condition"
  assumes "map_of annotations f = Some (fpre, bpres, fpost)"
  assumes "map_of (funcs program) f = Some fu"
  assumes "first_label fu = Some l"
  assumes "fpre s []"
  assumes "s' \<nexists>\<rightarrow>\<^sub>f"
  assumes "p = None"
  assumes "trans_closure_n step_f_n (branchf s p l f) n s'"
  shows "wp_steps_f_post (branchf s p l f) [] s' fpost"
proof -
  have "branchf s None l f \<rightarrow>\<^sub>f* s'"
    using assms(8) assms(7) n_steps_impl_steps
    by blast

  then show ?thesis
    using assms(6)
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case
      by fastforce
  next
    case (step smid send)

    obtain m where "step_f_n smid m send"
      using step(2) step_impl_exists_n_step
      by blast
    then have "m \<le> n"
      sorry

    obtain ms mp ml mf where "smid = branchf ms mp ml mf"
      by (metis terminal_impl_no_next_state(2) function_state.collapse(3) function_state.exhaust_disc is_branchf_def is_retf_def step.hyps(2)
          terminal_state_simps(4,5))

    then show ?case
      using assms(2,3,4,5,6,7) \<open>m \<le> n\<close>
    proof (induction n arbitrary: s l f s' rule: less_induct)
      case (less n s l f s')
      then show ?case
      proof (cases "m < n")
        case True
        
        then show ?thesis
          using less
          by blast
      next
        case False
        then have "m = n"
          using less by force

        then show ?thesis 
        proof (cases "m = 0")
          case True
          then show ?thesis
            using assms(1)
            unfolding call_verification_condition_def
            apply (elim allE[where x=f])
            apply (elim impE) using less apply blast
            apply (elim conjE)
            apply (erule allE[where x=fpre])
            apply (erule allE[where x=bpres])
            apply (erule allE[where x=fpost])
            apply (erule allE[where x=fu])
            apply (elim impE) using less apply blast
            apply (elim conjE impE)
            apply (erule allE[where x=l])
            apply (erule allE[where x=s])
            apply (elim impE) using less apply blast
            unfolding wp_func_replaced_calls_def
            subgoal premises prems
          proof -
            have "step_f_replaced_calls\<^sup>*\<^sup>* smid send"
              
              sorry
            then have "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s p l f) smid"
              sorry
            then show ?thesis
              using less step prems
              by (metis \<open>local.step_f_replaced_calls\<^sup>*\<^sup>* smid send\<close> rtranclp_trans)
          qed
          done
        next
          case False
          then show ?thesis sorry
        qed
      qed
    qed
  qed
qed


lemma
  assumes "call_verification_condition"
  shows "\<forall>f. map_of (funcs program) f \<noteq> None \<comment> \<open>For all functions in the program\<close>
    \<longrightarrow> (map_of annotations f \<noteq> None \<comment> \<open>They are annotated\<close>
    \<and> (\<forall>fpre bpres fpost fu. map_of annotations f = Some (fpre, bpres, fpost) \<and> map_of (funcs program) f = Some fu \<comment> \<open>And for their annotations and the function body\<close>
      \<longrightarrow> (first_label fu \<noteq> None \<comment> \<open>There is a first block label\<close>
          \<and> (\<forall>l s. first_label fu = Some l \<and> fpre s [] \<comment> \<open>And for the first block label and all states that satisfy the precondition\<close>
            \<longrightarrow> wp_steps_f (branchf s None l f) [] fpost \<comment> \<open>Will satisfy the postcondition of the function\<close>
            )
          )
      )
    )"
  apply (intro allI impI conjI)
  subgoal
    using assms
    unfolding call_verification_condition_def
    by blast
  subgoal
    using assms
    unfolding call_verification_condition_def
    by blast
  apply simp
  apply (elim conjE)
  unfolding wp_steps_f_def
  apply (intro allI impI)
  apply (elim conjE)
  apply (drule steps_impl_exists_n_steps)
  apply (elim exE)
  using unfolded_wp_vc assms by blast


definition "has_annotation fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf _ _ f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and> map_of annotations f \<noteq> None
  | branchf _ p l f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre,bpres,fpost) \<Rightarrow> map_of bpres (p,l) \<noteq> None
      )
  )"

definition "annotation_holds fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf s v f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre,bpres,fpost) \<Rightarrow> fpost s v
      )
  | branchf s p l f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (pres,post) \<Rightarrow>
          (case map_of pres (p,l) of
            None \<Rightarrow> False
          | Some pre \<Rightarrow> pre s
          )
      )
  )"


definition step_until :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" where
  "step_until fs fs' \<equiv> fs \<rightarrow>\<^sub>f fs' \<and> \<not>has_annotation fs"



definition annotated_step_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>f" 50) where
  "s \<Rightarrow>\<^sub>f s' \<equiv> (\<exists>x. s \<rightarrow>\<^sub>f x \<and> step_until\<^sup>*\<^sup>* x s') \<and> (has_annotation s' \<or> is_errf s')"
abbreviation annotated_steps_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>f*" 50) where
  "fs \<Rightarrow>\<^sub>f* fs' \<equiv> annotated_step_f\<^sup>*\<^sup>* fs fs'"



definition wp_step where
  "wp_step fs Q \<equiv> (\<forall>fs'. fs \<rightarrow>\<^sub>f fs' \<longrightarrow> \<not>is_errf fs' \<and> Q fs')"

definition wp_steps_until where
  "wp_steps_until fs Q \<equiv> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> \<not>is_errf fs \<longrightarrow> \<not>is_errf fs') \<and> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> has_annotation fs' \<longrightarrow> Q fs')"

definition wp_annotated_step_f where
  "wp_annotated_step_f fs Q \<equiv> (\<forall>fs'. fs \<Rightarrow>\<^sub>f fs' \<longrightarrow> \<not>is_errf fs' \<and> Q fs')"

lemma wp_step_intro:
  assumes "map_of (funcs program) f = Some fu"
  assumes "map_of (llvm_function.blocks fu) l = Some b"
  assumes "wp_instrs
    (execi p b s)
    (\<lambda>s'.
      (case s' of
        (flowi s'' br) \<Rightarrow>
          (case br of
            branch_label l' \<Rightarrow> Q (branchf s'' (Some l) l' f)
          | return_value v  \<Rightarrow> Q (retf s'' v f)
          )
      )
    )"
  shows "wp_step (branchf s p l f) Q"
    using assms
    unfolding wp_step_def wp_instrs_def
    apply clarsimp
    subgoal premises prems for fs'
    proof (cases fs')
      case (branchf x11 x12 x13 x14)
      then show ?thesis
        by (smt (verit) function_state.disc function_state.sel instruction_state.simps
            is_errf_def llvm_block_return.simps option.sel prems step_f.cases terminal_state_simps)
    next
      case (retf x21 x22)
      then show ?thesis
        by (smt (verit) function_state.disc function_state.sel instruction_state.simps
            is_errf_def llvm_block_return.simps option.sel prems step_f.cases terminal_state_simps)
    next
      case errf
      then show ?thesis
        by (smt (verit) assms function_state.disc instruction_state.disc function_state.inject function_state.sel instruction_state.simps
            is_errf_def llvm_block_return.simps option.sel prems step_f.cases terminal_state_simps option.distinct)
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
  shows "wp_annotated_step_f fs Q"
  using assms converse_rtranclpE
  unfolding wp_annotated_step_f_def wp_step_def annotated_step_f_def wp_steps_until_def
  by blast










lemma instrs_call_intro[wp_instrs_intro]:
  assumes "map_of (funcs program) f = Some fu"
  assumes "first_label fu = Some b"
  assumes "map_of annotations f = Some (pres, post)"
  assumes "map_of pres (None, b) = Some precond"
  assumes "precond (push_frame s)"
  assumes "\<And>s' v'. post s' v' \<Longrightarrow> wp_instrs (execi pre ([], is, t) (pop_frame s s')) Q"
  shows "wp_instrs (execi pre ([], (call n ty f p)#is, t) s) Q"
proof -
  show ?thesis sorry
qed


definition "floyd_cond s p l f \<equiv> wp_annotated_step_f (branchf s p l f) (\<lambda>fs'. annotation_holds fs')"


definition floyd_vc :: "bool" where
  "floyd_vc \<equiv>
    \<forall>f. map_of (funcs program) f \<noteq> None \<longrightarrow> \<comment> \<open>for all functions in our program\<close>
    first_label (the (map_of (funcs program) f)) \<noteq> None \<and> \<comment> \<open>there is a first block\<close>
    (case map_of annotations f of
      None \<Rightarrow> False \<comment> \<open>and there are annotations\<close>
    | Some (pres,post) \<Rightarrow>
        (map_of pres (None, the (first_label (the (map_of (funcs program) f)))) \<noteq> None) \<and> \<comment> \<open>and the first block has a precondition\<close>
        (\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
          (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
        )
    )"











fun annotation_holds_list where
  "annotation_holds_list P [] = True"
| "annotation_holds_list P (((p,l),pre)#pres) = (P p l \<and> annotation_holds_list P pres)"

lemma annotation_holds_list_imp_annotation_holds:
  assumes "annotation_holds_list (\<lambda>p l. (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f)) pres"
  shows "(\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
          (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
        )"
  using assms
  apply (induction pres)
  apply force
  subgoal for pre pres
    apply (intro allI impI)
    subgoal for p l s
      apply (cases "pre")
      subgoal for br precond
        apply (cases "br = (p,l)")
        subgoal
          by (metis (no_types, lifting) annotation_holds_list.simps(2))
        subgoal premises prems
        proof -
          have "annotation_holds_list (\<lambda>p l. (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f)) pres"
            using prems annotation_holds_list.elims(2)
            by blast 
          
          then show ?thesis
            using prems map_of_Cons_code(2)
            by metis
        qed
        done
      done
    done
  done

fun annotations_hold_list :: "(llvm_identifier \<Rightarrow> bool) \<Rightarrow> (llvm_identifier * llvm_function) list \<Rightarrow> bool" where
  "annotations_hold_list P [] = True"
| "annotations_hold_list P ((fi,fu)#funs) = (P fi \<and> annotations_hold_list P funs)"

lemma annotations_hold_list_imp_floyd_vc:
  assumes "annotations_hold_list (\<lambda>f. first_label (the (map_of (funcs program) f)) \<noteq> None \<and> \<comment> \<open>there is a first block\<close>
    (case map_of annotations f of
      None \<Rightarrow> False \<comment> \<open>and there are annotations\<close>
    | Some (pres,post) \<Rightarrow>
        (map_of pres (None, the (first_label (the (map_of (funcs program) f)))) \<noteq> None) \<and> \<comment> \<open>and the first block has a precondition\<close>
        (\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
          (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
        )
    )) funs"
  shows "\<forall>f. map_of (funs) f \<noteq> None \<longrightarrow> \<comment> \<open>for all functions in our program\<close>
    first_label (the (map_of (funcs program) f)) \<noteq> None \<and> \<comment> \<open>there is a first block\<close>
    (case map_of annotations f of
      None \<Rightarrow> False \<comment> \<open>and there are annotations\<close>
    | Some (pres,post) \<Rightarrow>
        (map_of pres (None, the (first_label (the (map_of (funcs program) f)))) \<noteq> None) \<and> \<comment> \<open>and the first block has a precondition\<close>
        (\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
          (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
        )
    )"
  using assms
  apply (induction funs)
  apply force
  subgoal for f fs
    apply (cases f)
    apply (intro allI impI)
    subgoal for fi fu f'
      apply (cases "fi = f'")
      subgoal
        using annotations_hold_list.simps(2) n_lists.simps(2) split_cong option.case_eq_if
        by (smt (verit))
      subgoal premises prems
      proof -
        have "annotations_hold_list (\<lambda>f. first_label (the (map_of (funcs program) f)) \<noteq> None \<and> \<comment> \<open>there is a first block\<close>
          (case map_of annotations f of
            None \<Rightarrow> False \<comment> \<open>and there are annotations\<close>
          | Some (pres,post) \<Rightarrow>
            (map_of pres (None, the (first_label (the (map_of (funcs program) f)))) \<noteq> None) \<and> \<comment> \<open>and the first block has a precondition\<close>
              (\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
                (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
              )
          )) fs" using prems
          by (metis (no_types, lifting) annotations_hold_list.simps(2))
        then show ?thesis
          using prems(1,3,4,5) by fastforce
      qed
      done
    done
  done

lemma floyd_vc_intro:
  assumes "annotations_hold_list (\<lambda>f. first_label (the (map_of (funcs program) f)) \<noteq> None \<and> \<comment> \<open>there is a first block\<close>
    (case map_of annotations f of
      None \<Rightarrow> False \<comment> \<open>and there are annotations\<close>
    | Some (pres,post) \<Rightarrow>
        (map_of pres (None, the (first_label (the (map_of (funcs program) f)))) \<noteq> None) \<and> \<comment> \<open>and the first block has a precondition\<close>
        (\<forall>p l. map_of pres (p,l) \<noteq> None \<longrightarrow> \<comment> \<open>and for all annotated blocks\<close>
          (\<forall>s. annotation_holds (branchf s p l f) \<longrightarrow> floyd_cond s p l f) \<comment> \<open>all states that satisfy the precond will satisfy any following precond\<close>
        )
    )) (funcs program)"
  shows "floyd_vc"
  using assms annotations_hold_list_imp_floyd_vc
  unfolding floyd_vc_def
  by blast


lemma floyd_vc_impl_annotation_holds:
  assumes "floyd_vc"
  shows "\<forall>fs fs'. annotation_holds fs \<and> fs \<Rightarrow>\<^sub>f fs' \<longrightarrow> annotation_holds fs'"
  apply (auto split: function_state.splits)
  subgoal premises prems for fs fs'
  proof (cases fs)
    case (branchf s p l f)
    then show ?thesis
      using assms prems
      unfolding floyd_vc_def floyd_cond_def wp_annotated_step_f_def annotation_holds_def
      by (smt (verit, ccfv_SIG) case_optionE case_prodE case_prod_conv function_state.simps(9) option.simps(4,5))
  next
    case (retf x21 x22 x23)
    then show ?thesis
      using annotated_step_f_def local.terminal_state_simps local.terminal_f_def prems
      by blast
  next
    case errf
    then show ?thesis 
      using annotated_step_f_def local.terminal_state_simps local.terminal_f_def prems
      by force 
  qed
  done

lemma floyd_vc_impl_annotated_steps_hold:
  assumes "fs \<Rightarrow>\<^sub>f* fs'"
  assumes "floyd_vc"
  assumes "annotation_holds fs"
  shows "annotation_holds fs'"
  using assms floyd_vc_impl_annotation_holds
  by (induction rule: converse_rtranclp_induct; blast)

lemma exists_first_cutpoint:
  assumes "fs (\<rightarrow>\<^sub>f)^n fs'"
  assumes "is_errf fs' \<or> has_annotation fs'"
  shows "\<exists>fsp m. step_until\<^sup>*\<^sup>* fs fsp \<and> (is_errf fsp \<or> has_annotation fsp) \<and> fsp (\<rightarrow>\<^sub>f)^m fs' \<and> m \<le> n"
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
  assumes path: "fs \<rightarrow>\<^sub>f* fs'"
  assumes annot: "has_annotation fs' \<or> is_errf fs'"
  shows "fs \<Rightarrow>\<^sub>f* fs'"
proof -
  obtain n where ndef: "fs (\<rightarrow>\<^sub>f)^n fs'" using path closure_steps_exists_n_steps by fast
  
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
        then obtain fs1 where fs1def1: "fs \<rightarrow>\<^sub>f fs1" and fs1def: "fs1 (\<rightarrow>\<^sub>f)^n' fs'"
          using less ndef
          by auto

        obtain fsa m where "step_until\<^sup>*\<^sup>* fs1 fsa" "has_annotation fsa \<or> is_errf fsa" "fsa (\<rightarrow>\<^sub>f)^m fs'" "m \<le> n'"
          using fs1def exists_first_cutpoint annot
          by blast

      then have "fs \<Rightarrow>\<^sub>f fsa" using fs1def1 unfolding annotated_step_f_def by blast

      also from less.IH[OF _ \<open>fsa (\<rightarrow>\<^sub>f)^m fs'\<close>] \<open>m \<le> n'\<close> Suc annot have "fsa \<Rightarrow>\<^sub>f* fs'" by force
      
      finally show ?thesis .
      qed
    qed
  qed


lemma function_steps_keep_function:
  assumes "fs \<rightarrow>\<^sub>f* fs'"
  assumes "fs = branchf s p l f"
  shows "(case fs' of retf s' v f' \<Rightarrow> f' = f | branchf s' p' l' f' \<Rightarrow> f' = f | errf \<Rightarrow> True)"
proof (cases fs')
  case (branchf s' p' l' f')
  show ?thesis
    using assms(1)
    apply (induction rule: rtranclp_induct)
    using assms(2)
     apply simp
    using local.step_f.cases by fastforce
next
  case (retf x21 x22 x23)
  show ?thesis 
    using assms(1)
    apply (induction rule: rtranclp_induct)
    using assms(2)
     apply simp
    using local.step_f.cases by fastforce
next
  case errf
  then show ?thesis
    by simp
qed


lemma floyd_vc_impl_wp_step:
  assumes "floyd_vc"
  assumes "map_of (funcs program) f = Some fu"
  assumes "map_of annotations f = Some (pres,post)"
  assumes "first_label fu = Some fl"
  assumes "annotation_holds fs"
  assumes "fs = branchf s None fl f"
  shows "wp_func fs post"
  unfolding wp_func_def
  apply (intro allI impI)
  subgoal premises prems for fs'
  proof -
    have "has_annotation fs'"
      unfolding has_annotation_def 
      by (smt (verit, ccfv_SIG) Steps.terminal_non_err annotation_holds_def assms(1,5) floyd_vc_def
          floyd_vc_impl_annotated_steps_hold function_state.case_eq_if function_state.disc(2) function_state.sel(7)
          function_state.simps(11) function_state.split_sel_asm is_errf_def le_boolD local.step_f.cases
          local.terminal_state_simps(3) option.distinct(1) option.simps(4) prems rtranclp.simps
          steps_to_annotation_impl_annotated_steps)
    
    then have "fs \<Rightarrow>\<^sub>f* fs'" using prems steps_to_annotation_impl_annotated_steps
      by blast

    then have "annotation_holds fs'"
      using assms(1,5) floyd_vc_impl_annotated_steps_hold by blast

    then show ?thesis
      using prems
      unfolding annotation_holds_def
      apply (cases fs')
      defer defer apply force defer apply (erule conjE)
      subgoal premises prems' for s v f'
      proof -
        have "f = f'" using prems' function_steps_keep_function assms function_state.simps
          by (smt (verit, ccfv_threshold))

        then show ?thesis
          using assms prems'
          by force
      qed
      
      done
  qed
  done

end


end



end