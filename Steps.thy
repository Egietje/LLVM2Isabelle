theory Steps
  imports Blocks
begin

context fixes program :: "llvm_program"
begin

section "Step Relation"

datatype instruction_state = 
    execi "llvm_identifier option" llvm_instruction_block state
  | flowi state llvm_block_return
  | is_erri: erri

datatype (discs_sels) function_state = 
    branchf (state: state) "llvm_identifier option" llvm_identifier llvm_identifier
  | retf (state: state) (ret_value: "llvm_value option") (ret_func: llvm_identifier)
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


abbreviation steps_i (infix "\<rightarrow>\<^sub>i*" 50) where
  "s \<rightarrow>\<^sub>i* s' \<equiv> step_i\<^sup>*\<^sup>* s s'"
abbreviation steps_f :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f*" 50) where
  "s \<rightarrow>\<^sub>f* s' \<equiv> step_f\<^sup>*\<^sup>* s s'"


section "Terminal States"

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


section "Determinism"

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

    have "\<And>s' v'. \<not>(branchf (push_frame s) None b f) \<rightarrow>\<^sub>f* retf s' v' f"
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



section "Weakest Precondition over Steps"

definition "wp_steps_i s Q \<equiv> \<forall>s'. terminates_to_i s s' \<longrightarrow> \<not>is_erri s' \<and> Q s'"
definition "wp_steps_f_post s p s' Q \<equiv> (\<not>is_errf s') \<and> (Q (state s) p (state s') (ret_value s'))"
definition "wp_steps_f s p Q \<equiv> \<forall>s'. terminates_to_f s s' \<longrightarrow> wp_steps_f_post s p s' Q"



section "Annotations"

type_synonym function_precondition = "state \<Rightarrow> llvm_value list \<Rightarrow> bool"
type_synonym function_postcondition = "state \<Rightarrow> llvm_value list \<Rightarrow> state \<Rightarrow> llvm_value option \<Rightarrow> bool"
type_synonym block_precondition = "state \<Rightarrow> bool"
type_synonym block_preconditions = "((llvm_identifier option * llvm_identifier) * block_precondition) list"
type_synonym annotations = "(llvm_identifier * (function_precondition * block_preconditions * function_postcondition)) list"

context
  fixes annotations :: "annotations"
begin



section "Replace Calls"

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

(* Precondition Failure / Missing Annotations step to ANY state si' (Chaos Over-approximation) *)
| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = Some (fpre,bpres,fpost)
  \<Longrightarrow> \<not>fpre (push_frame s) []
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) si'"

| "map_of (funcs program) f = Some fu
  \<Longrightarrow> first_label fu = Some b
  \<Longrightarrow> map_of annotations f = None
  \<Longrightarrow> step_i_replaced_calls (execi pre ([],(call na ty f p)#is,t) s) si'"

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
  ((\<forall>f fu fpre bpres fpost l s.
    map_of (funcs program) f = Some fu \<and> 
    map_of annotations f = Some (fpre, bpres, fpost) \<and>
    first_label fu = Some l \<and> 
    fpre s []
    \<longrightarrow> wp_func_replaced_calls (branchf s None l f) [] fpost)
  \<and> (\<forall>f. map_of (funcs program) f \<noteq> None \<longrightarrow> map_of annotations f \<noteq> None))"

definition "global_verification_condition \<equiv>
  ((\<forall>f fu fpre bpres fpost l s.
    map_of (funcs program) f = Some fu \<and>
    map_of annotations f = Some (fpre, bpres, fpost) \<and>
    first_label fu = Some l \<and> 
    fpre s []
    \<longrightarrow> wp_steps_f (branchf s None l f) [] fpost)
  \<and> (\<forall>f. map_of (funcs program) f \<noteq> None \<longrightarrow> map_of annotations f \<noteq> None))"

lemma step_impl_step_replaced:
  assumes "call_verification_condition"
  shows "step_i si si' \<Longrightarrow> step_i_replaced_calls si si'"
    and "step_f sf sf' \<Longrightarrow> step_f_replaced_calls sf sf'"
proof (induction rule: step_i_step_f.inducts)
  case (1 pre l s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (2 s b b' pre l1 l2)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (3 s b pre l1 l2)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (4 pre s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (5 s v v' pre t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (6 s v uu pre t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (7 f fu b s s' v' pre n ty p "is" t)
 \<comment> \<open> our IH: it holds for the function we call \<close>
  then have IH_f: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf (push_frame s) None b f) (retf s' v' f)"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> depending on if we have annotations\<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to ANY next state (undeterministic), so that includes the proper state we need \<close>
      \<comment> \<open> this is safe for our verification since that ALSO means it can step to an error,
           which means our verification conditions cannot proved if there are no annotations \<close>
      then show ?thesis
        by (simp add: "7.IH"(1) "7.hyps" step_i_replaced_calls_step_f_replaced_calls.intros(11))
    next
      case False
      \<comment> \<open> if we have annotations - obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        unfolding call_verification_condition_def
        by fast

      then show ?thesis
      \<comment> \<open> depending on if the precondition holds at this point \<close>
      proof (cases "fpre (push_frame s) []")
        case True
       \<comment> \<open> the precondition holds, which means the pre/post pair holds (per the verification condition) \<close>
       then have "wp_func_replaced_calls (branchf (push_frame s) None b f) [] fpost"
          using assms 7 annots
          unfolding call_verification_condition_def 
          by blast

       \<comment> \<open> extract the postcondition \<close>
       hence "wp_steps_f_post (branchf (push_frame s) None b f) [] (retf s' v' f) fpost"
          unfolding wp_func_replaced_calls_def 
          using IH_f terminal_f_def by simp
       hence post_holds: "fpost (push_frame s) [] s' v'"
          unfolding wp_steps_f_post_def by simp

        \<comment> \<open> and then we have our thesis - we have the postcondition just like in the replaced step relation \<close>
        then show ?thesis
          by (simp add: 7 True annots step_i_replaced_calls_step_f_replaced_calls.intros(7))
      next
        case False
        \<comment> \<open> if not - we again do not know the next state so we can step to ANY state, safe for the same reason as before \<close>
        then show ?thesis
          by (simp add: "7.IH"(1) "7.hyps" annots step_i_replaced_calls_step_f_replaced_calls.intros(10))
      qed
    qed
next
  case (8 f pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (9 f fu pre n ty p "is" t s)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (10 f fu b s pre n ty p "is" t)

  \<comment> \<open> our IH: it holds for the called function \<close>
  then have IH_f: "step_f_replaced_calls\<^sup>*\<^sup>* (branchf (push_frame s) None b f) errf"
    using mono_rtranclp
    by (metis (no_types, lifting))

  then show ?case
    \<comment> \<open> once again split based on whether we have annotations \<close>
    proof (cases "map_of annotations f = None")
      case True
      \<comment> \<open> if not - we can step to any next state including err \<close>
      then show ?thesis
        by (simp add: 10 step_i_replaced_calls_step_f_replaced_calls.intros(11))
    next
      case False
      \<comment> \<open> if we do, obtain them \<close>
      then obtain fpre bpres fpost where annots: "map_of annotations f = Some (fpre, bpres, fpost)"
        by fast
      
      \<comment> \<open> and show this means we do not satisfy the precondition \<close>
      then have "\<not> fpre (push_frame s) []"
      proof -
        \<comment> \<open> if we did have the precond, then the weakest precondition over steps would hold by our vc  \<close>
        have "fpre (push_frame s) [] \<Longrightarrow> wp_func_replaced_calls (branchf (push_frame s) None b f) [] fpost"
          using assms 10 annots
          unfolding call_verification_condition_def
          by blast
        \<comment> \<open> which means it holds for an error \<close>
        hence "fpre (push_frame s) [] \<Longrightarrow> wp_steps_f_post (branchf (push_frame s) None b f) [] errf fpost"
          unfolding wp_func_replaced_calls_def 
          using IH_f terminal_f_def
          by simp
        \<comment> \<open> however, that is a contradiction since wp specifies it does not reach errors \<close>
        then show ?thesis
          unfolding wp_steps_f_post_def by fastforce
      qed

      \<comment> \<open> since we don't have the precondition, we can transition to any state including err \<close>
      then show ?thesis
        by (simp add: "10.IH"(1) "10.hyps" annots step_i_replaced_calls_step_f_replaced_calls.intros(10))
    qed
next
  case (11 i s s' pre "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (12 i s uv pre "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (13 pre p s s' ps "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (14 pre p s uw ps "is" t)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (15 f fu lab b prev s s' l)
  then show ?case
    by (metis (no_types, lifting) mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros(16))
next
  case (16 f fu lab b prev s s' v)
  then show ?case
    by (metis (no_types, lifting) mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros(17))
next
  case (17 f fu lab b prev s)
  then show ?case
    by (metis (no_types, lifting) mono_rtranclp step_i_replaced_calls_step_f_replaced_calls.intros(18))
next
  case (18 f fu lab s prev)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
next
  case (19 f s prev lab)
  then show ?case
    by (simp add: step_i_replaced_calls_step_f_replaced_calls.intros)
qed




lemma unfolded_wp_vc:
  assumes "call_verification_condition"
  assumes "map_of (funcs program) f = Some fu"
  assumes "map_of annotations f = Some (fpre, bpres, fpost)"
  assumes "first_label fu = Some l"
  assumes "fpre s []"
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* (branchf s None l f) s'"
  assumes "s' \<nexists>\<rightarrow>\<^sub>f"
  shows "wp_steps_f_post (branchf s None l f) [] s' fpost"
  by (smt (verit, best) Steps.wp_func_replaced_calls_def assms(1,2,3,4,5,6,7) call_verification_condition_def)


lemma call_vc_impl_global_vc:
  "call_verification_condition \<Longrightarrow> global_verification_condition"
  unfolding global_verification_condition_def wp_steps_f_def
  apply (intro allI conjI impI)
   apply (smt (verit, ccfv_threshold) mono_rtranclp step_impl_step_replaced(2) unfolded_wp_vc)
  unfolding call_verification_condition_def
  by blast



section "Floyd Method"

fun replaced_n_steps :: "function_state \<Rightarrow> nat \<Rightarrow> function_state \<Rightarrow> bool" ("_ (\<rightarrow>\<^sub>f\<^sub>R)^_ _" [50,0,51] 50) where
  "fs \<rightarrow>\<^sub>f\<^sub>R^0 fs' = (fs' = fs)"
| "fs \<rightarrow>\<^sub>f\<^sub>R^(Suc n) fs' = (\<exists>fs''. step_f_replaced_calls fs fs'' \<and> fs'' \<rightarrow>\<^sub>f\<^sub>R^n fs')"

lemma exists_n_replaced_steps:
  "step_f_replaced_calls\<^sup>*\<^sup>* fs fs' \<Longrightarrow> \<exists>n. fs \<rightarrow>\<^sub>f\<^sub>R^n fs'"
  apply (induction rule: converse_rtranclp_induct)
  using replaced_n_steps.simps by blast+

definition "has_annotation fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf _ _ f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and> map_of annotations f \<noteq> None
  | branchf _ p l f \<Rightarrow> map_of (funcs program) f \<noteq> None \<and>
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow> p = None \<or> map_of bpres (p, l) \<noteq> None
      )
  )"

definition "annotation_holds s_init fs \<equiv>
  (case fs of
    errf \<Rightarrow> False
  | retf s v f \<Rightarrow> 
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow> fpost s_init [] s v
      )
  | branchf s p l f \<Rightarrow> 
      (case map_of annotations f of 
        None \<Rightarrow> False
      | Some (fpre, bpres, fpost) \<Rightarrow>
          (case p of
            None \<Rightarrow> fpre s []
          | Some pred \<Rightarrow> 
              (case map_of bpres (Some pred, l) of
                None \<Rightarrow> False
              | Some pre \<Rightarrow> pre s
              )
          )
      )
  )"

definition step_until :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" where
  "step_until fs fs' \<equiv> step_f_replaced_calls fs fs' \<and> \<not>has_annotation fs"

definition annotated_step :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "s \<Rightarrow> s' \<equiv> (\<exists>x. step_f_replaced_calls s x \<and> step_until\<^sup>*\<^sup>* x s') \<and> (has_annotation s' \<or> is_errf s')"

abbreviation annotated_steps :: "function_state \<Rightarrow> function_state \<Rightarrow> bool" (infix "\<Rightarrow>*" 50) where
  "fs \<Rightarrow>* fs' \<equiv> annotated_step\<^sup>*\<^sup>* fs fs'"

definition wp_step where
  "wp_step fs Q \<equiv> (\<forall>fs'. step_f_replaced_calls fs fs' \<longrightarrow> \<not>is_errf fs' \<and> Q fs')"

definition wp_func where
  "wp_func fs Q \<equiv> (\<forall>fs'. fs \<rightarrow>\<^sub>f* fs' \<and> (fs' \<nexists>\<rightarrow>\<^sub>f) \<longrightarrow> \<not>is_errf fs' \<and> (case fs' of retf s' v' _ \<Rightarrow> Q s' v' | _ \<Rightarrow> False))"

definition
  "wp_func_replaced_calls s Q \<equiv> \<forall>s'. (step_f_replaced_calls\<^sup>*\<^sup>* s s' \<and> (s' \<nexists>\<rightarrow>\<^sub>f)) \<longrightarrow> \<not>is_errf s' \<and> (case s' of retf s_res v_res _ \<Rightarrow> Q s_res v_res | _ \<Rightarrow> False)"

definition "call_verification_condition \<equiv>
  ((\<forall>f fu pres post l s.
    map_of (funcs program) f = Some fu \<and> 
    map_of annotations f = Some (pres, post) \<and>
    first_label fu = Some l \<and> 
    (case map_of pres (None, l) of Some precond \<Rightarrow> precond s | None \<Rightarrow> False)
    \<longrightarrow> wp_func_replaced_calls (branchf s None l f) post)
  \<and> (\<forall>f. map_of (funcs program) f \<noteq> None \<longrightarrow> map_of annotations f \<noteq> None))"

definition wp_steps_until where
  "wp_steps_until fs Q \<equiv> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> \<not>is_errf fs \<longrightarrow> \<not>is_errf fs') \<and> (\<forall>fs'. (step_until)\<^sup>*\<^sup>* fs fs' \<and> has_annotation fs' \<longrightarrow> Q fs')"

definition wp_annotated_step_f where
  "wp_annotated_step_f fs Q \<equiv> (\<forall>fs'. ((fs \<Rightarrow> fs') \<longrightarrow> (\<not>is_errf fs' \<and> Q fs')))"

definition "floyd_cond s_init s p l f \<equiv> wp_annotated_step_f (branchf s p l f) (\<lambda>fs'. annotation_holds s_init fs')"

definition floyd_vc :: "bool" where
  "floyd_vc \<equiv>
    \<forall>f. map_of (funcs program) f \<noteq> None \<longrightarrow> 
    (case map_of annotations f of
      None \<Rightarrow> False 
    | Some (fpre, bpres, fpost) \<Rightarrow>
        (first_label (the (map_of (funcs program) f)) \<noteq> None) \<and> 
        (\<forall>s_init. fpre s_init [] \<longrightarrow> 
           floyd_cond s_init s_init None (the (first_label (the (map_of (funcs program) f)))) f) \<and>
        (\<forall>pred l. map_of bpres (Some pred, l) \<noteq> None \<longrightarrow> 
           (\<forall>s_init s. annotation_holds s_init (branchf s (Some pred) l f) \<longrightarrow> 
              floyd_cond s_init s (Some pred) l f)
        )
    )"


lemma step_until_closure_to_annotated_step:
  assumes "step_f_replaced_calls fs x"
  assumes "step_until\<^sup>*\<^sup>* x fs'"
  assumes "has_annotation fs' \<or> is_errf fs'"
  shows "fs \<Rightarrow>\<^sub>f fs'"
  unfolding annotated_step_f_def
  using assms
  by blast


lemma steps_impl_annotated_steps:
  assumes "step_f_replaced_calls\<^sup>*\<^sup>* sf sf'"
  assumes "has_annotation sf'"
  shows "sf \<Rightarrow>* sf'"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step.IH show ?case


end
end