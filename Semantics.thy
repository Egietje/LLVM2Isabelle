theory Semantics
  imports "Definitions" "Registers" "Memory" "Partial_Function_MR/Partial_Function_MR"
begin

section "Simps"

lemma wp_case_value_addr_intro[wp_intro]:
  assumes "\<And>x. a = addr x \<Longrightarrow> wp (f x) Q"
  assumes "\<not>(\<exists>x. a = addr x) \<Longrightarrow> wp g Q"
  shows "wp (case a of addr x \<Rightarrow> f x | _ \<Rightarrow> g) Q"
  using assms
  unfolding wp_def
  by (cases "a"; auto)



section "Memory instructions"

definition execute_alloca :: "llvm_identifier \<Rightarrow> state \<Rightarrow> state option" where
  "execute_alloca name s = do {
      (s', a) \<leftarrow> Some (allocate_stack s);
      set_register name (addr a) s'
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
  


fun get_address_from_pointer :: "state \<Rightarrow> llvm_pointer \<Rightarrow> llvm_address option" where
  "get_address_from_pointer s p = do {
    a \<leftarrow> get_register s p;
    (case a of (addr a') \<Rightarrow> Some a' | _ \<Rightarrow> None)
  }"

definition execute_store :: "llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state option" where
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


definition execute_load :: "llvm_identifier \<Rightarrow> llvm_pointer \<Rightarrow> state \<Rightarrow> state option" where
  "execute_load n p s = do {
    a \<leftarrow> get_address_from_pointer s p;
    v \<leftarrow> get_memory s a;
    set_register n v s
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


fun add_values :: "llvm_add_wrap \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value option" where
  "add_values wrap (vi32 a) (vi32 b) = (if add_no_poison32 wrap a b then Some (vi32 (a+b)) else Some poison)"
| "add_values wrap (vi64 a) (vi64 b) = (if add_no_poison64 wrap a b then Some (vi64 (a+b)) else Some poison)"
| "add_values _ poison (vi32 _) = Some poison"
| "add_values _ (vi32 _) poison = Some poison"
| "add_values _ poison (vi64 _) = Some poison"
| "add_values _ (vi64 _) poison = Some poison"
| "add_values _ poison poison = Some poison"
| "add_values _ _ _ = None"


definition execute_add :: "llvm_identifier \<Rightarrow> llvm_add_wrap \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state option" where
  "execute_add name wrap v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> add_values wrap v1' v2';
    set_register name res s
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
fun compare_values :: "llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value option" where
  "compare_values c (vi32 a) (vi32 b) = Some (compare_values_32 c a b)"
| "compare_values c (vi64 a) (vi64 b) = Some (compare_values_64 c a b)"
| "compare_values _ _ _ = None"

fun same_signs32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "same_signs32 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"
fun same_signs64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "same_signs64 a b = ((a <s 0 \<and> b <s 0) \<or> (0 \<le>s a \<and> 0 \<le>s b))"

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value option" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if same_signs32 a b then compare_values c (vi32 a) (vi32 b) else Some poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if same_signs64 a b then compare_values c (vi64 a) (vi64 b) else Some poison)"
| "compare_values_sign True c _ _ = None"

definition execute_icmp :: "llvm_identifier \<Rightarrow> llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state \<Rightarrow> state option" where
  "execute_icmp name same_sign cond v1 v2 s = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    set_register name res s
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



section "Phi nodes"

fun phi_lookup :: "llvm_identifier option \<Rightarrow> (llvm_identifier * llvm_value_ref) list \<Rightarrow> llvm_value_ref option" where
  "phi_lookup l ls = do {
    prev \<leftarrow> l;
    assert (distinct (map fst ls));
    map_of ls prev
  }"

definition execute_phi :: "llvm_phi_node \<Rightarrow> llvm_identifier option \<Rightarrow> state \<Rightarrow> state option" where
  "execute_phi p prev s =
    (case p of (phi name type values) \<Rightarrow>
      do {
        v \<leftarrow> phi_lookup prev values;
        v' \<leftarrow> get_register s v;
        set_register name v' s
      }
    )"


section "Blocks and functions"

context
  fixes program :: llvm_program
begin

datatype exec_type = exec_instruction llvm_instruction
  | exec_block "llvm_identifier option" llvm_instruction_block
  | exec_blocks "llvm_identifier option" llvm_identifier llvm_labeled_blocks
  | exec_func "llvm_identifier" "llvm_value list"

datatype exec_result = state_only state
  | ctrl_flow state llvm_block_return
  | func_ret state "llvm_value option"


fun stack_size :: "state \<Rightarrow> nat" where
  "stack_size (state l g s h) = length s"
fun restore_stack :: "state \<Rightarrow> nat \<Rightarrow> state" where
  "restore_stack (state l g s h) n = (state l g (take n s) h)"
fun local_registers :: "state \<Rightarrow> (llvm_register_model * state)" where
  "local_registers (state l g s h) = (l, (state Mapping.empty g s h))"
fun restore_registers :: "state \<Rightarrow> llvm_register_model \<Rightarrow> state" where
  "restore_registers (state _ g s h) l = (state l g s h)"

fun store_parameters :: "llvm_identifier list \<Rightarrow> llvm_value list \<Rightarrow> state \<Rightarrow> state option" where
  "store_parameters (i#is) (v#vs) s = do {
    s' \<leftarrow> set_register i v s;
    store_parameters is vs s'
  }"
| "store_parameters [] [] s = Some s"
| "store_parameters _ _ _ = None"

fun get_parameters :: "llvm_value_ref list \<Rightarrow> state \<Rightarrow> (llvm_value list) option" where
  "get_parameters (v#vs) s = do {
    v' \<leftarrow> get_register s v;
    vs' \<leftarrow> get_parameters vs s;
    Some (v'#vs')
  }"
| "get_parameters [] _ = Some []"


partial_function (option) exec where
  "exec t s = (case t of
    exec_instruction (call name type fun pars) \<Rightarrow>
      do {
        ps \<leftarrow> get_parameters (map snd pars) s;
        ret \<leftarrow> exec (exec_func fun ps) s;
        (s', v) \<leftarrow> (case ret of
          func_ret s' v \<Rightarrow> Some (s', v)
        | _ \<Rightarrow> None);
        s'' \<leftarrow>
          (case name of
            Some n \<Rightarrow> do {
              v' \<leftarrow> v;
              set_register n v' s'
            }
          | None \<Rightarrow> Some s'
          );
        Some (state_only s'')
      }
  | exec_instruction i \<Rightarrow>
      do {
        s' \<leftarrow> (case i of
          alloca name type align              \<Rightarrow> execute_alloca name s
        | store type value pointer align      \<Rightarrow> execute_store value pointer s
        | load name type pointer align        \<Rightarrow> execute_load name pointer s
        | add name wrap type v1 v2            \<Rightarrow> execute_add name wrap v1 v2 s
        | icmp name same_sign cond type v1 v2 \<Rightarrow> execute_icmp name same_sign cond v1 v2 s
        );
        Some (state_only s')
      }
  | exec_block prev b \<Rightarrow>
    (case b of
      (p#ps,is,t) \<Rightarrow> do {
        s' \<leftarrow> execute_phi p prev s;
        exec (exec_block prev (ps,is,t)) s'
      }
    | ([],i#is,t) \<Rightarrow> do {
        s' \<leftarrow> exec (exec_instruction i) s;
        (case s' of
          state_only s' \<Rightarrow> exec (exec_block prev ([],is,t)) s'
        | _ \<Rightarrow> None
        )
      }
    | ([],[],t) \<Rightarrow>
      (case t of
        ret r \<Rightarrow>
          (case r of
            Some (t, v) \<Rightarrow>
              (case get_register s v of
                Some v' \<Rightarrow> Some (ctrl_flow s (return_value (Some v')))
              | _     \<Rightarrow> None
              )
          | None \<Rightarrow> Some (ctrl_flow s (return_value None))
          )
      | br_i1 b l1 l2 \<Rightarrow>
          (case get_register s b of
            Some (vi1 b') \<Rightarrow> Some (ctrl_flow s (branch_label (if b' then l1 else l2)))
          | _           \<Rightarrow> None
          )
      | br_label l \<Rightarrow> Some (ctrl_flow s (branch_label l))
      )
    )
  | exec_blocks pre cur lbs \<Rightarrow>
      do {
        block \<leftarrow> map_of lbs cur;
        s' \<leftarrow> exec (exec_block pre block) s;
        (case s' of
          ctrl_flow s' br \<Rightarrow>
            (case br of
              branch_label l \<Rightarrow> exec (exec_blocks (Some cur) l lbs) s'
            | return_value v \<Rightarrow> Some (func_ret s' v)
            )
        | _ \<Rightarrow> None
        )
      }
  | exec_func name pars \<Rightarrow>
    do { \<comment> \<open>store initial state that needs to be restored (stack, local registers) \<close>
      (l, s') \<leftarrow> Some (local_registers s);
      stack_len \<leftarrow> Some (stack_size s);
      f  \<leftarrow> map_of (funcs program) name;
      fb \<leftarrow>
        (case llvm_function.blocks f of
          ((fb,_)#_) \<Rightarrow> Some fb
        | _ \<Rightarrow> None
        );
      ret \<leftarrow> exec (exec_blocks None fb (llvm_function.blocks f)) s';
      (s'', v) \<leftarrow>
        (case ret of
          func_ret s v \<Rightarrow> Some (s, v)
        | _ \<Rightarrow> None
        );
      Some (func_ret (restore_stack (restore_registers s'' l) stack_len) v)
    }
  )"

end

partial_function (option)
  execute_instruction :: "llvm_instruction \<Rightarrow> state \<Rightarrow> exec_Some option"
where
  "execute_instruction ii is = (case (case ii of
    \<comment> \<open>Allocate new memory value on the stack, and set the specified register to its address\<close>
    alloca name type align              \<Rightarrow> execute_alloca name is
    \<comment> \<open>Read address from pointer and store value in the stack or the heap\<close>
  | store type value pointer align      \<Rightarrow> execute_store value pointer is
    \<comment> \<open>Read address from pointer and load value from either the stack or the heap\<close>
  | load name type pointer align        \<Rightarrow> execute_load name pointer is
    \<comment> \<open>Get values, add according to wrap option (or poison), and store in register\<close>
  | add name wrap type v1 v2            \<Rightarrow> execute_add name wrap v1 v2 is
    \<comment> \<open>Get values, do comparison, and store in register\<close>
  | icmp name same_sign cond type v1 v2 \<Rightarrow> execute_icmp name same_sign cond v1 v2 is
  ) of Some s' \<Rightarrow> Some (state_only s') | _ \<Rightarrow> None)"

partial_function (option)
  execute_block :: "llvm_identifier option \<Rightarrow> llvm_instruction_block \<Rightarrow> state \<Rightarrow> exec_result option"
  where
 "execute_block previous bb bs = (case bb of
    ((phi name type values)#ps, is, t) \<Rightarrow>
    (case execute_phi previous name values bs of
      Some s' \<Rightarrow> execute_block previous (ps, is, t) s'
    | err e \<Rightarrow> None
    )
  | (_, i#is, t) \<Rightarrow>
    (case execute_instruction i bs of
      Some (state_only s') \<Rightarrow> execute_block previous ([],is,t) s'
    | _ \<Rightarrow> None
    )
  | (_, _, br_i1 v l1 l2) \<Rightarrow>
    (case (do {
      val \<leftarrow> get_register bs v;
      label \<leftarrow> (case val of (vi1 b) \<Rightarrow> Some (if b then l1 else l2) | _ \<Rightarrow> err incompatible_types);
      Some (ctrl_flow bs (branch_label label))
    }) of Some x \<Rightarrow> Some x | _ \<Rightarrow> None)
  | (_, _, br_label l) \<Rightarrow>
    Some (ctrl_flow bs (branch_label l))
  | (_, _, ret t v) \<Rightarrow>
    (case get_register bs v of
      Some v' \<Rightarrow> Some (ctrl_flow bs (return_value v'))
    | _ \<Rightarrow> None
    )
  )"

partial_function (tailrec)
  execute_blocks :: "llvm_identifier option \<Rightarrow> llvm_identifier \<Rightarrow> llvm_labeled_blocks \<Rightarrow> state \<Rightarrow> exec_Some option"
where
 "execute_blocks bsp bsl bsb bss =
    (case map_of bsb bsl of
      None \<Rightarrow> err unknown_label
    | Some block \<Rightarrow>
      (case execute_block bsp block bss of
        err e \<Rightarrow> err e
      | Some (ctrl_flow s' br) \<Rightarrow>
        (case br of
          return_value v \<Rightarrow> Some (func_ret s' (Some v))
        | branch_label l \<Rightarrow> execute_blocks (Some bsl) l bsb s'
        )
      | _ \<Rightarrow> err internal_error
      )
    )"

partial_function (tailrec) execute_function :: "llvm_function \<Rightarrow> state \<Rightarrow> (state * llvm_value option) option" where
  "execute_function (func _ ((l,b)#ls)) s = execute_blocks None l ((l,b)#ls) s"
| "execute_function _ s = Some (s, None)"



lemmas [code] = execute_blocks.simps



section "Intro Rules"

lemma [wp_intro]: "wp (execute_alloca name s) Q \<Longrightarrow> wp (execute_instruction (alloca name type align) s) Q"
  by (simp add: execute_instruction.simps)
lemma [wp_intro]: "wp (execute_store value pointer s) Q \<Longrightarrow> wp (execute_instruction (store type value pointer align) s) Q"
  by (simp add: execute_instruction.simps)
lemma [wp_intro]: "wp (execute_load name pointer s) Q \<Longrightarrow> wp (execute_instruction (load name type pointer align) s) Q"
  by (simp add: execute_instruction.simps)
lemma [wp_intro]: "wp (execute_add name wrap v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (add name wrap type v1 v2) s) Q"
  by (simp add: execute_instruction.simps)
lemma [wp_intro]: "wp (execute_icmp name same_sign cond v1 v2 s) Q \<Longrightarrow> wp (execute_instruction (icmp name same_sign cond type v1 v2) s) Q"
  by (simp add: execute_instruction.simps)


lemma block_phi_wp_intro[wp_intro]:
  assumes "wp (execute_phi p name values s) (\<lambda>s'. wp (execute_block p (ps, is, t) s') Q)"
  shows "wp (execute_block p ((phi name type values)#ps, is, t) s) Q"
  apply (subst execute_block.simps)
  using assms
  unfolding wp_gen_def
  by (auto split: option.splits list.splits)

lemma block_instr_wp_intro[wp_intro]:
  assumes "wp (execute_instruction i s) (\<lambda>s'. wp (execute_block p ([], is, t) s') Q)"
  shows "wp (execute_block p ([], i#is, t) s) Q"
  apply (subst execute_block.simps)
  using assms
  unfolding wp_gen_def
  by (auto split: option.splits)

lemma block_ret_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s value = Some v"
  shows "wp (execute_block p ([], [], ret type value) s) (\<lambda>r. r = (s, return_value v))"
  apply (subst execute_block.simps)
  using assms
  unfolding wp_gen_def
  apply (cases s; cases "value")
  by (auto simp: return_def split: option.splits)

lemma block_br_label_wp_intro[THEN consequence, wp_intro]:
  shows "wp (execute_block p ([], [], br_label l) s) (\<lambda>r. r = (s, branch_label l))"
  apply (subst execute_block.simps)
  unfolding wp_gen_def
  by (auto simp: return_def)

lemma block_br_i1_wp_intro[THEN consequence, wp_intro]:
  assumes "register_\<alpha> s value = Some (vi1 b)"
  shows "wp (execute_block p ([], [], br_i1 value l1 l2) s) (\<lambda>r. r = (s, branch_label (if b then l1 else l2)))"
  apply (subst execute_block.simps)
  unfolding wp_gen_def
  using assms
  by (auto simp: return_def split: option.splits)

lemma phi_wp_intro[THEN consequence, wp_intro]:
  assumes "distinct (map fst values)"
  assumes "p = Some p'" "map_of values p' = Some v" "register_\<alpha> s v = Some v'"
  shows "wp (execute_phi p name values s) (\<lambda>s'. register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v') \<and> memory_\<alpha> s' = memory_\<alpha> s)"
  unfolding execute_phi_def
  apply simp
  using assms
  apply (intro wp_intro; auto) done

end