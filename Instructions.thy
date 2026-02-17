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

definition execute_alloca :: "state \<Rightarrow> llvm_register_name \<Rightarrow> state result" where
  "execute_alloca s name = do {
      (s', a) \<leftarrow> return (allocate_stack s);
      return (set_register s' name (addr a))
    }"

lemma wp_execute_alloca_intro[THEN consequence, wp_intro]:
  "wp (execute_alloca s name) (\<lambda>s'. \<exists>a. (register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (addr a)) \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some None) \<and> memory_\<alpha> s a = None))"
  unfolding execute_alloca_def
  by (intro wp_intro; auto)


fun get_address_from_pointer :: "state \<Rightarrow> llvm_pointer \<Rightarrow> llvm_address result" where
  "get_address_from_pointer s p = do {
    a \<leftarrow> get_register s p;
    (case a of (addr a') \<Rightarrow> ok a' | _ \<Rightarrow> err not_an_address)
  }"

definition execute_store :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "execute_store s v p = do {
    address \<leftarrow> get_address_from_pointer s p;
    value \<leftarrow> get_register s v;
    set_memory s address value
  }"

lemma wp_execute_store_intro[THEN consequence, wp_intro]:
  assumes "\<exists>a. register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a \<noteq> None"
  assumes "register_\<alpha> s value \<noteq> None"
  shows "wp (execute_store s value pointer) (\<lambda>s'. \<exists>a v. register_\<alpha> s pointer = Some (addr a) \<and> register_\<alpha> s value = Some v \<and> memory_\<alpha> s' = (memory_\<alpha> s)(a := Some (Some v)) \<and> register_\<alpha> s = register_\<alpha> s')"
  unfolding execute_store_def
  using assms
  apply simp
  by (intro wp_intro; auto)


definition execute_load :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_pointer \<Rightarrow> state result" where
  "execute_load s n p = do {
    a \<leftarrow> get_address_from_pointer s p;
    v \<leftarrow> get_memory s a;
    return (set_register s n v)
  }"

lemma wp_execute_load_intro[THEN consequence, wp_intro]:
  assumes "\<exists>a v. register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a = Some (Some v)"
  shows "wp (execute_load s name pointer) (\<lambda>s'. \<exists>a v. register_\<alpha> s pointer = Some (addr a) \<and> memory_\<alpha> s a = Some (Some v) \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some v))"
  unfolding execute_load_def
  using assms
  apply simp
  by (intro wp_intro; auto)

thm wp_execute_load_intro[THEN consequence]


section "Add instruction"
(* TODO: support pointers *)

fun unsigned_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "unsigned_overflow32 a b = ((a + b) < a)"

fun signed_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "signed_overflow32 a b = (sint a + sint b \<noteq> sint (a + b))"

fun unsigned_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "unsigned_overflow64 a b = ((a + b) < a)"

fun signed_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "signed_overflow64 a b = (sint a + sint b \<noteq> sint (a + b))"

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

fun add_values :: "llvm_add_wrap \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "add_values wrap (vi32 a) (vi32 b) = (if add_no_poison32 wrap a b then ok (vi32 (a+b)) else ok poison)"
| "add_values wrap (vi64 a) (vi64 b) = (if add_no_poison64 wrap a b then ok (vi64 (a+b)) else ok poison)"
| "add_values _ poison (vi32 _) = ok poison"
| "add_values _ (vi32 _) poison = ok poison"
| "add_values _ poison (vi64 _) = ok poison"
| "add_values _ (vi64 _) poison = ok poison"
| "add_values _ poison poison = ok poison"
| "add_values _ _ _ = err incompatible_types"


definition execute_add :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_add_wrap \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state result" where
  "execute_add s name wrap v1 v2 = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> add_values wrap v1' v2';
    return (set_register s name res)
  }"


lemma wp_execute_add_32_intro[THEN consequence, wp_intro]:
  assumes "\<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> add_no_poison32 wrap v1' v2'"
  shows "wp (execute_add s name wrap v1 v2) (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi32 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_intro; simp; auto; intro wp_intro; simp)

lemma wp_execute_add_64_intro[THEN consequence, wp_intro]:
  assumes "\<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> add_no_poison64 wrap v1' v2'"
  shows "wp (execute_add s name wrap v1 v2) (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (vi64 (v1' + v2'))))"
  using assms
  unfolding execute_add_def
  by (intro wp_intro; simp; auto; intro wp_intro; simp)



section "Compare instruction"

fun compare_values_32 :: "llvm_compare_condition \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> llvm_value" where
  "compare_values_32 comp_eq a b = vi1 (a = b)"
| "compare_values_32 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_32 comp_ugt a b = vi1 ((uint a) > (uint b))"
| "compare_values_32 comp_uge a b = vi1 ((uint a) \<ge> (uint b))"
| "compare_values_32 comp_ult a b = vi1 ((uint a) < (uint b))"
| "compare_values_32 comp_ule a b = vi1 ((uint a) \<le> (uint b))"
| "compare_values_32 comp_sgt a b = vi1 ((sint a) > (sint b))"
| "compare_values_32 comp_sge a b = vi1 ((sint a) \<ge> (sint b))"
| "compare_values_32 comp_slt a b = vi1 ((sint a) < (sint b))"
| "compare_values_32 comp_sle a b = vi1 ((sint a) \<le> (sint b))"

fun compare_values_64 :: "llvm_compare_condition \<Rightarrow> word64 \<Rightarrow> word64 \<Rightarrow> llvm_value" where
  "compare_values_64 comp_eq a b = vi1 (a = b)"
| "compare_values_64 comp_ne a b = vi1 (a \<noteq> b)"
| "compare_values_64 comp_ugt a b = vi1 ((uint a) > (uint b))"
| "compare_values_64 comp_uge a b = vi1 ((uint a) \<ge> (uint b))"
| "compare_values_64 comp_ult a b = vi1 ((uint a) < (uint b))"
| "compare_values_64 comp_ule a b = vi1 ((uint a) \<le> (uint b))"
| "compare_values_64 comp_sgt a b = vi1 ((sint a) > (sint b))"
| "compare_values_64 comp_sge a b = vi1 ((sint a) \<ge> (sint b))"
| "compare_values_64 comp_slt a b = vi1 ((sint a) < (sint b))"
| "compare_values_64 comp_sle a b = vi1 ((sint a) \<le> (sint b))"

(* TODO: support pointers *)
fun compare_values :: "llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values c (vi32 a) (vi32 b) = ok (compare_values_32 c a b)"
| "compare_values c (vi64 a) (vi64 b) = ok (compare_values_64 c a b)"
| "compare_values _ _ _ = err incompatible_types"

fun same_signs :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "same_signs a b = ((a \<ge> 0 \<and> b \<ge> 0) \<or> (a < 0 \<and> b < 0))"

fun compare_values_sign :: "llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value \<Rightarrow> llvm_value \<Rightarrow> llvm_value result" where
  "compare_values_sign False c a b = compare_values c a b"
| "compare_values_sign True c (vi32 a) (vi32 b) = (if same_signs (sint a) (sint b) then compare_values c (vi32 a) (vi32 b) else ok poison)"
| "compare_values_sign True c (vi64 a) (vi64 b) = (if same_signs (sint a) (sint b) then compare_values c (vi64 a) (vi64 b) else ok poison)"
| "compare_values_sign True c _ _ = err incompatible_types"

definition execute_icmp :: "state \<Rightarrow> llvm_register_name \<Rightarrow> llvm_same_sign \<Rightarrow> llvm_compare_condition \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value_ref \<Rightarrow> state result" where
  "execute_icmp s name same_sign cond v1 v2 = do {
    v1' \<leftarrow> get_register s v1;
    v2' \<leftarrow> get_register s v2;
    res \<leftarrow> compare_values_sign same_sign cond v1' v2';
    return (set_register s name res)
  }"

lemma wp_execute_icmp_32_intro[THEN consequence, wp_intro]:
  assumes "\<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> (if ss then same_signs (sint v1') (sint v2') else True)"
  shows "wp (execute_icmp s name ss cond v1 v2) (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi32 v1') \<and> register_\<alpha> s v2 = Some (vi32 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_32 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_intro; auto; intro wp_intro; auto)

lemma wp_execute_icmp_64_intro[THEN consequence, wp_intro]:
  assumes "\<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> (if ss then same_signs (sint v1') (sint v2') else True)"
  shows "wp (execute_icmp s name ss cond v1 v2) (\<lambda>s'. \<exists>v1' v2'. register_\<alpha> s v1 = Some (vi64 v1') \<and> register_\<alpha> s v2 = Some (vi64 v2') \<and> memory_\<alpha> s' = memory_\<alpha> s \<and> register_\<alpha> s' = (register_\<alpha> s)(reg name := Some (compare_values_64 cond v1' v2')))"
  using assms
  unfolding execute_icmp_def
  by (cases ss; intro wp_intro; auto; intro wp_intro; auto)



section "Instruction wrapper"

fun execute_instruction :: "state \<Rightarrow> llvm_instruction \<Rightarrow> state result" where
  (* Allocate new memory value on the stack, and set the specified SSA name to its address. *)
  "execute_instruction s (alloca name type align) = execute_alloca s name"
  (* Read address from pointer and store value in the stack or the heap. *)
| "execute_instruction s (store type value pointer align) = execute_store s value pointer"
  (* Read address from pointer and load value from either the stack or the heap. *)
| "execute_instruction s (load name type pointer align) = execute_load s name pointer"
  (* Get values, add according to wrap option (or poison), and store at SSA name. *)
| "execute_instruction s (add name wrap type v1 v2) = execute_add s name wrap v1 v2"
  (* Get values, do comparison, and store at SSA name. *)
| "execute_instruction s (icmp name same_sign cond type v1 v2) = execute_icmp s name same_sign cond v1 v2"

lemma [wp_intro]: "wp (execute_alloca s name) Q \<Longrightarrow> wp (execute_instruction s (alloca name type align)) Q"
  by simp
lemma [wp_intro]: "wp (execute_store s value pointer) Q \<Longrightarrow> wp (execute_instruction s (store type value pointer align)) Q"
  by simp
lemma [wp_intro]: "wp (execute_load s name pointer) Q \<Longrightarrow> wp (execute_instruction s (load name type pointer align)) Q"
  by simp
lemma [wp_intro]: "wp (execute_add s name wrap v1 v2) Q \<Longrightarrow> wp (execute_instruction s (add name wrap type v1 v2)) Q"
  by simp
lemma [wp_intro]: "wp (execute_icmp s name same_sign cond v1 v2) Q \<Longrightarrow> wp (execute_instruction s (icmp name same_sign cond type v1 v2)) Q"
  by simp

end