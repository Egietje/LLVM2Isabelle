theory Semantics
  imports Structure "HOL-Library.Mapping"
begin

type_synonym register_state = "(llvm_identifier, llvm_value) mapping"

datatype memory_entry = mem_unset | mem_value llvm_value | mem_freed
type_synonym mem = "llvm_address \<rightharpoonup> memory_entry"

definition disjoint :: "mem \<Rightarrow> mem \<Rightarrow> bool" where
  "disjoint h1 h2 \<equiv> dom h1 \<inter> dom h2 = {}"

definition union :: "mem \<Rightarrow> mem \<Rightarrow> mem" ("_ \<union> _" 50) where
  "(h1 \<union> h2) \<equiv> h1 ++ h2"

definition separating_conjunction :: "(mem \<Rightarrow> bool) \<Rightarrow> (mem \<Rightarrow> bool) \<Rightarrow> (mem \<Rightarrow> bool)" ("_ * _" 50) where
  "(A * B) h \<equiv> (\<exists>h1 h2. disjoint h1 h2 \<and> h = union h1 h2 \<and> A h1 \<and> B h2)"

definition valid :: "llvm_address \<Rightarrow> mem \<Rightarrow> bool" where
  "valid l h \<equiv> dom h = {l} \<and> h \<noteq> [l \<mapsto> mem_freed]"

definition contains :: "llvm_address \<Rightarrow> llvm_value \<Rightarrow> (mem \<Rightarrow> bool)" ("_ \<mapsto> _" 50) where
  "(l \<mapsto> v) h \<equiv> h = [l \<mapsto> mem_value v]"

definition empty :: "mem \<Rightarrow> bool" where
  "empty h \<equiv> h = Map.empty"

definition prop_empty :: "bool \<Rightarrow> mem \<Rightarrow> bool" where
  "prop_empty P h \<equiv> empty h \<and> P"
definition separating_implication :: "(mem \<Rightarrow> bool) \<Rightarrow> (mem \<Rightarrow> bool) \<Rightarrow> (mem \<Rightarrow> bool)" where
  "separating_implication A B h \<equiv> (\<forall>h'. (disjoint h h' \<and> A h') \<longrightarrow> B (union h h'))"

datatype state = state register_state mem



definition set_register :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> state" where
  "set_register i v s = (case s of state r m \<Rightarrow> state (Mapping.update i v r) m)"

definition get_register :: "llvm_identifier \<Rightarrow> state \<Rightarrow> llvm_value option" where
  "get_register i s = (case s of state r m \<Rightarrow> Mapping.lookup r i)"



fun addr_index :: "llvm_address \<Rightarrow> nat" where
  "addr_index (saddr n) = n"
| "addr_index (haddr n) = n"

fun is_saddr where
  "is_saddr (saddr _) = True"
| "is_saddr _ = False"

fun is_haddr where
  "is_haddr (haddr _) = True"
| "is_haddr _ = False"

definition max_address :: "llvm_address set \<Rightarrow> nat" where
  "max_address d =
     (if d = {} then 0 else Max (addr_index ` d))"

definition fresh_stack_address :: "mem \<Rightarrow> llvm_address" where
  "fresh_stack_address h =
     (let saddrs = {a \<in> dom h. is_saddr a}
      in saddr (Suc (max_address saddrs)))"

definition fresh_heap_address :: "mem \<Rightarrow> llvm_address" where
  "fresh_heap_address h =
     (let haddrs = {a \<in> dom h. is_haddr a}
      in haddr (Suc (max_address haddrs)))"


lemma mem_helper:
  assumes "finite (dom h)"
  and "haddr ad = fresh_heap_address h"
  and "is_haddr x"
  and "h x = Some y"
  shows "addr_index x < ad"
proof (-)
  have "ad = Suc (if \<forall>x. x \<in> dom h \<longrightarrow> \<not> is_haddr x then 0 else Max (addr_index ` {a \<in> dom h. is_haddr a}))"
    using assms
    unfolding fresh_heap_address_def max_address_def
    by simp

  moreover

  obtain x' where xdef: "haddr x' = x"
    using assms
    by (cases x; simp)

  then have "x' \<in> addr_index ` {a \<in> dom h. is_haddr a}"
    using assms
    by force

  then have "x' \<le> Max (addr_index ` {a \<in> dom h. is_haddr a})"
    using assms xdef by simp

  then have "addr_index x \<le> (if \<forall>x. x \<in> dom h \<longrightarrow> \<not> is_haddr x then 0 else Max (addr_index ` {a \<in> dom h. is_haddr a}))"
    using assms xdef by auto

  ultimately

  show ?thesis by simp
qed

lemma stack_helper:
  assumes "finite (dom h)"
  and "saddr ad = fresh_stack_address h"
  and "is_saddr x"
  and "h x = Some y"
  shows "addr_index x < ad"
proof (-)
  have "ad = Suc (if \<forall>x. x \<in> dom h \<longrightarrow> \<not> is_saddr x then 0 else Max (addr_index ` {a \<in> dom h. is_saddr a}))"
    using assms
    unfolding fresh_stack_address_def max_address_def
    by simp

  moreover

  obtain x' where xdef: "saddr x' = x"
    using assms
    by (cases x; simp)

  then have "x' \<in> addr_index ` {a \<in> dom h. is_saddr a}"
    using assms
    by force

  then have "x' \<le> Max (addr_index ` {a \<in> dom h. is_saddr a})"
    using assms xdef by simp

  then have "addr_index x \<le> (if \<forall>x. x \<in> dom h \<longrightarrow> \<not> is_saddr x then 0 else Max (addr_index ` {a \<in> dom h. is_saddr a}))"
    using assms xdef by auto

  ultimately

  show ?thesis by simp
qed


lemma fresh_heap_not_in_dom: "finite (dom h) \<Longrightarrow> fresh_heap_address h \<notin> dom h"
  using mem_helper unfolding fresh_heap_address_def by force

lemma fresh_stack_not_in_dom: "finite (dom h) \<Longrightarrow> fresh_stack_address h \<notin> dom h"
  using stack_helper unfolding fresh_stack_address_def by force


definition allocate_stack :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_stack s \<equiv> (case s of state r m \<Rightarrow> (let a = fresh_stack_address m in (state r (m(a \<mapsto> mem_unset)), a)))"

definition allocate_heap :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_heap s \<equiv> (case s of state r m \<Rightarrow> (let a = fresh_heap_address m in (state r (m(a \<mapsto> mem_unset)), a)))"


definition "get_memory a s \<equiv> (case s of state r m \<Rightarrow> (case m a of Some (mem_value v) \<Rightarrow> Some v | _ \<Rightarrow> None))"

definition "set_memory a v s \<equiv> (case s of state r m \<Rightarrow> (case m a of None \<Rightarrow> None | Some mem_freed \<Rightarrow> None | _ \<Rightarrow> Some (state r (m(a := Some (mem_value v))))))"

lemma "((a \<mapsto> v) * B) m \<Longrightarrow> get_memory a (state r m) = Some v"
  unfolding get_memory_def contains_def separating_conjunction_def union_def disjoint_def
  by (cases "m a"; auto)

lemma "(((a \<mapsto> v) * (b \<mapsto> x)) * (c \<mapsto> y)) m \<Longrightarrow> get_memory a (state r m) = Some v"
  unfolding get_memory_def contains_def separating_conjunction_def union_def disjoint_def
  by force


lemma "((valid a) * B) m \<Longrightarrow> set_memory a v (state r m) \<noteq> None"
  unfolding set_memory_def separating_conjunction_def union_def disjoint_def valid_def apply (cases "m a"; auto)
  subgoal for mv apply (cases mv) apply auto by fastforce
  done


lemma "((valid a) * B) m \<Longrightarrow> set_memory a v (state r m) = Some (state r' m') \<Longrightarrow> r' = r \<and> ((valid a) * B) m' \<and> ((a \<mapsto> v) * B) m'"
  unfolding set_memory_def contains_def separating_conjunction_def valid_def disjoint_def union_def apply (intro conjI)
    apply (cases "m a") apply simp apply simp subgoal for mv by (cases mv; simp)
    apply (cases "m a") apply simp apply simp subgoal for mv apply (cases mv; simp)
    apply (metis (no_types, lifting) dom_eq_singleton_conv fun_upd_upd insert_disjoint(2) map_add_upd_left map_upd_eqD1
        memory_entry.distinct(6))
    by (smt (verit) dom_empty dom_fun_upd fun_upd_None_if_notin_dom fun_upd_upd insert_disjoint(2) map_add_upd
        map_add_upd_left map_upd_eqD1 memory_entry.distinct(6))
    apply (cases "m a") apply simp apply simp subgoal for mv apply (cases mv; simp)
     apply (metis dom_eq_singleton_conv fun_upd_upd insert_disjoint(2) map_add_upd_left)
    apply auto
    by (metis domIff dom_eq_singleton_conv fun_upd_upd map_add_upd_left)
  done



lemma allocate_heap_sep:
  assumes "finite (dom h)"
  assumes "(state r' h', a) = allocate_heap (state r h)"
  shows "((\<lambda>h1. h1 = h) * (\<lambda>h2. h2 = [a \<mapsto> mem_unset])) h'"
  unfolding separating_conjunction_def using assms unfolding allocate_stack_def apply auto
  apply (metis (mono_tags, lifting) Int_insert_right_if0 allocate_heap_def disjoint_def dom_empty dom_fun_upd
      fresh_heap_not_in_dom inf_bot_right option.distinct(1) snd_conv state.case)
  by (metis (mono_tags, lifting) allocate_heap_def map_add_empty map_add_upd old.prod.inject state.case state.inject
      union_def)

end