theory MemoryModel
  imports Result
begin

section "Definitions"


subsection "Types"

datatype 'a memory_value = mem_unset | mem_val 'a | mem_freed
type_synonym 'a memory_model = "'a memory_value list"
type_synonym memory_model_address = nat


subsection "Operations"

fun assert where "assert e True = return ()" | "assert e False = err e"
lemma assert_inv_simps[simp]: 
  "assert e P = return x \<longleftrightarrow> P" 
  "assert e P = err e' \<longleftrightarrow> \<not>P \<and> e'=e"
  apply (cases P; simp add: return_def)
  apply (cases P; auto simp add: return_def)
  done


definition allocate_memory :: "'a memory_model \<Rightarrow> ('a memory_model * memory_model_address)" where
  "allocate_memory m = (m@[mem_unset], length m)"

definition valid_memory_address :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_memory_address m a = (a < length m \<and> m!a \<noteq> mem_freed)"

definition get_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a result" where
  "get_memory m a =
    (if valid_memory_address m a then
      (case (m!a) of
        mem_unset \<Rightarrow> err uninitialized_address
      | mem_val v \<Rightarrow> ok v
      | mem_freed \<Rightarrow> err unallocated_address
    ) else err unallocated_address)"

lemma return_bind[simp]: "do {x\<leftarrow>return v; f x} = f v"
  unfolding bind_def return_def by auto

lemma err_bind[simp]: "do { x\<leftarrow>err e; m x } = err e"
  unfolding bind_def by auto


lemma "get_memory m a = do {
  assert unallocated_address (valid_memory_address m a);
  (case (m!a) of
    mem_unset \<Rightarrow> err uninitialized_address
  | mem_val v \<Rightarrow> ok v
  | mem_freed \<Rightarrow> err unallocated_address)
}"
  unfolding get_memory_def
  by (auto )



definition set_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a \<Rightarrow> 'a memory_model result" where
  "set_memory m a v = (if valid_memory_address m a then ok (m[a:=(mem_val v)]) else err unallocated_address)"

definition free_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a memory_model result" where
  "free_memory m a = (if valid_memory_address m a then ok (m[a:=mem_freed]) else err unallocated_address)"

definition empty_memory_model :: "'a memory_model" where
  "empty_memory_model = []"



section "Lemmas"


subsection "Empty memory"

lemma memory_empty_get: "get_memory empty_memory_model a = err unallocated_address"
  unfolding empty_memory_model_def get_memory_def valid_memory_address_def
  by simp

lemma memory_empty_invalid: "\<not>valid_memory_address empty_memory_model a"
  unfolding empty_memory_model_def valid_memory_address_def
  by simp

lemma memory_empty_set: "set_memory empty_memory_model a v = err unallocated_address"
  unfolding empty_memory_model_def set_memory_def valid_memory_address_def
  by simp


subsection "Allocate"

lemma memory_allocate_get_uninitialized: "allocate_memory m = (m', i) \<longrightarrow> get_memory m' i = err uninitialized_address"
  unfolding allocate_memory_def get_memory_def valid_memory_address_def 
  by auto

lemma memory_allocate_validity: "(m', i) = allocate_memory m \<longrightarrow> \<not>valid_memory_address m i \<and> valid_memory_address m' i"
  unfolding allocate_memory_def valid_memory_address_def
  by simp

(* Removed due to free *)
(*lemma memory_valid_suc: "valid_memory_address s (Suc i) \<longrightarrow> valid_memory_address s i"
  using valid_memory_address_def
  by simp*)

lemma memory_set_unallocated: "\<not>valid_memory_address m i \<longrightarrow> set_memory m i v = err unallocated_address"
  unfolding set_memory_def
  by simp

lemma memory_set_ok_valid: "set_memory m i v = ok m' \<longrightarrow> valid_memory_address m' i \<and> valid_memory_address m i"
  unfolding set_memory_def valid_memory_address_def
  by auto

lemma memory_get_ok_valid: "get_memory m a = ok v \<longrightarrow> valid_memory_address m a"
  unfolding get_memory_def valid_memory_address_def
  by simp

(* GET (PUT X) = X *)
lemma memory_set_get: "set_memory m i v = ok m' \<longrightarrow> get_memory m' i = ok v"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (PUT X) Y = Y*)
lemma memory_set_set_get: "set_memory m i v = ok m' \<longrightarrow> set_memory m' i v' = ok m'' \<longrightarrow> get_memory m'' i = ok v'"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (GET I) = ID*)
lemma memory_get_set_id: "get_memory m i = ok v \<longrightarrow> set_memory m i v = ok m' \<longrightarrow> m = m'"
  unfolding set_memory_def get_memory_def
  using list_update_id memory_value.exhaust
  by (metis memory_value.simps(10,8,9) result.distinct(1) result.inject(1))

(*GET a1, PUT a2, GET a1*)
lemma memory_set_independent: "a1 \<noteq> a2 \<longrightarrow> get_memory m a1 = ok v1 \<longrightarrow> set_memory m a2 v2 = ok m' \<longrightarrow> get_memory m' a1 = ok v1"
  unfolding get_memory_def set_memory_def valid_memory_address_def
  by auto

(*VALID a1 \<rightarrow> ALLOC \<rightarrow> VALID a1*)
lemma memory_valid_alloc_valid: "valid_memory_address m a \<longrightarrow> allocate_memory m = (m', a') \<longrightarrow> valid_memory_address m' a"
  unfolding valid_memory_address_def allocate_memory_def
  using nth_append_left
  by fastforce

(*GET a1 = (ALLOC, GET a1)*)
lemma memory_alloc_get_eq: "get_memory m a = ok v \<longrightarrow> allocate_memory m = (m', a') \<longrightarrow> get_memory m' a = ok v"
  using nth_append_left memory_get_ok_valid
  unfolding get_memory_def allocate_memory_def valid_memory_address_def
  by force


lemma memory_free_get: "free_memory m a = ok m' \<Longrightarrow> get_memory m' a = err unallocated_address"
  unfolding get_memory_def free_memory_def valid_memory_address_def
  by (auto split: if_splits)

lemma memory_free_set: "free_memory m a = ok m' \<longrightarrow> set_memory m' a v = err unallocated_address"
  unfolding set_memory_def free_memory_def valid_memory_address_def
  by auto

lemma memory_free_invalid: "free_memory m a = ok m' \<longrightarrow> \<not>valid_memory_address m' a \<and> valid_memory_address m a"
  unfolding free_memory_def valid_memory_address_def
  by auto

lemma memory_free_independent_valid: "valid_memory_address m a \<longrightarrow> free_memory m a' = ok m' \<longrightarrow> a \<noteq> a' \<longrightarrow> valid_memory_address m' a"
  unfolding get_memory_def free_memory_def valid_memory_address_def
  by auto

lemma "free_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m' a \<longleftrightarrow> valid_memory_address m a"
  unfolding get_memory_def free_memory_def valid_memory_address_def
  by (auto split: if_splits)


lemma memory_free_independent_get: "get_memory m a = ok v \<longrightarrow> free_memory m a' = ok m' \<longrightarrow> a \<noteq> a' \<longrightarrow> get_memory m' a = ok v"
  unfolding free_memory_def get_memory_def valid_memory_address_def
  using length_list_update nth_list_update result.distinct(1) result.inject(1)
  by metis


end