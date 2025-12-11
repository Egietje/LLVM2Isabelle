theory MemoryModel
  imports Result
begin

section "Definitions"


subsection "Types"

datatype 'a memory_value = mem_unset | mem_val 'a | mem_freed

type_synonym 'a memory_model = "'a memory_value list"
type_synonym memory_model_address = nat


subsection "Operations"

definition allocate_memory :: "'a memory_model \<Rightarrow> ('a memory_model * memory_model_address)" where
  "allocate_memory m = (m@[mem_unset], length m)"

definition valid_memory_address :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_memory_address m a = (a < length m \<and> m!a \<noteq> mem_freed)"

definition get_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a result" where
  "get_memory m a = do {
    assert unallocated_address (valid_memory_address m a);
    (case (m!a) of
      mem_unset \<Rightarrow> err uninitialized_address
    | mem_val v \<Rightarrow> ok v
    | mem_freed \<Rightarrow> err unallocated_address)
  }"

definition set_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a \<Rightarrow> 'a memory_model result" where
  "set_memory m a v = do {
    assert unallocated_address (valid_memory_address m a);
    return (m[a:=(mem_val v)])
  }"

definition free_memory :: "'a memory_model \<Rightarrow> memory_model_address \<Rightarrow> 'a memory_model result" where
  "free_memory m a = do {
    assert unallocated_address (valid_memory_address m a);
    return (m[a:=mem_freed])
  }"

definition empty_memory_model :: "'a memory_model" where
  "empty_memory_model = []"



section "Lemmas"



subsection "Empty"

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

lemma memory_allocate_get_uninitialized: "allocate_memory m = (m', i) \<Longrightarrow> get_memory m' i = err uninitialized_address"
  unfolding allocate_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


lemma memory_allocate_validity: "(m', i) = allocate_memory m \<Longrightarrow> \<not>valid_memory_address m i \<and> valid_memory_address m' i"
  unfolding allocate_memory_def valid_memory_address_def
  by simp

lemma memory_allocate_independent_valid: "allocate_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a \<longleftrightarrow> valid_memory_address m' a"
  unfolding valid_memory_address_def allocate_memory_def
  using nth_append_left
  by fastforce

lemma memory_allocate_independent_get: "allocate_memory m = (m', a') \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = get_memory m' a" 
  unfolding valid_memory_address_def allocate_memory_def get_memory_def
  using nth_append_left
  by (cases "a < a'"; fastforce)


subsection "Set"

lemma memory_set_invalid: "\<not>valid_memory_address m a \<Longrightarrow> set_memory m a v = err unallocated_address"
  unfolding set_memory_def
  by simp

lemma memory_set_ok_valid: "set_memory m a v = ok m' \<Longrightarrow> valid_memory_address m' a \<and> valid_memory_address m a"
  unfolding set_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_ok_valid_wp: "wp_ok (set_memory m a v) (\<lambda> m'. valid_memory_address m' a \<and> valid_memory_address m a)"
  unfolding set_memory_def
  apply simp
  unfolding valid_memory_address_def
  by simp

lemma memory_set_override: "set_memory m i v = ok m' \<Longrightarrow> set_memory m' i v' = ok m'' \<Longrightarrow> get_memory m'' i = ok v'"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_override_wp:
  "wp_ok (do {
    m' \<leftarrow> set_memory m a v1;
    m'' \<leftarrow> set_memory m' a v2;
    get_memory m'' a}) (\<lambda>v. v = v2)"
  apply simp
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


lemma memory_set_identity: "get_memory m i = ok v \<Longrightarrow> set_memory m i v = ok m' \<Longrightarrow> m = m'"
  unfolding get_memory_def set_memory_def
  apply simp
  unfolding valid_memory_address_def
  apply (cases "m!i"; simp)
  using list_update_id
  by metis

lemma memory_set_identity_wp: "wp_ok (do { v \<leftarrow> get_memory m a; set_memory m a v }) ((=) m)"
  apply simp
  unfolding get_memory_def set_memory_def
  apply simp
  unfolding valid_memory_address_def
  using list_update_id
  by (cases "m!a"; auto; metis)


lemma memory_set_get: "set_memory m i v = ok m' \<Longrightarrow> get_memory m' i = ok v"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_get_wp: "wp_ok (do {m' \<leftarrow> set_memory m a v; get_memory m' a}) ((=) v)"
  apply simp
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


lemma memory_set_independent_get: "set_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = get_memory m' a"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_set_independent_get_wp: "a \<noteq> a' \<Longrightarrow> wp_ok (set_memory m a' v) (\<lambda>m'. get_memory m' a = get_memory m a)"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


lemma memory_set_independent_valid: "set_memory m a' v = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a = valid_memory_address m' a"
  unfolding set_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto


subsection "Get"

lemma memory_get_ok_valid: "get_memory m a = ok v \<Longrightarrow> valid_memory_address m a"
  unfolding get_memory_def
  by simp


subsection "Free"

lemma memory_free_get: "free_memory m a = ok m' \<Longrightarrow> get_memory m' a = err unallocated_address"
  unfolding free_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_free_set: "free_memory m a = ok m' \<Longrightarrow> set_memory m' a v = err unallocated_address"
  unfolding free_memory_def set_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_free_invalid: "free_memory m a = ok m' \<Longrightarrow> \<not>valid_memory_address m' a \<and> valid_memory_address m a"
  unfolding free_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_free_independent_valid: "free_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> valid_memory_address m a \<longleftrightarrow> valid_memory_address m' a"
  unfolding free_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

lemma memory_free_independent_get: "free_memory m a' = ok m' \<Longrightarrow> a \<noteq> a' \<Longrightarrow> get_memory m a = ok v \<longleftrightarrow> get_memory m' a = ok v"
  unfolding free_memory_def get_memory_def
  apply simp
  unfolding valid_memory_address_def
  by auto

end