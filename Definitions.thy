theory Definitions
  imports "Word_Lib/Word_Names" "HOL-Library.Mapping" "Result"
begin

section "LLVM AST"


subsection "Types and values"

datatype llvm_type = i1 | i32 | i64 | addr_type

type_synonym memory_model_address = nat
datatype llvm_address = saddr memory_model_address | haddr memory_model_address | gaddr memory_model_address

datatype llvm_value = vi1 bool | vi32 word32 | vi64 word64 | addr llvm_address | poison

datatype llvm_identifier = is_lid: lid string | gid string



datatype llvm_value_ref = reg llvm_identifier | val llvm_value

(* Should only have a memory address or memory address... *)
type_synonym llvm_pointer = llvm_value_ref


subsection "Instructions"

type_synonym llvm_align = int

datatype llvm_add_wrap = add_nuw | add_nsw | add_nuw_nsw | add_default
datatype llvm_compare_condition = comp_eq | comp_ne
                                | comp_ugt | comp_uge | comp_ult | comp_ule
                                | comp_sgt | comp_sge | comp_slt | comp_sle
type_synonym llvm_same_sign = bool

datatype llvm_phi_node = phi llvm_identifier llvm_type "(llvm_identifier * llvm_value_ref) list"


datatype llvm_instruction = alloca llvm_identifier llvm_type "llvm_align option"
                          | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
                          | load llvm_identifier llvm_type llvm_pointer "llvm_align option"
                          | add llvm_identifier llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
                          | icmp llvm_identifier llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
                          | is_call: call "llvm_identifier option" llvm_type llvm_identifier "(llvm_type * llvm_value_ref) list"

datatype llvm_terminator_instruction = ret "(llvm_type * llvm_value_ref) option"
                                     | br_i1 llvm_value_ref llvm_identifier llvm_identifier
                                     | br_label llvm_identifier


subsection "Blocks, functions, programs"

type_synonym llvm_instruction_block = "(llvm_phi_node list * llvm_instruction list * llvm_terminator_instruction)"

type_synonym llvm_labeled_blocks = "(llvm_identifier * llvm_instruction_block) list"

datatype llvm_block_return = return_value "llvm_value option"
                           | branch_label llvm_identifier

datatype llvm_function = func llvm_type (params: "(llvm_identifier * llvm_type) list") (blocks: llvm_labeled_blocks)
hide_const (open) llvm_function.blocks

type_synonym llvm_program = "(llvm_identifier * llvm_function) list"



section "State"


subsection "Definitions"

type_synonym llvm_register_model = "(string, llvm_value) mapping"
type_synonym llvm_global_variable_model = "(string, memory_model_address) mapping"



datatype memory_value = mem_unset | mem_val llvm_value | mem_freed
type_synonym llvm_memory_model = "memory_value list"

definition empty_memory :: "llvm_memory_model" where
  "empty_memory = []"


type_synonym state = "llvm_register_model * llvm_global_variable_model * llvm_memory_model * llvm_memory_model * llvm_memory_model"

definition empty_state :: "state" where
  "empty_state = (Mapping.empty, Mapping.empty, empty_memory, empty_memory, empty_memory)"


subsection "Register operations"

(* Get *)
fun get_register :: "llvm_register_model \<Rightarrow> string \<Rightarrow> llvm_value result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register_name | Some v \<Rightarrow> ok v)"

fun get_global_var :: "llvm_global_variable_model \<Rightarrow> string \<Rightarrow> llvm_value result" where
  "get_global_var r n = (case Mapping.lookup r n of None \<Rightarrow> err unknown_register_name | Some v \<Rightarrow> ok (addr (gaddr v)))"

fun dereference :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value result" where
  "dereference _ (val v) = ok v"
| "dereference (lr,gr,sm,hm,gm) (reg (lid n)) = get_register lr n"
| "dereference (lr,gr,sm,hm,gm) (reg (gid n)) = get_global_var gr n"


(* Set *)
definition set_single_register :: "string \<Rightarrow> llvm_value \<Rightarrow> llvm_register_model \<Rightarrow> llvm_register_model" where
  "set_single_register n v r = Mapping.update n v r"

fun set_register :: "llvm_identifier \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> state result" where
  "set_register (lid n) v (lr,gr,sm,hm,gm) = ok (set_single_register n v lr,gr,sm,hm,gm)"
| "set_register _ _ _ = err global_register_overwrite"

subsection "Memory operations"

(* Allocate *)
definition allocate_single_memory :: "llvm_memory_model \<Rightarrow> (llvm_memory_model * memory_model_address)" where
  "allocate_single_memory m = (m@[mem_unset], length m)"

definition allocate_stack :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_stack s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory sm in ((lr,gr,m,hm,gm), saddr a))"

definition allocate_heap :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_heap s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory hm in ((lr,gr,sm,m,gm), haddr a))"

definition allocate_global :: "state \<Rightarrow> (state * llvm_address)" where
  "allocate_global s = (case s of (lr,gr,sm,hm,gm) \<Rightarrow> let (m, a) = allocate_single_memory gm in ((lr,gr,sm,hm,m), gaddr a))"


(* Address validity *)
definition allocated_single_memory_address :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "allocated_single_memory_address m a = (a < length m)"
definition valid_single_memory_address :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> bool" where
  "valid_single_memory_address m a = (allocated_single_memory_address m a \<and> m!a \<noteq> mem_freed)"

fun allocated_memory_address :: "state \<Rightarrow> llvm_address \<Rightarrow> bool" where
  "allocated_memory_address (lr,gr,sm,hm,gm) (haddr a) = allocated_single_memory_address hm a"
| "allocated_memory_address (lr,gr,sm,hm,gm) (saddr a) = allocated_single_memory_address sm a"
| "allocated_memory_address (lr,gr,sm,hm,gm) (gaddr a) = allocated_single_memory_address gm a"

fun valid_memory_address :: "state \<Rightarrow> llvm_address \<Rightarrow> bool" where
  "valid_memory_address (lr,gr,sm,hm,gm) (haddr a) = valid_single_memory_address hm a"
| "valid_memory_address (lr,gr,sm,hm,gm) (saddr a) = valid_single_memory_address sm a"
| "valid_memory_address (lr,gr,sm,hm,gm) (gaddr a) = valid_single_memory_address gm a"


(* Get *)
definition get_single_memory :: "llvm_memory_model \<Rightarrow> memory_model_address \<Rightarrow> llvm_value result" where
  "get_single_memory m a = do {
    assert invalid_address (allocated_single_memory_address m a);
    (case (m!a) of
      mem_unset \<Rightarrow> err invalid_address
    | mem_val v \<Rightarrow> ok v
    | mem_freed \<Rightarrow> err invalid_address)
  }"

fun get_memory :: "state \<Rightarrow> llvm_address \<Rightarrow> llvm_value result" where
  "get_memory (lr,gr,sm,hm,gm) (haddr a) = get_single_memory hm a"
| "get_memory (lr,gr,sm,hm,gm) (saddr a) = get_single_memory sm a"
| "get_memory (lr,gr,sm,hm,gm) (gaddr a) = get_single_memory gm a"


(* Set *)
definition set_single_memory :: "memory_model_address \<Rightarrow> llvm_value \<Rightarrow> llvm_memory_model \<Rightarrow> llvm_memory_model result" where
  "set_single_memory a v m = do {
    assert invalid_address (valid_single_memory_address m a);
    return (m[a:=(mem_val v)])
  }"

fun set_memory :: "llvm_address \<Rightarrow> llvm_value \<Rightarrow> state \<Rightarrow> state result" where
  "set_memory (saddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v sm;
    return (lr,gr,m,hm,gm)
  }"
| "set_memory (haddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v hm;
    return (lr,gr,sm,m,gm)
  }"
| "set_memory (gaddr a) v (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> set_single_memory a v gm;
    return (lr,gr,sm,hm,m)
  }"


(* Free *)
definition free_single_memory :: "memory_model_address \<Rightarrow> llvm_memory_model \<Rightarrow> llvm_memory_model result" where
  "free_single_memory a m = do {
    assert invalid_address (valid_single_memory_address m a);
    return (m[a:=mem_freed])
  }"

fun free_memory :: "llvm_address \<Rightarrow> state \<Rightarrow> state result" where
  "free_memory (haddr a) (lr,gr,sm,hm,gm) = do {
    m \<leftarrow> free_single_memory a hm;
    return (lr,gr,sm,m,gm)
  }"
| "free_memory _ _ = err unfreeable_memory"



subsection "Stack Frames"

fun push_frame :: "state \<Rightarrow> state" where "push_frame (lr,gr,sm,hm,gm) = (Mapping.empty,gr,sm,hm,gm)"
fun pop_frame :: "state \<Rightarrow> state \<Rightarrow> state" where "pop_frame (lr,gr,sm,hm,gm) (lr',gr',sm',hm',gm') = (lr,gr',take (length sm) sm',hm',gm')"



section "Abstractions"


subsection "Memory"

definition single_memory_\<alpha> where
  "single_memory_\<alpha> m a \<equiv> if allocated_single_memory_address m a
  then Some (m!a)
  else None"

fun memory_\<alpha> :: "state \<Rightarrow> llvm_address \<Rightarrow> memory_value option" where
  "memory_\<alpha> (lr,gr,sm,hm,gm) (saddr a) = single_memory_\<alpha> sm a"
| "memory_\<alpha> (lr,gr,sm,hm,gm) (haddr a) = single_memory_\<alpha> hm a"
| "memory_\<alpha> (lr,gr,sm,hm,gm) (gaddr a) = single_memory_\<alpha> gm a"


subsection "Register"

fun register_\<alpha> :: "state \<Rightarrow> llvm_value_ref \<Rightarrow> llvm_value option" where
  "register_\<alpha> (lr,gr,sm,hm,gm) (val v) = Some v"
| "register_\<alpha> (lr,gr,sm,hm,gm) (reg (lid n)) = Mapping.lookup lr n"
| "register_\<alpha> (lr,gr,sm,hm,gm) (reg (gid n)) = (case Mapping.lookup gr n of Some a \<Rightarrow> Some (addr (gaddr a)) | None \<Rightarrow> None)"



end