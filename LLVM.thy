theory LLVM
  imports Main HOL.Real "Word_Lib/Word_64" "Word_Lib/Word_32" "HOL-Library.AList_Mapping"
begin

find_consts "('k, 'a) Mapping.mapping \<Rightarrow> 'k \<Rightarrow> 'a option "
value "Mapping.ordered_entries (Mapping.empty :: (nat, nat) mapping)"

section "LLVM AST"

datatype LLVMType = i32 | i64 | f32 | saddr | maddr

type_synonym LLVMRegisterName = string
type_synonym MemoryModelAddress = nat

datatype LLVMAddress = StackAddress MemoryModelAddress | HeapAddress MemoryModelAddress

datatype LLVMValue = vi32 word32 | vi64 word64 | addr LLVMAddress | poison | freed | unset

datatype LLVMValueRef = reg LLVMRegisterName | val LLVMValue

(* Should only have a memory address or memory address... *)
datatype LLVMPointer = ptr LLVMValueRef

datatype LLVMFunctionDefinition = FuncDef string LLVMType

type_synonym LLVMAlign = int

datatype LLVMAddWrapOption = AddNoUnsignedWrap | AddNoSignedWrap | AddNoUnsignedSignedWrap | AddDefaultWrap

datatype LLVMInstruction
  = alloca LLVMRegisterName LLVMType "LLVMAlign option"
  | store LLVMType LLVMValueRef LLVMPointer "LLVMAlign option"
  | load LLVMRegisterName LLVMType LLVMPointer "LLVMAlign option"
  | add LLVMRegisterName LLVMAddWrapOption LLVMType LLVMValueRef LLVMValueRef
  | ret LLVMType LLVMValueRef

type_synonym LLVMInstructions = "LLVMInstruction list"

type_synonym LLVMLabeledInstructions = "string \<Rightarrow> LLVMInstructions option"

datatype LLVMFunction = Func LLVMFunctionDefinition LLVMInstructions LLVMLabeledInstructions

datatype LLVMMetaData = Meta string string string

type_synonym LLVMAttributes = "string list"

datatype LLVM = LLVM LLVMMetaData "LLVMFunction list" LLVMAttributes



section "Execution"


subsection "State"

datatype Error = UnknownRegister | UninitializedRegister | RegisterOverride
  | UnallocatedStackAddress | UnallocatedMemoryAddress
  | UninitializedStackAddress | UninitializedMemoryAddress
  | NotAnAddress | IncompatibleTypes
datatype 'a Result = Ok 'a | Err Error
(*investigate*)
typ "Error+'a"


type_synonym Registers = "(LLVMRegisterName, LLVMValue) mapping"
type_synonym MemoryModel = "LLVMValue list"
type_synonym State = "Registers * MemoryModel * MemoryModel"


(* Register functions and lemmas *)
definition get_register :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue Result" where
  "get_register r n = (case Mapping.lookup r n of None \<Rightarrow> Err UnknownRegister | Some v \<Rightarrow> Ok v)"

definition set_register :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue \<Rightarrow> Registers Result" where
  "set_register r n v = (case Mapping.lookup r n of None \<Rightarrow> Ok (Mapping.update n v r) | Some _ \<Rightarrow> Err RegisterOverride)"


lemma register_set_ok_unknown: "set_register r n v = Ok r' \<longrightarrow> get_register r n = Err UnknownRegister"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_set_get: "set_register r n v = Ok r' \<longrightarrow> get_register r' n = Ok v"
  using register_set_ok_unknown
  unfolding set_register_def get_register_def option.case_eq_if
  by auto

lemma register_get_ok_set: "get_register r n = Ok v \<longrightarrow> set_register r n v' = Err RegisterOverride"
  unfolding set_register_def get_register_def option.case_eq_if
  by simp

lemma register_set_set: "set_register r n v = Ok r' \<longrightarrow> set_register r' n v' = Err RegisterOverride"
  unfolding set_register_def option.case_eq_if
  by auto



definition get_value :: "Registers \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMValue Result" where
  "get_value r v = (case v of (val va) \<Rightarrow> Ok va | (reg re) \<Rightarrow> get_register r re)"


(* Stack functions and lemmas *)
definition allocate_memory :: "MemoryModel \<Rightarrow> (MemoryModel * MemoryModelAddress)" where
  "allocate_memory s = (s@[unset], length s)"

definition valid_memory_address :: "MemoryModel \<Rightarrow> MemoryModelAddress \<Rightarrow> bool" where
  "valid_memory_address s a = (a < length s)"

definition get_memory :: "MemoryModel \<Rightarrow> MemoryModelAddress \<Rightarrow> LLVMValue Result" where
  "get_memory s a = (if valid_memory_address s a then Ok (s!a) else Err UnallocatedStackAddress)"

definition set_memory :: "MemoryModel \<Rightarrow> MemoryModelAddress \<Rightarrow> LLVMValue \<Rightarrow> MemoryModel Result" where
  "set_memory s a v = (if valid_memory_address s a then Ok (s[a:=v]) else Err UnallocatedStackAddress)"


lemma memory_allocate_get_unset: "allocate_memory s = (s', i) \<longrightarrow> get_memory s' i = Ok unset"
  using allocate_memory_def get_memory_def valid_memory_address_def by auto

lemma memory_allocate_invalid: "(s', i) = allocate_memory s \<longrightarrow> \<not>valid_memory_address s i"
  using allocate_memory_def valid_memory_address_def
  by simp

lemma memory_allocate_valid: "(s', i) = allocate_memory s \<longrightarrow> valid_memory_address s' i"
  using allocate_memory_def valid_memory_address_def
  by simp

lemma memory_valid_suc: "valid_memory_address s (Suc i) \<longrightarrow> valid_memory_address s i"
  using valid_memory_address_def
  by simp

lemma memory_set_unallocated: "\<not>valid_memory_address s i \<longrightarrow> set_memory s i v = Err UnallocatedStackAddress"
  unfolding set_memory_def
  by simp

lemma memory_set_ok_valid: "set_memory s i v = Ok s' \<longrightarrow> valid_memory_address s' i \<and> valid_memory_address s i"
  unfolding set_memory_def valid_memory_address_def
  by auto

(* GET (PUT X) = X *)
lemma memory_set_get: "valid_memory_address s i \<longrightarrow> set_memory s i v = Ok s' \<longrightarrow> get_memory s' i = Ok v"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (PUT X) Y = Y*)
lemma memory_set_set_get: "valid_memory_address s i \<longrightarrow> set_memory s i v = Ok s' \<longrightarrow> set_memory s' i v' = Ok s'' \<longrightarrow> get_memory s'' i = Ok v'"
  unfolding valid_memory_address_def set_memory_def get_memory_def
  by auto

(*PUT (GET I) = ID*)
lemma memory_get_set_id: "valid_memory_address s i \<longrightarrow> get_memory s i = Ok v \<longrightarrow> set_memory s i v = Ok s' \<longrightarrow> s = s'"
  unfolding set_memory_def get_memory_def
  by auto

(*GET a1, PUT a2, GET a1*)
lemma memory_set_independent: "valid_memory_address s a1 \<longrightarrow> valid_memory_address s a2 \<longrightarrow> a1 \<noteq> a2 \<longrightarrow> get_memory s a1 = Ok v1 \<longrightarrow> set_memory s a2 v2 = Ok s' \<longrightarrow> get_memory s' a1 = Ok v1"
  unfolding get_memory_def set_memory_def valid_memory_address_def
  by auto

(*VALID a1 \<rightarrow> ALLOC \<rightarrow> VALID a1*)
lemma memory_valid_alloc_valid: "valid_memory_address s a \<longrightarrow> allocate_memory s = (s', a') \<longrightarrow> valid_memory_address s' a"
  unfolding valid_memory_address_def allocate_memory_def
  by auto

(*VALID a1 \<rightarrow> GET a1 = (ALLOC, GET a1)*)
lemma memory_alloc_get_eq: "valid_memory_address s a \<longrightarrow> get_memory s a = Ok v \<longrightarrow> allocate_memory s = (s', a') \<longrightarrow> get_memory s' a = Ok v"
  unfolding get_memory_def allocate_memory_def valid_memory_address_def
  using nth_append_left
  by auto



subsection "Executors"

(* Store instruction helpers *)
fun store_to_stack_or_heap :: "Registers \<Rightarrow> MemoryModel \<Rightarrow> MemoryModel \<Rightarrow> LLVMAddress \<Rightarrow> LLVMValue \<Rightarrow> State Result" where
  "store_to_stack_or_heap r s h (StackAddress a) v =
      (case set_memory s a v of Ok s' \<Rightarrow> Ok (r, s', h) | Err e \<Rightarrow> Err e)"
| "store_to_stack_or_heap r s h (HeapAddress a) v =
      (case set_memory h a v of Ok h' \<Rightarrow> Ok (r, s, h') | Err e \<Rightarrow> Err e)"

fun store_value :: "State \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "store_value (r, s, m) v (ptr p) =
   (case get_value r p of
      Ok (addr a) \<Rightarrow>
        (case get_value r v of
           Err e \<Rightarrow> Err e
         | Ok value \<Rightarrow> store_to_stack_or_heap r s m a value)
    | Ok _ \<Rightarrow> Err NotAnAddress
    | Err e \<Rightarrow> Err e)"


(* Load instruction helpers *)
fun load_from_stack_or_heap :: "MemoryModel \<Rightarrow> MemoryModel \<Rightarrow> LLVMAddress \<Rightarrow> LLVMValue Result" where
  "load_from_stack_or_heap s h (StackAddress a) =
    (case get_memory s a of Ok unset \<Rightarrow> Err UninitializedStackAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"
| "load_from_stack_or_heap s h (HeapAddress a) =
    (case get_memory s a of Ok unset \<Rightarrow> Err UninitializedMemoryAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"

fun load_value :: "State \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "load_value (r, s, m) n (ptr p) =
    (case get_value r p of
      Ok (addr a) \<Rightarrow>
        (case load_from_stack_or_heap s m a of
          Err e \<Rightarrow> Err e
        | Ok v \<Rightarrow>
          (case set_register r n v of
            Err e \<Rightarrow> Err e
          | Ok r' \<Rightarrow> Ok (r', s, m)))
    | Ok _ \<Rightarrow> Err NotAnAddress
    | Err e \<Rightarrow> Err e)"


(* Add instruction helpers *)
fun unsigned_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "unsigned_overflow32 a b = ((a + b) < a)"

fun signed_overflow32 :: "word32 \<Rightarrow> word32 \<Rightarrow> bool" where
  "signed_overflow32 a b = (sint a + sint b \<noteq> sint (a + b))"

fun unsigned_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "unsigned_overflow64 a b = ((a + b) < a)"

fun signed_overflow64 :: "word64 \<Rightarrow> word64 \<Rightarrow> bool" where
  "signed_overflow64 a b = (sint a + sint b \<noteq> sint (a + b))"

fun add_values :: "LLVMAddWrapOption \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue Result" where
  "add_values wrap (vi32 a) (vi32 b) = (
      let uov = unsigned_overflow32 a b;
          sov = signed_overflow32 a b
      in case wrap of
           AddDefaultWrap \<Rightarrow> Ok (vi32 (a + b))
         | AddNoUnsignedWrap \<Rightarrow> (if uov then Ok poison else Ok (vi32 (a + b)))
         | AddNoSignedWrap \<Rightarrow> (if sov then Ok poison else Ok (vi32 (a + b)))
         | AddNoUnsignedSignedWrap \<Rightarrow>
               (if uov \<or> sov then Ok poison else Ok (vi32 (a + b)))
     )"
| "add_values wrap (vi64 a) (vi64 b) = (
      let uov = unsigned_overflow64 a b;
          sov = signed_overflow64 a b
      in case wrap of
           AddDefaultWrap \<Rightarrow> Ok (vi64 (a + b))
         | AddNoUnsignedWrap \<Rightarrow> (if uov then Ok poison else Ok (vi64 (a + b)))
         | AddNoSignedWrap \<Rightarrow> (if sov then Ok poison else Ok (vi64 (a + b)))
         | AddNoUnsignedSignedWrap \<Rightarrow>
               (if uov \<or> sov then Ok poison else Ok (vi64 (a + b)))
     )"
| "add_values wrap poison v2 = Ok poison"
| "add_values wrap v1 poison = Ok poison"
| "add_values _ _ _ = Err IncompatibleTypes"


(* Execute a single instruction *)
fun execute_instruction :: "State \<Rightarrow> LLVMInstruction \<Rightarrow> (State * LLVMValue option) Result" where
  (* Allocate new memory value, and set the specified register to its address. *)
  "execute_instruction (r, s, m) (alloca name type align) =
    (let (s', a) = allocate_memory s in
      (case set_register r name (addr (StackAddress a)) of
        Err e \<Rightarrow> Err e
      | Ok r' \<Rightarrow> Ok ((r', s', m), None)))" |
  (* Read address from pointer and store value in either memory or memory. *)
  "execute_instruction s (store type value pointer align) =
    (case store_value s value pointer of
      Err e \<Rightarrow> Err e
    | Ok s' \<Rightarrow> Ok (s', None))" |
  (* Read address from pointer, and load value from either memory or memory. *)
  "execute_instruction s (load register type pointer align) =
    (case load_value s register pointer of
      Err e \<Rightarrow> Err e
    | Ok s' \<Rightarrow> Ok (s', None))" |
  (* Get values, add according to wrap option (or poison), and store in register. *)
  "execute_instruction (r, s, m) (add register wrap type v1 v2) =
    (case get_value r v1 of
      Err e \<Rightarrow> Err e
    | Ok v1' \<Rightarrow>
      (case get_value r v2 of
        Err e \<Rightarrow> Err e
      | Ok v2' \<Rightarrow>
        (case add_values wrap v1' v2' of
          Err e \<Rightarrow> Err e
        | Ok v \<Rightarrow>
          (case set_register r register v of
            Err e \<Rightarrow> Err e
          | Ok r' \<Rightarrow> Ok ((r', s, m), None)))))" |
  (* Set the return value to the value of v. *)
  "execute_instruction (r, s, m) (ret t v) =
    (case get_value r v of
      Err e \<Rightarrow> Err e
    | Ok v' \<Rightarrow> Ok ((r, s, m), Some v'))"


fun execute_instructions :: "State \<Rightarrow> LLVMInstruction list \<Rightarrow> (State * LLVMValue option) Result" where
  "execute_instructions s [] = Ok (s, None)" |
  "execute_instructions s (i#is) =
    (case execute_instruction s i of
      Err e \<Rightarrow> Err e
    | Ok (s', r) \<Rightarrow>
      (case r of
        None \<Rightarrow> execute_instructions s' is
      | (Some _) \<Rightarrow> Ok (s', r)))"

fun execute_function :: "State \<Rightarrow> LLVMFunction \<Rightarrow> (LLVMValue option) Result" where
  "execute_function v (Func _ i _) =
    (case execute_instructions v i of
      Err e \<Rightarrow> Err e
    | Ok (_, r) \<Rightarrow> Ok r)"





definition main :: "LLVMFunction" where
  "main = Func (FuncDef ''main'' i32) [
    alloca ''%1'' i32 (Some 4),
    alloca ''%2'' i32 (Some 4),
    alloca ''%3'' i32 (Some 4),
    alloca ''%4'' i32 (Some 4),
    store i32 (val (vi32 0)) (ptr (reg ''%1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''%2'')) (Some 4),
    store i32 (val (vi32 2)) (ptr (reg ''%3'')) (Some 4),
    store i32 (val (vi32 3)) (ptr (reg ''%3'')) (Some 4),
    load ''%5'' i32 (ptr (reg ''%2'')) (Some 4),
    load ''%6'' i32 (ptr (reg ''%3'')) (Some 4),
    add ''%7'' AddNoUnsignedWrap i32 (reg ''%5'') (reg ''%6''),
    store i32 (reg ''%7'') (ptr (reg ''%4'')) (Some 4),
    load ''%8'' i32 (ptr (reg ''%4'')) (Some 4),
    ret i32 (reg ''%8'')
  ] (\<lambda>x. None)"

definition meta :: "LLVMMetaData" where
  "meta = Meta ''test.c'' ''e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128'' ''x86_64-w64-windows-gnu''"

definition attrs :: "LLVMAttributes" where
  "attrs = []"

value "LLVM meta [main] attrs"

value "execute_function (Mapping.empty, [], []) main"


end