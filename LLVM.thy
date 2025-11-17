theory LLVM
  imports Main HOL.Real "Word_Lib/Word_64" "Word_Lib/Word_32"
begin

section "LLVM AST"

datatype LLVMType = i32 | i64 | f32 | saddr | maddr

type_synonym LLVMRegisterName = string
type_synonym LLVMStackAddress = nat
type_synonym LLVMMemoryAddress = nat

datatype LLVMValue = vi32 word32 | vi64 word64 | vsaddr LLVMStackAddress | vmaddr LLVMMemoryAddress | poison | freed | unset

datatype LLVMValueRef = reg LLVMRegisterName | val LLVMValue

(* Should only have a stack address or memory address... *)
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

fun isOk :: "'a Result \<Rightarrow> bool" where
  "isOk (Ok _) = True"
| "isOk (Err _) = False"


type_synonym Registers = "(LLVMRegisterName * LLVMValue) list"
type_synonym Stack = "LLVMValue list"
type_synonym Memory = "LLVMValue list"

type_synonym State = "Registers * Stack * Memory"


(* Register functions and lemmas *)
fun get_register :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue Result" where
  "get_register [] _ = Err UnknownRegister"
| "get_register ((n, v)#r) n' = (if n = n' then Ok v else get_register r n')"

definition set_register :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue \<Rightarrow> Registers Result" where
  "set_register r n v = (case get_register r n of
    (Ok _) \<Rightarrow> Err RegisterOverride |
    _ \<Rightarrow> Ok ((n,v)#r))"

fun get_value :: "Registers \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMValue Result" where
  "get_value _ (val v) = Ok v" |
  "get_value r (reg n) = get_register r n"


lemma set_unknown_register: "get_register r n = Err UnknownRegister \<longrightarrow> Ok r' = set_register r n v \<longrightarrow> get_register r' n = Ok v"
  using set_register_def by auto

lemma override_register: "get_register r n = Ok v \<longrightarrow> set_register r n v' = Err RegisterOverride"
  using set_register_def by simp

lemma set_set_unknown_register: "get_register r n = Err UnknownRegister \<longrightarrow> Ok r' = set_register r n v \<longrightarrow> set_register r' n v' = Err RegisterOverride"
  using set_unknown_register override_register by simp

lemma get_value_register: "get_register r n = Ok v \<longrightarrow> get_value r (reg n) = Ok v"
  by simp


(* Stack functions and lemmas *)
definition allocate_stack :: "Stack \<Rightarrow> (Stack * LLVMStackAddress)" where
  "allocate_stack s = (s@[unset], length s)"

definition valid_stack_address :: "Stack \<Rightarrow> LLVMStackAddress \<Rightarrow> bool" where
  "valid_stack_address s a = (a < length s)"

fun get_stack :: "Stack \<Rightarrow> LLVMStackAddress \<Rightarrow> LLVMValue Result" where
  "get_stack [] _ = Err UnallocatedStackAddress" |
  "get_stack (x#_) 0 = Ok x" |
  "get_stack (_#xs) (Suc a) = get_stack xs a"

fun set_stack :: "Stack \<Rightarrow> LLVMStackAddress \<Rightarrow> LLVMValue \<Rightarrow> Stack Result" where
  "set_stack [] _ _ = Err UnallocatedStackAddress" |
  "set_stack (_#s) 0 v = Ok (v#s)" |
  "set_stack (x#xs) (Suc n) v = (case (set_stack xs n v) of
    (Err e) \<Rightarrow> Err e |
    (Ok s) \<Rightarrow> Ok (x#s))"

lemma stack_allocate_append_unset: "(s', i) = allocate_stack s \<longrightarrow> s' = s@[unset]"
  using allocate_stack_def by simp

lemma stack_allocate_len: "(s', i) = allocate_stack s \<longrightarrow> length s' = length s + 1"
  using allocate_stack_def by simp

lemma stack_allocate_index_unset: "(s', i) = allocate_stack s \<longrightarrow> s'!i = unset"
  using allocate_stack_def by simp

lemma stack_get_eq_index: "i < length s \<longrightarrow> get_stack s i = Ok (s!i)"
  by (induct rule: get_stack.induct; simp)

lemma stack_allocate_get_unset: "(s', i) = allocate_stack s \<longrightarrow> get_stack s' i = Ok unset"
  using allocate_stack_def stack_get_eq_index by simp

lemma stack_set_unallocated: "i \<ge> length s \<longrightarrow> set_stack s i v = Err UnallocatedStackAddress"
  by (induct rule: set_stack.induct; simp)

lemma stack_set_ok: "i < length s \<longrightarrow> s' = set_stack s i v \<longrightarrow> isOk s'"
proof (induct rule: set_stack.induct)
  case (1 uu uv)
  then show ?case by simp
next
  case (2 uw s v)
  then show ?case by simp
next
  case (3 x xs n v)
  then show ?case by (cases "set_stack xs n v"; simp)
qed

lemma aaaa: "i < length s \<longrightarrow> Suc i < length (a#s)" by simp
lemma aaab: "Suc i < length (a#s) \<longrightarrow> i < length s" by simp

lemma stack_set_len: "i < length s \<longrightarrow> Ok s' = set_stack s i v \<longrightarrow> length s = length s'"
proof (induct s)
  case Nil
  then show ?case by simp
next
  case (Cons a s)
  then show ?case proof (induct i)
    case 0
    then show ?case by simp
  next
    case (Suc i)
    then have "length s = i" using Suc Cons try sorry
    then show ?case try0 sorry
  qed
qed


lemma stack_get_set: "i < length s \<longrightarrow> Ok s' = set_stack s i v \<longrightarrow> get_stack s' i = Ok v"
proof (induct rule: get_stack.induct)
  case (1 uu)
  then show ?case sorry
next
  case (2 x uv)
  then show ?case sorry
next
  case (3 uw xs a)
  then show ?case sorry
qed



fun allocate_memory :: "Memory \<Rightarrow> (Memory * LLVMMemoryAddress)" where
  "allocate_memory [] = ([unset], 0)" |
  "allocate_memory (x#xs) = (let (s, a) = allocate_memory xs in (x#s, Suc a))"

fun get_memory :: "Memory \<Rightarrow> LLVMMemoryAddress \<Rightarrow> LLVMValue Result" where
  "get_memory [] _ = Err UnallocatedMemoryAddress" |
  "get_memory (x#_) 0 = Ok x" |
  "get_memory (_#xs) (Suc a) = get_memory xs a"

fun set_memory :: "Memory \<Rightarrow> LLVMMemoryAddress \<Rightarrow> LLVMValue \<Rightarrow> Memory Result" where
  "set_memory [] _ _ = Err UnallocatedMemoryAddress" |
  "set_memory (_#s) 0 v = Ok (v#s)" |
  "set_memory (x#xs) (Suc n) v = (case (set_memory xs n v) of
    (Err e) \<Rightarrow> Err e |
    (Ok s) \<Rightarrow> Ok (x#s))"



subsection "Executors"

(* Store instruction helpers *)
fun store_val_to_stack_or_mem :: "Registers \<Rightarrow> Stack \<Rightarrow> Memory \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue \<Rightarrow> State Result" where
  "store_val_to_stack_or_mem r s m (vsaddr a) value =
      (case set_stack s a value of Ok s' \<Rightarrow> Ok (r, s', m) | Err e \<Rightarrow> Err e)"
| "store_val_to_stack_or_mem r s m (vmaddr a) value =
      (case set_memory m a value of Ok m' \<Rightarrow> Ok (r, s, m') | Err e \<Rightarrow> Err e)"
| "store_val_to_stack_or_mem _ _ _ _ _ = Err NotAnAddress"

fun store_value :: "State \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "store_value (r, s, m) v (ptr p) =
   (case get_value r p of
      Err e \<Rightarrow> Err e
    | Ok a \<Rightarrow>
        (case get_value r v of
           Err e \<Rightarrow> Err e
         | Ok value \<Rightarrow> store_val_to_stack_or_mem r s m a value))"


(* Load instruction helpers *)
fun load_val_from_stack_or_mem :: "Stack \<Rightarrow> Memory \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue Result" where
  "load_val_from_stack_or_mem s m (vsaddr a) =
    (case get_stack s a of Ok unset \<Rightarrow> Err UninitializedStackAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"
| "load_val_from_stack_or_mem s m (vmaddr a) =
    (case get_memory s a of Ok unset \<Rightarrow> Err UninitializedMemoryAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"
| "load_val_from_stack_or_mem _ _ _ = Err NotAnAddress"

fun load_value :: "State \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "load_value (r, s, m) n (ptr p) =
    (case get_value r p of
      Ok a \<Rightarrow>
        (case load_val_from_stack_or_mem s m a of
          Err e \<Rightarrow> Err e
        | Ok v \<Rightarrow>
          (case set_register r n v of
            Err e \<Rightarrow> Err e
          | Ok r' \<Rightarrow> Ok (r', s, m)))
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
  (* Allocate new stack value, and set the specified register to its address. *)
  "execute_instruction (r, s, m) (alloca name type align) =
    (let (s', a) = allocate_stack s in
      (case set_register r name (vsaddr a) of
        Err e \<Rightarrow> Err e
      | Ok r' \<Rightarrow> Ok ((r', s', m), None)))" |
  (* Read address from pointer and store value in either stack or memory. *)
  "execute_instruction s (store type value pointer align) =
    (case store_value s value pointer of
      Err e \<Rightarrow> Err e
    | Ok s' \<Rightarrow> Ok (s', None))" |
  (* Read address from pointer, and load value from either stack or memory. *)
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

value "execute_function ([], [], []) main"


end