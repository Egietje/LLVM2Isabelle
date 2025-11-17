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


type_synonym Registers = "(LLVMRegisterName * LLVMValue) list"
type_synonym Stack = "LLVMValue list"
type_synonym Memory = "LLVMValue list"

type_synonym State = "Registers * Stack * Memory"


fun getRegister :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue Result" where
  "getRegister [] _ = Err UnknownRegister"
| "getRegister ((n, v)#r) n' = (if n = n' then Ok v else getRegister r n')"

definition setRegister :: "Registers \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMValue \<Rightarrow> Registers Result" where
  "setRegister r n v = (case getRegister r n of
    (Ok _) \<Rightarrow> Err RegisterOverride |
    _ \<Rightarrow> Ok ((n,v)#r))"

fun getValue :: "Registers \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMValue Result" where
  "getValue _ (val v) = Ok v" |
  "getValue r (reg n) = getRegister r n"


fun allocateStack :: "Stack \<Rightarrow> (Stack * LLVMStackAddress)" where
  "allocateStack [] = ([unset], 0)" |
  "allocateStack (x#xs) = (let (s, a) = allocateStack xs in (x#s, Suc a))"

fun getStack :: "Stack \<Rightarrow> LLVMStackAddress \<Rightarrow> LLVMValue Result" where
  "getStack [] _ = Err UnallocatedStackAddress" |
  "getStack (x#_) 0 = Ok x" |
  "getStack (_#xs) (Suc a) = getStack xs a"

fun setStack :: "Stack \<Rightarrow> LLVMStackAddress \<Rightarrow> LLVMValue \<Rightarrow> Stack Result" where
  "setStack [] _ _ = Err UnallocatedStackAddress" |
  "setStack (_#s) 0 v = Ok (v#s)" |
  "setStack (x#xs) (Suc n) v = (case (setStack xs n v) of
    (Err e) \<Rightarrow> Err e |
    (Ok s) \<Rightarrow> Ok (x#s))"


fun allocateMemory :: "Memory \<Rightarrow> (Memory * LLVMMemoryAddress)" where
  "allocateMemory [] = ([unset], 0)" |
  "allocateMemory (x#xs) = (let (s, a) = allocateMemory xs in (x#s, Suc a))"

fun getMemory :: "Memory \<Rightarrow> LLVMMemoryAddress \<Rightarrow> LLVMValue Result" where
  "getMemory [] _ = Err UnallocatedMemoryAddress" |
  "getMemory (x#_) 0 = Ok x" |
  "getMemory (_#xs) (Suc a) = getMemory xs a"

fun setMemory :: "Memory \<Rightarrow> LLVMMemoryAddress \<Rightarrow> LLVMValue \<Rightarrow> Memory Result" where
  "setMemory [] _ _ = Err UnallocatedMemoryAddress" |
  "setMemory (_#s) 0 v = Ok (v#s)" |
  "setMemory (x#xs) (Suc n) v = (case (setMemory xs n v) of
    (Err e) \<Rightarrow> Err e |
    (Ok s) \<Rightarrow> Ok (x#s))"



subsection "Executors"

(* Store instruction helpers *)
fun storeValueToStackOrMemory :: "Registers \<Rightarrow> Stack \<Rightarrow> Memory \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue \<Rightarrow> State Result" where
  "storeValueToStackOrMemory r s m (vsaddr a) value =
      (case setStack s a value of Ok s' \<Rightarrow> Ok (r, s', m) | Err e \<Rightarrow> Err e)"
| "storeValueToStackOrMemory r s m (vmaddr a) value =
      (case setMemory m a value of Ok m' \<Rightarrow> Ok (r, s, m') | Err e \<Rightarrow> Err e)"
| "storeValueToStackOrMemory _ _ _ _ _ = Err NotAnAddress"

fun storeValue :: "State \<Rightarrow> LLVMValueRef \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "storeValue (r, s, m) v (ptr p) =
   (case getValue r p of
      Err e \<Rightarrow> Err e
    | Ok a \<Rightarrow>
        (case getValue r v of
           Err e \<Rightarrow> Err e
         | Ok value \<Rightarrow> storeValueToStackOrMemory r s m a value))"


(* Load instruction helpers *)
fun loadValueFromStackOrMemory :: "Stack \<Rightarrow> Memory \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue Result" where
  "loadValueFromStackOrMemory s m (vsaddr a) =
    (case getStack s a of Ok unset \<Rightarrow> Err UninitializedStackAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"
| "loadValueFromStackOrMemory s m (vmaddr a) =
    (case getMemory s a of Ok unset \<Rightarrow> Err UninitializedMemoryAddress | Ok v \<Rightarrow> Ok v | Err e \<Rightarrow> Err e)"
| "loadValueFromStackOrMemory _ _ _ = Err NotAnAddress"

fun loadValue :: "State \<Rightarrow> LLVMRegisterName \<Rightarrow> LLVMPointer \<Rightarrow> State Result" where
  "loadValue (r, s, m) n (ptr p) =
    (case getValue r p of
      Ok a \<Rightarrow>
        (case loadValueFromStackOrMemory s m a of
          Err e \<Rightarrow> Err e
        | Ok v \<Rightarrow>
          (case setRegister r n v of
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

fun addValues :: "LLVMAddWrapOption \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue \<Rightarrow> LLVMValue Result" where
  "addValues wrap (vi32 a) (vi32 b) = (
      let uov = unsigned_overflow32 a b;
          sov = signed_overflow32 a b
      in case wrap of
           AddDefaultWrap \<Rightarrow> Ok (vi32 (a + b))
         | AddNoUnsignedWrap \<Rightarrow> (if uov then Ok poison else Ok (vi32 (a + b)))
         | AddNoSignedWrap \<Rightarrow> (if sov then Ok poison else Ok (vi32 (a + b)))
         | AddNoUnsignedSignedWrap \<Rightarrow>
               (if uov \<or> sov then Ok poison else Ok (vi32 (a + b)))
     )"
| "addValues wrap (vi64 a) (vi64 b) = (
      let uov = unsigned_overflow64 a b;
          sov = signed_overflow64 a b
      in case wrap of
           AddDefaultWrap \<Rightarrow> Ok (vi64 (a + b))
         | AddNoUnsignedWrap \<Rightarrow> (if uov then Ok poison else Ok (vi64 (a + b)))
         | AddNoSignedWrap \<Rightarrow> (if sov then Ok poison else Ok (vi64 (a + b)))
         | AddNoUnsignedSignedWrap \<Rightarrow>
               (if uov \<or> sov then Ok poison else Ok (vi64 (a + b)))
     )"
| "addValues wrap poison v2 = Ok poison"
| "addValues wrap v1 poison = Ok poison"
| "addValues _ _ _ = Err IncompatibleTypes"


(* Execute a single instruction *)
fun executeInstruction :: "State \<Rightarrow> LLVMInstruction \<Rightarrow> (State * LLVMValue option) Result" where
  (* Allocate new stack value, and set the specified register to its address. *)
  "executeInstruction (r, s, m) (alloca name type align) =
    (let (s', a) = allocateStack s in
      (case setRegister r name (vsaddr a) of
        Err e \<Rightarrow> Err e
      | Ok r' \<Rightarrow> Ok ((r', s', m), None)))" |
  (* Read address from pointer and store value in either stack or memory. *)
  "executeInstruction s (store type value pointer align) =
    (case storeValue s value pointer of
      Err e \<Rightarrow> Err e
    | Ok s' \<Rightarrow> Ok (s', None))" |
  (* Read address from pointer, and load value from either stack or memory. *)
  "executeInstruction s (load register type pointer align) =
    (case loadValue s register pointer of
      Err e \<Rightarrow> Err e
    | Ok s' \<Rightarrow> Ok (s', None))" |
  (* Get values, add according to wrap option (or poison), and store in register. *)
  "executeInstruction (r, s, m) (add register wrap type v1 v2) =
    (case getValue r v1 of
      Err e \<Rightarrow> Err e
    | Ok v1' \<Rightarrow>
      (case getValue r v2 of
        Err e \<Rightarrow> Err e
      | Ok v2' \<Rightarrow>
        (case addValues wrap v1' v2' of
          Err e \<Rightarrow> Err e
        | Ok v \<Rightarrow>
          (case setRegister r register v of
            Err e \<Rightarrow> Err e
          | Ok r' \<Rightarrow> Ok ((r', s, m), None)))))" |
  (* Set the return value to the value of v. *)
  "executeInstruction (r, s, m) (ret t v) =
    (case getValue r v of
      Err e \<Rightarrow> Err e
    | Ok v' \<Rightarrow> Ok ((r, s, m), Some v'))"


fun executeInstructions :: "State \<Rightarrow> LLVMInstruction list \<Rightarrow> (State * LLVMValue option) Result" where
  "executeInstructions s [] = Ok (s, None)" |
  "executeInstructions s (i#is) =
    (case executeInstruction s i of
      Err e \<Rightarrow> Err e
    | Ok (s', r) \<Rightarrow>
      (case r of
        None \<Rightarrow> executeInstructions s' is
      | (Some _) \<Rightarrow> Ok (s', r)))"

fun executeFunction :: "State \<Rightarrow> LLVMFunction \<Rightarrow> (LLVMValue option) Result" where
  "executeFunction v (Func _ i _) =
    (case executeInstructions v i of
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

value "executeFunction ([], [], []) main"


end