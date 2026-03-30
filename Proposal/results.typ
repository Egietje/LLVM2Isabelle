#import "functions.typ": fig

= Preliminary Results (WIP)
<sec-preliminary-results>

This section covers the preliminary results from work already done.
Specifically, it details how `SG1` and `SG2` have already been achieved in @sec-llvm-in-isabelle and @sec-ver-infra respectively, and how `SG3` is being tackled in @sec-ver-tools.

== LLVM-IR in Isabelle
<sec-llvm-in-isabelle>

A subset of LLVM-IR's structure and semantics have been defined in Isabelle.
The chosen subset covers basic language features that allow simple programs, such as the `mult` function from @lst-mult-llvm, to be described and executed.
Specifically, the structure of some instructions, basic blocks, functions, and programs have been defined, as well as their semantics.

The structure has been defined using datatypes in the form of its AST.
For example, a datatype `llvm_instruction` has been defined which can be instantiated as any of the supported instructions with their specific options according to their definition in LLVM's language reference manual.
Its definition is shown in @lst-instr-type.
Such definitions have been made for types, typed values, identifiers, value references (either a direct value, or value from a register), alignment specifications, add wrap options, compare conditions,
phi instructions, regular instructions, terminator instructions, basic blocks, block return values, functions, and programs.

#fig(```isabelle
datatype llvm_instruction = alloca llvm_register_name llvm_type "llvm_align option"
                          | store llvm_type llvm_value_ref llvm_pointer "llvm_align option"
                          | load llvm_register_name llvm_type llvm_pointer "llvm_align option"
                          | add llvm_register_name llvm_add_wrap llvm_type llvm_value_ref llvm_value_ref
                          | icmp llvm_register_name llvm_same_sign llvm_compare_condition llvm_type llvm_value_ref llvm_value_ref
```,
  [Datatype Definition for LLVM-IR Instructions]
)<lst-instr-type>

On top of this representation of the AST, the semantics are defined using functions that form an interpreter.
At the instruction level lies a function that takes in an execution state, a triple of register values, stack memory, and heap memory, as well as an `llvm_instruction`, and produces a new state result.
This result can be successful, in which case it contains the new state, or be erroneous if some execution requirement was not met, for example when trying access a value in a register that has not been assigned.
Using this function, a basic block executor is defined that executes its internal instructions in-order, taking in an execution state and basic block, and producing a result tuple of a new state and block return value.
Its definition is shown in @lst-block-exec.
For this, a monad is defined for the `result` type, so errors automatically short-circuit execution, and successful execution flows naturally.
Block return values contain information on whether to branch to a different basic block, or return from the function with a value.
Finally, an executor for functions is defined that uses the basic block executor to execute its basic blocks, using the block return values to properly handle control-flow.

#fig(```isabelle
fun execute_block :: "llvm_label option ⇒ llvm_instruction_block ⇒ state ⇒ (state * llvm_block_return) result" where
  "execute_block previous ((phi name type values)#ps, is, t) s = do {
    s' ← execute_phi previous name values s;
    execute_block previous (ps, is, t) s'
  }"
| "execute_block previous ([], i#is, t) s = do {
    s' ← execute_instruction i s;
    execute_block previous ([], is, t) s'
  }"
| "execute_block previous (_, _, br_i1 v l1 l2) s = do {
    val ← get_register s v;
    label ← (case val of (vi1 b) ⇒ ok (if b then l1 else l2) | _ ⇒ err incompatible_types);
    return (s, branch_label label)
  }"
| "execute_block previous (_, _, br_label l) s = return (s, branch_label l)"
| "execute_block previous (_, _, ret t v) s = do {
    res ← get_register s v;
    return (s, return_value res)
  }"
```,
  [Basic Block Execution Function]
)<lst-block-exec>

Together, the defined structure and semantics can be used to execute functions made up of the supported instructions.

== Verification Infrastructure
<sec-ver-infra>

  - on top of the structure and semantics, weakest pre-condition infrastucture has been defined
  - using these weakest pre-conditions, single instructions can be symbolically executed, giving the user proof-goals for their prerequisites to execute without errors and the resulting execution state, using proof-friendly abstractions
  - also, entire instruction blocks can be executed symbolically, giving the user proof-goals for successful execution of the entire block and the final execution state, using the same abstractions


== Verification Tools
<sec-ver-tools>

  - hoare triple definition to invoke weakest pre-condition infrastructure more intuitively
  - annotated function datatype to specify pre-conditions for basic blocks in a function, as well as post-conditions for the function
  - `verify` function that takes an annotated function and produces a boolean if it can be v
  - Eisbach methods to automatically perform verification of sub-goals (along with debug variants), allowing the user to only have to deal with the final goals, or failing sub-goals (e.g. due to missing pre-conditions for basic blocks)
  - TODO is ensuring this functionality works properly, handle edge-cases more elegantly, and clean it up


This section will cover the following information:

- `SG1` has been achieved:
- `SG2` has been achieved:
- `SG3` has been mostly achieved:
- `SG4` has not been achieved yet:
  - only a few simple programs have been put through the tool, too simple to say much about its true usefulness

/*


Preliminary results

Work has already begun defining the semantics of LLVM in Isabelle and creating a verification condition generator based on Floyd's assertion method using weakest precondition mechanics.


 LLVM semantics

Part of the LLVM-IR's AST has been defined as datatypes in Isabelle.
With this part of the AST, functions made up of instruction blocks can be executed.

The operational semantics are defined as follows:
- Functions contain multiple labeled instruction blocks and one unlabeled block to be executed first.
- Instruction blocks have a list of regular instructions to be executed in order and one terminator instruction that impacts execution flow.
- Instructions are executed according to their specification in the LLVM Language Reference Manual.#footnote("https://llvm.org/docs/LangRef.html")

Execution of any single instruction takes in some state and produces a state.
This state is defined as follows:
- It is a triple of single static assignment (SSA) values, a stack, and a heap.
- The stack and heap have the same underlying memory definition: a list of values. They are addressable using indices in these lists.
- SSA values are a mapping from a name to a value. Although LLVM only allows assigning them once per function, this only applies to their static definition, not their value in execution. As such, no such limitation is posed here. This means the verifier works on a superset of LLVM.

The regular instructions currently (partly) implemented are:
- alloca - allocates a new address in the stack, and keeps track of the address with some SSA name.
- store - stores a value at some address in the stack or heap.
- load - loads a value from some address in the stack or heap and keep track of it with an SSA name.
- icmp - compares two values (32/64 bit signed/unsigned integers) and keep track of the result as a single bit (boolean) with an SSA name.
- add - adds two values (32/64 bit signed/unsigned integers) and keep track of the result with an SSA name (another 32/64 bit integer or a poison value if an overflow occurred).
- phi - stores an SSA value from a list of possible values depending on the instruction block that lead to this block.

The terminator instructions implemented are:
- br - branch to a different instruction given its label (could always be the same label, or switch based on a boolean SSA value).
- ret - return from the function with some value.

With this implementation, basic programs consisting of these instructions can already be executed.
For example, take the following C program:
```C
int main() {
    int y = 1;
    int x = y?1:0;
    return x;
}
```

This might produce the following LLVM-IR code:
```llvm
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  %5 = load i32, ptr %2, align 4
  %6 = icmp ne i32 %5, 0
  br i1 %6, label %7, label %9

7:
  store i32 1, ptr %4, align 4
  %8 = load i32, ptr %4, align 4
  br label %10

9:
  br label %10

10:
  %11 = phi i32 [ %8, %9 ], [ 0, %9 ]
  store i32 %11, ptr %3, align 4
  %12 = load i32, ptr %3, align 4
  ret i32 %12
}
```

Encoded into the current AST representation, this becomes:
```isabelle
definition pmain :: "llvm_instruction_block" where
  "pmain = ([
    alloca ''1'' i32 (Some 4),
    alloca ''2'' i32 (Some 4),
    alloca ''3'' i32 (Some 4),
    alloca ''4'' i32 (Some 4),
    store i32 (val (vi32 0)) (ssa_val ''1'') (Some 4),
    store i32 (val (vi32 1)) (ssa_val ''2'') (Some 4),
    load ''5'' i32 (ssa_val ''2'') (Some 4),
    icmp ''6'' False comp_ne i32 (ssa_val ''5'') (val (vi32 0))],
    br_i1 (ssa_val ''6'') ''7'' ''9''
  )"

definition p7 :: "llvm_instruction_block" where
  "p7 = ([
    store i32 (val (vi32 1)) (ssa_val ''4'') (Some 4),
    load ''8'' i32 (ssa_val ''4'') (Some 4)],
    br_label ''10''
  )"

definition p9 :: "llvm_instruction_block" where
  "p9 = ([],
    br_label ''10''
  )"

definition p10 :: "llvm_instruction_block" where
  "p10 = ([
    phi ''11'' i32 [(''7'', ssa_val ''8''), (''9'', val (vi32 0))],
    store i32 (ssa_val ''11'') (ssa_val ''3'') (Some 4),
    load ''12'' i32 (ssa_val ''3'') (Some 4)],
    ret i32 (ssa_val ''12'')
  )"

definition phi_main :: "llvm_function" where
  "phi_main = func (func_def ''main'' i32) pmain [(''7'', p7), (''9'', p9), (''10'', p10)]"
```

This can be executed as follows, which gives the proper return value:
```isabelle
value "execute_function empty_state phi_main"

= "ok (Some (vi32 1))" :: "llvm_value option result"
```


 Weakest precondition mechanics

- Intro rules done for abstractions, some instructions

*/
