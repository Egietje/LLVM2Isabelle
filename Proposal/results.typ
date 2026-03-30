= Preliminary Results (WIP)
<sec-preliminary-results>

This section will cover the following information:

- `SG1` has been achieved:
  - a subset of LLVM-IR's structure and semantics have been defined in Isabelle:
  - structure defined using datatypes in the form of its AST
  - semantics defined using functions that form an interpreter which can be given part of the AST to execute instruction blocks 
- `SG2` has been achieved:
  - on top of the structure and semantics, weakest pre-condition infrastucture has been defined
  - using these weakest pre-conditions, single instructions can be symbolically executed, giving the user proof-goals for their prerequisites to execute without errors and the resulting execution state, using proof-friendly abstractions
  - also, entire instruction blocks can be executed symbolically, giving the user proof-goals for successful execution of the entire block and the final execution state, using the same abstractions
- `SG3` has been mostly achieved:
  - hoare triple definition to invoke weakest pre-condition infrastructure more intuitively
  - annotated function datatype to specify pre-conditions for basic blocks in a function, as well as post-conditions for the function
  - `verify` function that takes an annotated function and produces a boolean if it can be v
  - Eisbach methods to automatically perform verification of sub-goals (along with debug variants), allowing the user to only have to deal with the final goals, or failing sub-goals (e.g. due to missing pre-conditions for basic blocks)
  - TODO is ensuring this functionality works properly, handle edge-cases more elegantly, and clean it up
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
