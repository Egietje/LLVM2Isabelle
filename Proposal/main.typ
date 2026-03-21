
#let title-page(title:[], email:[], name:[], fill: yellow, body) = {
  set page(margin: (top: 3cm, rest: 4cm))
  set text(font: "Source Sans Pro", size: 14pt)
  set heading(numbering: "1.1.1")
  line(start: (0%, 0%), end: (8.5in, 0%), stroke: (thickness: 2pt))
  align(horizon + left)[
    #text(size: 24pt, title)\
    #v(1em)
    Research Topics
    #v(2em)
    #text(name)\
    #link(email)
  ]
  
  align(bottom + left)[#datetime.today().display()]
  pagebreak()
  set page(fill: none, margin: auto)
  align(horizon, outline(indent: auto))
  pagebreak()
  body
}
#let code(body, title) = figure(
  body,
  caption: title,
)


#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()

#codly(languages: codly-languages)



#show: body => title-page(
  title: "Deductive LLVM verification in Isabelle",
  email: "mailto:t.s.kas@student.utwente.nl",
  name: "Thomas Kas",
  body
)

#set page(margin: 1.5cm)
#set par(
  justify: true,
)


= Introduction

As software is used in more and more safety-critical areas, the importance of its verification grows rapidly.
It is used in modes of transportation like cars and planes, critical infrastructure like traffic lights and power plants, and many other areas.
If the software controlling these things fails, the consequences are great.
As such, verifying such pieces of software work as intended is crucial.

This verification can be done through various different methods.
One such method is model checking, where a model of the system the software acts upon is created and used to verify the software functions correctly in some or all possible states of the model.
Another method is dynamic analysis, where (a part of) the software is run and its results are checked against the expected outcome, commonly implemented in unit or acceptance tests.
In contrast to dynamic analysis, static analysis can identify possible issues without running the software, usually consisting of common programming mistakes but limited in its scope, as it usually does not verify the implementation matches the expected behavior.
Finally, there is deductive verification, which mathematically verifies correctness using logical reasoning based on pre- and post-conditions.
It is using this method that a new verification tool will be created in this thesis.

Verification can be done at various stages in compilation of software.
It might be done with the source code, which has the most meaning to developers as this is what they directly interact with and can alter easily, with fully compiled binaries, which says the most about the actual execution as compilation might introduce artifacts not present in the source code, or with some intermediary between these stages.

Performing verification on source code comes with the advantage that it is relatively easy to integrate the verification into the program, for example with in-line verification instructions, but this comes at the cost of the verification being tied to the specific programming language the software was written in.
Switching (part of) the software to a different programming language, for example when modernizing legacy code, means that either the verification tool used has to also support that new language, or a different verification tool has to be used and all existing verification has to be redone.

Targeting a lower level like machine instructions gets around this issue, but means that only a single target is verified, tying the verification to a specific architecture.
If the target architecture stays the same, it is possible to use the same verification regardless of the source language.
However, switching the target architecture means that a different verification tool has to be found and verification has to be redone once more.

This thesis aims to create a tool for deductive verification at a level between these two, namely LLVM-IR.
This is the intermediate representation of LLVM, a compilation framework that has separate front-ends and back-ends for different source languages and target architectures.
It allows language-engineers to have a single compilation target, LLVM-IR, to automatically support many different target architectures, including x86, ARM, and RISC-V.
Furthermore, it allows developers working on new hardware targets to implement a single backend for LLVM-IR, automatically enabling support for all languages that compile to it.
What this means for the tool is that, once functional, it automatically supports software written in many source languages for many target architectures.

Finally, the chosen verification tool for this thesis is Isabelle/HOL.
Isabelle/HOL is an interactive theorem prover that allows users to specify theorems using higher-order logic and mathematically prove them to be correct.
Whenever a new theorem is created, Isabelle gives the user proof (sub-)goals that have to be proven for the theorem to be accepted.
It provides different tools and solvers to the user which aid in simplifying, breaking up, and eventually proving these goals.
It is also a functional programming language, allowing users to create their own datatypes and functions, and letting them use these in their lemmas.


== Research Goals

With that, the goal of this thesis will be to create a deductive verification tool for LLVM-IR programs within Isabelle/HOL.
This will be achieved through the following steps:
+ defining the semantics of a subset of LLVM-IR in Isabelle,
+ implementing deductive verification infrastructure that works with these semantics,
+ creating tools to efficiently and effectively verify LLVM-IR programs,
+ use these tools on some program.



= Background

This section explores the background of the concepts that lay at the foundation of this thesis.
Specifically, @sec-ded-ver explains how deductive verification works and how it is done, then @sec-llvm explores how LLVM-IR is structured and how it works semantically, and finally @sec-isabelle introduces the different features of Isabelle/HOL that will be used to achieve the different goals of this thesis.

== Deductive Verification
<sec-ded-ver>

Deductive verification is a method to mathematically verify the correctness of programs based in pre- and post-conditions.
There exist many different deductive verifiers for different languages and toolchains, based on mostly the same principles.

At the core of deductive verification lie pre-conditions, commands, and post-conditions.
The combination of the three, often referred to as Hoare triples, allows one to reason about programs.
The pre-conditions, $P$, represent some conditions that have to hold for the command, $c$, to execute properly, while the post-conditions, $Q$, represent the intended result of the command.

#code(
  ```C
/*@
requires a * b < 2^32
requires b >= 0;
ensures \result == a * b;
*/
int mult(int a, int b);
```,
  [C `mult` Function Annotated with ACSL Specifications]
)<lst-mult-spec>

Consider @lst-mult-spec.
It contains a specification for the function `mult`, written in ACSL, a specification language used in deductive verification of C programs using Frama-C.
This specifies two pre-conditions and one post-condition for the function, which represents a command.
Specifically, the pre-conditions state that the inputs `a` and `b` multiplied should not exceed the 32-bit integer limit and `b` should be non-negative for the function to execute properly.
If this holds, then the post-condition states that the result will be the inputs `a` and `b` multiplied.

#code(
```C
int mult(int a, int b) {
    int result = 0;
    for (int i = 0; i < b; i++) {
        result += a;
    }
    return result;
}
```,
  [C `mult` Function Implementation]
)<lst-mult-impl>

To prove that a post-condition follows from the pre-conditions and the command, the semantic meaning of the command has to be described formally.
This time, consider the implementation of the `mult` function in @lst-mult-impl.
To prove anything about this function, the prover needs to know what exact effects the instructions have on the execution state: how values of the `int` type behave, how assigning variables behaves, how different operations such as `++` and `+=` interact these values, and how control-flow is impacted by the `for`-loop and `return` keyword.
Once it knows this, it can go through the instructions of the function and execute them symbolically, keeping track of how execution state and flow have been impacted thus far.


== LLVM-IR
<sec-llvm>

#code(
  ```llvm
define dso_local noundef i32 @mult(int, int)(i32 noundef %a, i32 noundef %b) {
entry:
  %a.addr = alloca i32, align 4
  %b.addr = alloca i32, align 4
  %result = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 %a, ptr %a.addr, align 4
  store i32 %b, ptr %b.addr, align 4
  store i32 0, ptr %result, align 4
  store i32 0, ptr %i, align 4
  br label %for.cond

for.cond:
  %0 = load i32, ptr %i, align 4
  %1 = load i32, ptr %b.addr, align 4
  %cmp = icmp slt i32 %0, %1
  br i1 %cmp, label %for.body, label %for.end

for.body:
  %2 = load i32, ptr %a.addr, align 4
  %3 = load i32, ptr %result, align 4
  %add = add nsw i32 %3, %2
  store i32 %add, ptr %result, align 4
  br label %for.inc

for.inc:
  %4 = load i32, ptr %i, align 4
  %inc = add nsw i32 %4, 1
  store i32 %inc, ptr %i, align 4
  br label %for.cond

for.end:
  %5 = load i32, ptr %result, align 4
  ret i32 %5
}
```,
  [`mult` Function compiled to LLVM-IR]
)<lst-mult-llvm>

It is possible to go even further.
LLVM is a toolkit for the construction of compilers, optimizers, and run-time environments, and LLVM-IR is its intermediate representation (IR), a low-level programming language similar to assembly.
It can be used to develop front-ends for any programming languages, and back-ends for any target architectures.
It supports compiling many languages, including C, C++, Haskell, and Rust, to a wide range of target architectures, including x86-64, ARM, and RISC-V.
An example of the C `mult` function compiled to LLVM-IR can be seen in @lst-mult-llvm.

By targeting LLVM-IR with a deductive verifier, all supported front-end languages and back-end architectures are supported in a single verifier.
This drastically increases the usefulness of such a tool: users only need to learn how to use this one tool to be able to verify the correctness of almost any program, no matter what source language it is written in or what architecture the program will run on.
Moreover, decompilation of assembly into LLVM-IR is relatively simple due to its low-level nature and as such, verifying programs without their source code is also possible.


== Isabelle
<sec-isabelle>

In order to do any kind of deductive verification, some proof assistant is needed.
It has to be able to formally represent LLVM-IR and describe its exact semantics, and it needs to be able to mathematically prove theorems stated using these semantics.
The interactive theorem-prover Isabelle is well-suited to this task.

Moreover, Isabelle is a functional language and allows users to create functions that can be used within proofs.
Most recursive functions are automatically proven to terminate, but some require the user to prove they terminate.
Pattern matching can be used in the definitions of functions.
For example, see the `mult` function written as a recursive function over `b` in @lst-mult-isabelle.
Here, `a` and `b` are natural numbers.

#code(
  ```isabelle
fun mult where
  "mult a 0 = 0"
| "mult a (Suc b) = a + mult a b"
  ```,
  [Isabelle `mult` Recursive Function]
)<lst-mult-isabelle>

Creating a theorem to prove that the `mult` function indeed multiplies the two inputs is possible by stating that `mult a b` is equal to `a * b`.
This can be seen in @lst-mult-proof.

#code(
  ```isabelle
lemma "mult a b = a * b"
  apply (induction b)
  apply simp
  apply simp
  done
```,
  [Theorem of `mult` Function Result in Isabelle]
)<lst-mult-proof>

The proof works as follows:
- applying induction over `b`, to get two sub-goals:
  - the base case: `mult a 0 = a * 0`
  - the inductive step: `⋀b. mult a b = a * b ⟹ mult a (Suc b) = a * (Suc b)`
- applying the simplifier to the base case, which rewrites `mult a 0` to its definition, `0`, and rewrites `a * 0` to `0` as well, and finally proves the sub-goal `0 = 0` using reflection.
- applying the simplifier to the inductive step, which rewrites `mult a (Suc b)` to its definition `a + mult a b`, uses the assumption (which is specified for any b) to rewrite `mult a b` to `a * b` resulting in `a + a * b = a * (Suc b)`, and finally proves it correct using the internal definition of multiplication of natural numbers and reflection.


== Goals and Structure

The goal of this thesis is to create a deductive verifier for a subset of LLVM-IR programs using Isabelle.

[LLVM background section ref] gives an in-depth overview of the structure and semantics of LLVM-IR, while [Isabelle background section ref] gives an in-depth overview of how Isabelle works and can be used for this purpose.


For research topics:

Then, [preliminary results section ref] shows what has already been implemented to meet the goal of the thesis, while [next work and planning section ref] goes over what still needs to be done along with a rough planning on when these will be achieved. Finally, [related works section ref] goes over other work in the deductive verification space.

For final thesis:

Then, [LLVM-IR semantics in Isabelle section ref] shows how the LLVM-IR structure and semantics have been defined within Isabelle, and [deductive verification of LLVM-IR in Isabelle section ref] explains how these semantics are used to create a deductive verifier for LLVM-IR in Isabelle.
Next, [using the deductive verifier section ref] uses this deductive verifier to verify an LLVM-IR program.
Finally, [related works section ref] goes over other work in the deductive verification space and [future works section ref] highlights next steps that can be taken using the LLVM-IR deductive verifier.


#pagebreak()




= Outline

- intro sketch
  - why is llvm deductive verification useful?
  - what methods will be used?
    - dedver
    - isabelle
    - LLVM-IR
  - research goals
  - include example

- Introduction
  - why software verification
  - which methods will be used (1-2 sentences why)
    - dedver
    - isabelle
    - LLVM-IR
  - research goals
  - motivating example
- Background
  - Deductive verification
  - Isabelle
  - LLVM(-IR)

- Introduction
  - software verification
    - why is it necessary?
    - what are some different methods
      - deductive verification
      - model checking
      - unit-testing, acceptance testing, model-based testing, etc.
  - deductive verification
    - underlying principles
      - Hoare logic (+ separation logic)
      - Floyd's method
    - why choose this for this thesis?
  - LLVM
    - why was it created?
    - why choose it for this thesis?
      - nearly all modern programming languages support compiling to LLVM
      - decompiling binaries to LLVM is relatively straight-forward
  - Isabelle
    - what does it do?
    - why choose it for this thesis?
 - what I'll do (research questions!)
  - outline of sections of thesis
    - background
    - LLVM-IR
    - implementation
- background
  - in-depth explanation of deductive verification
  - in-depth explanation of Isabelle (only the features I use!)
- LLVM-IR
  - describe syntax
    - program made up of functions
    - functions made up of instruction blocks
    - instruction blocks made up of a label, phi nodes, instructions, and terminal instructions
    - C -> LLVM-IR example
  - describe semantics
    - function executed -> first block executed
    - instructions executed sequentially
    - terminal instruction branches to a different block, or returns a value from the function
    - phi nodes assign values to a register depending on the previous block
- LLVM-IR in Isabelle (preliminary results)
  - how is syntax implemented
    - datatypes and type-synonyms
  - how are semantics implemented
    - interpreter over the IR
    - functions are executed from the first block onwards
    - blocks are executed by sequentially executing each instruction
    - flow is handled using terminator instructions, either executing another block or returning a value
    - instructions alter the state according to the semantics defined in the language reference#footnote("https://llvm.org/docs/LangRef.html")
  - ! the semantics cannot be verified to be accurate, so it is trusted: assumed to be correct !
- deductive verification of LLVM-IR (TODO)
  - flow-graph of blocks constructed
  - pre- and post-conditions for any diverging blocks
  - given the pre-condition of a block, show the post-condition of the next diverging endpoint holds
  - where to define these pre- and post-conditions
  - instructions have some effect on state - described in weakest precondition rules
  - verification condition generator takes the pre- and post-conditions, and provides goals to prove
  - only partial correctness
- related works
- planning for completion of the thesis
  - implement separation logic
  - support arrays
  - create control-flow graphs of functions
  - implement VCG for multiple blocks strung together
  - allow annotating blocks with pre- and post-conditions
    - determine diverging paths
    - instantiate phi-nodes based on previous blocks
  - create a translation tool from native LLVM-IR to IsabeLLVM
    - if time permits, create a parser for it within Isabelle
    - otherwise, a simple Rust script will do
    - perhaps also the other way around

    - define MVP
    - risk analysis

#pagebreak()

Introduction

Say we have a C function for multiplying two integers:
```C
int mult(int a, int b) {
    int result = 0;
    for (int i = 0; i < b; i++) {
        result += a;
    }
    return result;
}
```
How would one verify that the returned value is indeed equal to a and b multiplied together?


Software Verification

One way to go about verifying this result is using a software verification tool made for the program's source language.
Such tools are used to assert that specific conditions hold in the execution of a program.
For the given example, a reasonable option would be to use Frama-C.@dedver-framac
This is a mature platform that can be used to verify specifications written in ACSL (ANSI/ISO C Specification Language), for example:
```C
/*@
requires a * b < 2^32;
requires b >= 0;
ensures \result == a * b;
*/
int mult(int a, int b);
```

This specification contains two pre-conditions and a post-condition.
Specifically, the pre-condition states that the inputs multiplied together should not overflow and b should be non-negative, and the post-condition states that, if the pre-condition held, then the result of the function is equal to the two inputs multiplied together.

However, these conditions are not enough to prove the correctness of the program.
They only provide the goals for the correctness proof.
In order actually prove that the post-condition follows from the pre-condition, the actual program and control-flow has to be taken into account.

For Frama-C, this involves annotating parts of the implementation where the control-flow is non-linear.
In our example, this is the while-loop, which has to be annotated by a loop-invariant.
These are invariants that hold both at the start of the loop and after every single execution.
We might define the following loop-invariant:
```C
int mult(int a, int b) {
    int result = 0;
    /*@
    loop invariant 0 <= i <= b;
    loop invariant result == a * i;
    */
    for (int i = 0; i < b; i++) {
        result += a;
    }
    return result;
}
```

With that, Frama-C is able to verify that the result will be equal to ```C a*b```.
How this verification works under the hood is explained in.
However, what if we now want to use this function in a different programming language, for example in Rust or C`#`?
This would involve finding a new verification framework and writing new specifications in its semantics.
Is it there a way to use the same verification framework for many different languages?


There are two different, but similar, formal systems for this exact purpose.
These are Hoare logic, a deductive system based on axioms and inference rules@hoare-logic described in , and Floyd's method@floyd-method.

- difficult to assess whether a program always does what it's supposed to
- mostly based on Hoare Logic , sometimes 
- many existing verification tools for different languages


Note that there is a difference between the domain of the integers a and b in the code and the specification.
In the code, these are 32-bit integers, which means they have limits and can overflow when they become too high, while in the specification they are mathematical integers without bounds.

Deductive Verification

 Hoare Logic

Hoare logic forms the basis of a lot of program verification.

- pre-conditions define what is needed to execute successfully
- post-conditions define the expected result of successful execution
- "if P holds and we execute c, then Q holds afterwards"


 Floyd's Method

However, Hoare logic is not the only basis to be used for program verification.
Another method was defined by Floyd independently from Hoare.
Rather than defining an algebra like Hoare, Floyd's method views programs as flowcharts where each vertex represents a command being executed.
Verification conditions are defined as $V_c (P; Q)$ which assert that if $P$ holds and command $c$ is executed, then $Q$ will hold afterwards.@floyd-method


Separation Logic

- @separation-logic
- Extension with better reasoning for programs with pointers/dynamic memory allocation
- Axiomatic specification of memory operations @axiom-spec-memory-model

Existing Verifiers

Wow

 LLVM

- intermediate language for compilation
- supports many source languages as it's relatively simple to compile to
- many target architectures
- built-in optimizations
- example of LLVM program
- "How would we prove that this program is correct?"


Isabelle

- interactive theorem prover: allows user to specify theorems and prove them correct
- provides user with goals to be proven and tools to prove those goals
- allows user to create functions and datatypes
- theorems can incorporate these functions and datatypes
- example of Isabelle datatype, function, and proof




 Existing imperative program verifiers

- Framework for VCGs using theorem provers @vcg-via-tp
- Exporting from Isabelle to LLVM@peter-isabelle-to-llvm
- Verifying x86 binaries@peter-x86-verification

 Deductive verifiers

There exist many deductive verifiers for different purposes, based on different principles.
Some are based on separation logic, while others use verification condition generators.

Ones based on VCGs often use a frontend/backend architecture, where the frontend translates a verification problem into some intermediate language used in verification, and the backend extracts proof obligations and proves them.@dedver-viper
With this architecture, it becomes easier to support new languages for verification, as only a new frontend needs to be created rather than reimplementing all verification infrastructure.
This architecture aligns with that of LLVM-based compilers, which also use a separate frontend (translating the source language to the LLVM-IR) and backend (compiling the LLVM-IR to the target architecture).

This architecture is brought to separation-logic based verifiers by Viper. It is a verification infrastructure, consisting of an intermediate language and two internal verifiers. Its aim is to bring the frontend/backend architecture to separation logic based verifiers. It supports many different languages through separate frontends, including Rust, Java, and C.@dedver-viper
An example of such a front-end is VerCors. This is a verifier aimed at concurrent programs written in languages such as Java, OpenCL, and OpenMP.@dedver-vercors
It has a prototype implementation to support verification of LLVM-IR programs called VCLLVM, which is not yet production-ready.@vercors-llvm Its purpose is similar to that of this project: create a verifier for LLVM so that all languages compiling to LLVM are immediately supported.

Another separation-logic based verifier is VeriFast, aimed at verifying single- and multi-threaded C and Java programs.@dedver-verifast

Dafny has a similar approach with a key difference: instead of compiling programs to Dafny from their source language, programmers instead create programs in the Dafny language, verify them there, and then compile them from Dafny to their preferred language.@dedver-dafny

- RESOLVE@dedver-resolve
- Whiley@dedver-whiley
- Frama-C@dedver-framac
- KIV@dedver-kiv
- OpenJML@dedver-jml



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


Rough planning

- Better LLVM semantics
- Finish intro rules for instructions
- Support verification condition generation at the level of blocks
- Add method of specifying pre- and post-conditions for code blocks 
- Create flowchart view of code blocks
- Match up post-condition of one block with pre-condition of subsequent block for correctness proofs
- Support more LLVM instructions
- Support arrays
- Import/export from/to direct LLVM code

#pagebreak()

#bibliography("references.bib", style: "ieee")
