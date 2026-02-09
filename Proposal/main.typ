
#let title-page(title:[], email:[], name:[], fill: yellow, body) = {
  set page(margin: (top: 1.5in, rest: 2in))
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

#show: body => title-page(
  title: "LLVM verification in Isabelle",
  email: "mailto:t.s.kas@student.utwente.nl",
  name: "Thomas Kas",
  body
)

#set page(margin: 1.5cm)
#set par(
  justify: true,
)
= Topic

LLVM is an intermediate language for compilers that serves as a backend for compilation to many different CPU architectures.
It abstracts from architecture-specific CPU instruction to provide a set of common instructions for which it is relatively easy to create a compiler for programming languages.
From there, LLVM has compilers to many different architectures with specific optimizations.
This means creating a compiler from your language to LLVM is all that is needed to be able to compile to most existing architectures, rather than having to create compilers for each architecture. 
The aim of my thesis is to import LLVM snippets into Isabelle in order to create formal proofs for arbitrary programs written in languages that can be compiled to LLVM.

= Related work

Much has been written about software verification.
This section covers the basic principles defined by Hoare and Floyd (@sec-hoare-logic and @sec-floyd-method), extensions opens those bases (@sec-separation-logic and @sec-ver-con-gen), different ways of modeling memory in proofs (@sec-memory-models), and finally different existing program verifiers and their underlying principles (@sec-existing-verifiers).

== Hoare Logic <sec-hoare-logic>

Hoare logic forms the basis of a lot of program verification.
It defines methods of reasoning about programs through the connections between preconditions $P$, programs $Q$ (now commonly $c$), and results of execution (or postconditions) $R$ (now commonly $Q$).
This means that as long as the intended execution of the program can be defined in terms of assertions about the values of variables at some point in execution, Hoare logic can be used to prove the partial correctness of such programs.
However, the logic defined by Hoare cannot be used to proof termination of programs, and as such can only prove partial correctness.@hoare-logic
As such, extensions and alternate methods have been defined, such as separation logic (see @sec-separation-logic) and verification condition generators (see @sec-ver-con-gen).


== Floyd’s Method <sec-floyd-method>

However, Hoare logic is not the only basis to be used for program verification.
Another method was defined by Floyd independently from Hoare.
Rather than defining an algebra like Hoare, Floyd's method views programs as flowcharts where each vertex represents a command being executed.
Verification conditions are defined as $V_c (P; Q)$ which assert that if $P$ holds and command $c$ is executed, then $Q$ will hold afterwards.@floyd-method


== Separation Logic <sec-separation-logic>
== Verification Condition Generators <sec-ver-con-gen>


== Memory Models <sec-memory-models>
Axiomatic specification of memory operations @axiom-spec-memory-model


== Existing imperative program verifiers <sec-existing-verifiers>

Framework for VCGs using theorem provers @vcg-via-tp

Exporting from Isabelle to LLVM@peter-isabelle-to-llvm

Verifying x86 binaries@peter-x86-verification

=== Deductive verifiers

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

RESOLVE@dedver-resolve

Whiley@dedver-whiley

Frama-C@dedver-framac

KIV@dedver-kiv

OpenJML@dedver-jml



= Preliminary results

Work has already begun defining the semantics of LLVM in Isabelle and creating a verification condition generator based on Floyd's assertion method using weakest precondition mechanics.


== LLVM semantics

Part of the LLVM-IR's AST has been defined as datatypes in Isabelle.
With this part of the AST, functions made up of instruction blocks can be executed.

The operational semantics are defined as follows:
- Functions contain multiple labeled instruction blocks and one unlabeled block to be executed first.
- Instruction blocks have a list of regular instructions to be executed in order and one terminator instruction that impacts execution flow.
- Instructions are executed according to their specification in the LLVM Language Reference Manual.#footnote("https://llvm.org/docs/LangRef.html")

Execution of any single instruction takes in some state and produces a state.
This state is defined as follows:
- It is a triple of registers, a stack, and a heap.
- The stack and heap have the same underlying memory definition: a list of values. They are addressable using indices in these lists.
- Registers are a mapping from a name to a value. (TODO: change 'registers' to 'SSA-values' in implementation and report)

The regular instructions currently (partly) implemented are:
- alloca - allocates a new address in the stack, and stores the address in some register.
- store - stores a value at some address in the stack or heap.
- load - loads a value from some address in the stack or heap into a register.
- icmp - compares two values (32/64 bit signed/unsigned integers) and stores the result in a register as a single bit (boolean).
- add - adds two values (32/64 bit signed/unsigned integers) and stores the result in a register (another 32/64 bit integer or a poison value if an overflow occurred).
- phi - store a value from a list of possible values into a register depending on the instruction block that lead to this block.

The terminator instructions implemented are:
- br - branch to a different instruction given its label (could always be the same label, or switch based on a boolean value in some register).
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
    store i32 (val (vi32 0)) (ptr (reg ''1'')) (Some 4),
    store i32 (val (vi32 1)) (ptr (reg ''2'')) (Some 4),
    load ''5'' i32 (ptr (reg ''2'')) (Some 4),
    icmp ''6'' False comp_ne i32 (reg ''5'') (val (vi32 0))],
    br_i1 (reg ''6'') ''7'' ''9''
  )"

definition p7 :: "llvm_instruction_block" where
  "p7 = ([
    store i32 (val (vi32 1)) (ptr (reg ''4'')) (Some 4),
    load ''8'' i32 (ptr (reg ''4'')) (Some 4)],
    br_label ''10''
  )"

definition p9 :: "llvm_instruction_block" where
  "p9 = ([],
    br_label ''10''
  )"

definition p10 :: "llvm_instruction_block" where
  "p10 = ([
    phi ''11'' i32 [(''7'', reg ''8''), (''9'', val (vi32 0))],
    store i32 (reg ''11'') (ptr (reg ''3'')) (Some 4),
    load ''12'' i32 (ptr (reg ''3'')) (Some 4)],
    ret i32 (reg ''12'')
  )"

definition phi_main :: "llvm_function" where
  "phi_main = func (func_def ''main'' i32) pmain [(''7'', p7), (''9'', p9), (''10'', p10)]"
```

This can be executed as follows, which gives the proper return value:
```isabelle
value "execute_function empty_state phi_main"
```


== Weakest precondition mechanics

Taking inspiration from Hoare logic, 
To reason about the execution of 


= Rough planning

- Better LLVM semantics (e.g. register overrides)
- Support verification condition generation at the level of blocks
- Add method of specifying pre- and post-conditions for code blocks 
- Create flowchart view of code blocks
- Match up post-condition of one block with pre-condition of subsequent block for correctness proofs
- Support more LLVM instructions
- Import/export from/to direct LLVM code

#pagebreak()

#bibliography("references.bib", style: "ieee")
