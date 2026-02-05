
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
With this part of the AST,  can be passed to  to execute them.
Such invocations serve as the basis of proofs.

The operational semantics are defined as follows:
- Functions contain multiple labeled instruction blocks and one unlabeled block to be executed first.
- Instruction blocks have a list of regular instructions to be executed in order and up to one terminator instruction that impacts execution flow.
- Instructions are executed according to their specification in the LLVM Language Reference Manual.#footnote("https://llvm.org/docs/LangRef.html")
- Execution state is defined as a triple of registers, a stack, and a heap.

The regular instructions currently (partly) implemented are:
- alloca
- store
- load
- icmp
- add
- phi

The terminator instructions implemented are:
- br
- ret


== Weakest precondition mechanics



= Rough planning

#pagebreak()

#bibliography("references.bib", style: "ieee")
