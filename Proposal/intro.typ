#import "functions.typ": fig

= Introduction

As software is used in more and more safety-critical areas, the importance of its verification grows rapidly.
It is used to control modes of transportation like cars and planes, critical infrastructure like power plants and electrical grids, and many other areas.
If such software fails, the consequences are great, which means verifying that such pieces of software work as intended has become crucial.
The goal of this thesis is to create a verification tool for most software regardless of source language or target architecture by strategically choosing an optimal verification method and target combination.


== Motivating Example

A simple example of a C program to be verified is shown in @lst-mult-impl.
It consists of only the function `mult`, which takes two parameters `a` and `b`, and should result in an integer of these inputs multiplied together.
Its implementation is not quite straight-forward as it does not use any multiplication instruction, instead relying on a for-loop with repeated additions.
As such, verification of even such a relatively simple program requires in-depth understanding of the semantics of C.
#fig(
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


== Verification Methods

This verification can be done through various different methods.
One such method is model checking, where a model of the system the software acts upon is created and used to verify the software functions correctly in some or all possible states of the model.
Another method is dynamic analysis, where (part of) the software is run and its results or execution states are checked against some expected outcome or allowed bounds, commonly implemented in unit or acceptance tests.
In contrast to dynamic analysis, static analysis techniques can be used to identify issues without running the software. The issues it can identify usually consist of common programming mistakes and is limited in its scope, lacking the strength to verify an implementation matches the expected behavior.
Finally, there is deductive verification, which mathematically verifies correctness using logical reasoning based on pre- and post-conditions.
It is using this last method, deductive verification, that a new verification tool will be created in this thesis, as its formal mathematical basis allows for the most rigorous verification of these approaches.


== Verification Targets

Deductive verification can be done at various stages in compilation of software.
It might be done with the source code, with fully compiled binaries, or with some intermediary between these stages.
Performing verification on source code comes with the advantage that it is relatively easy to integrate the verification into the program, for example with in-line verification instructions, but this comes at the cost of the verification being tied to the specific programming language the software was written in.
Targeting a lower level like machine instructions gets around this issue and is the closest to verifying the actual execution of a program, as compilation might introduce artifacts not present in source code, but means that only a single target is verified, tying the verification to a specific architecture.
In both cases, changing the language or architecture the verification is done with means porting the verification to a different target as well, introducing more overhead for such tasks.

This thesis aims to create a tool for deductive verification at a level between these two, namely LLVM-IR.
This is the intermediate representation of LLVM, a compilation framework that has separate front-ends and back-ends for different source languages and target architectures.
It allows language-engineers to only target a single compilation representation, LLVM-IR, while supporting many different target architectures, including x86, ARM, and RISC-V.
Furthermore, it allows developers working on new hardware targets to implement a single back-end for LLVM-IR, automatically enabling support for all languages that compile to it.
For our proposed verification tool this means that, once functional, it will support software written in a wide range of source languages and targeting many target architectures.


== Verification Back-end

Finally, the chosen formal verification back-end for this thesis is Isabelle/HOL.
This is an interactive theorem prover that allows users to specify theorems using higher-order logic and mathematically prove them to be correct.
Whenever a new theorem is created, it gives the user proof (sub-)goals that have to be proven for the theorem to be accepted.
Different tools and solvers are provided to the user which aid in simplifying, breaking up, and eventually proving these goals.
Furthermore, it is possible to define custom proof methods for specific tasks using the Eisbach infrastructure.
Isabelle is also a functional programming language, allowing users to create their own datatypes and functions, and letting them use these in their lemmas.
All of these features combined make Isabelle well-suited to defining the structure and semantics of LLVM-IR and creating verification tools that are straight-forward to use on top of that.


== Research Goals

With that, the main research goal of this thesis is:\
`RG` - _Creating a deductive verification tool for partial correctness of LLVM-IR programs within Isabelle/HOL._

This can be achieved through the following sub-goals, producing a minimum viable product:\
`SG1` - _Defining the semantics of a targeted subset of LLVM-IR in Isabelle._\
`SG2` - _Implementing deductive verification infrastructure that works with these semantics._\
`SG3` - _Creating tools to efficiently and effectively verify LLVM-IR programs._\
`SG4` - _Using these tools on some program to show its efficacy._

Once these goals are achieved and an MVP has been produced it can be extended with multiple extension goals, such as:\
`EG1` - _Extending the defined subset of LLVM-IR to support more of its features, instructions, and intrinsics._\
`EG2` - _Creating another tool to port LLVM-IR output into the verifier and vice versa, preferably using Isabelle to prove it can losslessly port LLVM-IR programs._\
`EG3` - _Improving the backend using advanced verification principles, such as separation logic, to make verification easier._\
`EG4` - _Extending the verifier to prove total correctness rather than only partial correctness._\
These extension goals are not strictly necessary to achieve the main research goal, but do enhance the functionality of the created tool.


== Proposal Note

Work has already begun implementing the tool described in this proposal, following the philosophy that practical experience is a great way to better understand choices made in existing literature.
As such, in addition to giving background information on the techniques and technologies this thesis will incorporate, this proposal also describes the work that has already been done towards the goals of the thesis.
This makes the proposal slightly larger than other similar research proposals, as it covers this work in some detail.

Specifically, @sec-background gives background information on techniques and technologies to be used for this thesis,
@sec-preliminary-results covers preliminary results from the work that has already been done,
@sec-related-work covers existing literature in this space to take inspiration from,
and finally @sec-planning gives a rough planning on how work will proceed from this point forward to complete the proposed tool, as well as some implementation risks and mitigation strategies should they arise.
