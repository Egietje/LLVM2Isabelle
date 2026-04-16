#import "functions.typ": fig

= Introduction

Software plays a crucial role in many safety-critical areas.
It helps steer cars and planes, controls traffic lights and bridges, and synchronizes power plants and electrical grids.
With that, its correct functioning is of the utmost importance, as the consequences are great when such software fails.
Common software testing methods, for example those involving static or dynamic analysis, only reveal the (potential) presence of bugs, but cannot prove their absence.
To assert the absence of bugs, formal verification of the software is required.

A simple example of a program to be verified is shown in @lst-mult-impl.
The program, written in C, consists of the function `mult`, which takes two parameters `a` and `b`, and should result in an integer of these inputs multiplied together.
Its implementation is not quite straight-forward as it does not use any multiplication instruction, instead relying on a for-loop with repeated additions.
While simple, the program helps illustrate the pros and cons of conventional testing and formal verification.
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

Such programs are commonly tested with dynamic analysis: the program is run for various test-cases with different inputs, and the results are compared to their expected outcomes.
These tests are great at quickly identifying major implementation mistakes, however they do not cover all possible inputs and thus cannot assert that the implementation is always correct.
Furthermore, they might be analyzed using static analysis tools which help identify common mistakes, but do not know about how the program is supposed to work.
Both techniques are useful in their own right, but are not powerful enough to assert a program always works as intended.

As stated previously, formal verification methods are required to assert whether a program is always correct.
For example, model-checking can be used to assert correctness for all possible states of an abstract model of the program.
While effective, this method is not very efficient.
It requires the creation of a model, which itself has to be correct, as well as exploring all possible states of said model, which can quickly become infeasible as the model grows.
For our example, this involves trying all possible values for `a` and `b` combined, yielding $2^64$ verification conditions.

In contrast, deductive verification does not suffer these shortcomings.
It operates on an annotated version of the code of the program and proves correctness using mathematical reasoning.
Essentially, it boils down to symbolically executing the program, keeping track of how the execution state and control flow are impacted, and proving that the specified conditions hold for all possible execution states. 
Note that this does not happen through exhaustively checking all possible execution states as with model checking, but rather using a single symbolic representation that contains all states.

We will create a new deductive verification tool in this thesis, as its formal mathematical basis allows for the most efficient and rigorous verification of the described approaches.
To use this method, a target language has to be chosen for which the structure and semantics have to be formally defined.
Furthermore, a formal back-end has to be chosen in which these definitions can be created and the deductive verification's proof system can be described.


== Verification Targets

Deductive verification can be done at various stages in compilation of software.
It might be done with the source code, with fully compiled binaries, or with some intermediary between these stages.
Performing verification on source code comes with the advantage that it is relatively easy to integrate the verification into the program, for example with in-line verification instructions, but this comes at the cost of the verification being tied to the specific programming language the software was written in.
Targeting a lower level like machine instructions gets around this issue and is the closest to verifying the actual execution of a program, as compilation might introduce artifacts not present in source code, but means that only a single target is verified, tying the verification to a specific architecture.
In both cases, changing the language or architecture the verification is done with means porting the verification to a different target as well, introducing more overhead for such tasks.

In this thesis, we will target LLVM-IR.
This language lives between a program's source-code and compilation target, being part of the LLVM compilation framework.
One if its goals is to allow language-engineers to only target a single compilation representation, LLVM-IR, while supporting many different target architectures, including x86, ARM, and RISC-V.
Another goal is to allow developers working on new hardware targets to implement a single back-end for LLVM-IR, automatically enabling support for all languages that compile to it.
These goals has been mostly achieved, with some target-specific intrinsics and differences being present in LLVM-IR.
Our tool will have to deal with these differences properly when encountered.
As such, one does not write programs directly in LLVM-IR, but any supported language can be compiled to it.
We can use this to our benefit: once functional, our tool will immediately support software written in a wide range of source languages and targeting many target architectures.


== Verification Back-end

Finally, the chosen formal verification back-end for this thesis is Isabelle/HOL.
This is an interactive theorem prover that allows users to specify theorems using higher-order logic and mathematically prove them to be correct.
Whenever a new theorem is created, it gives the user proof (sub-)goals that have to be proven for the theorem to be accepted.
Different tools and solvers are provided to the user which aid in simplifying, breaking up, and eventually proving these goals.
Furthermore, it is possible to define custom proof methods for specific tasks using the Eisbach infrastructure.
Isabelle is also a functional programming language, allowing users to create their own datatypes and functions, and letting them use these in their lemmas.
All of these features combined make Isabelle well-suited to defining the structure and semantics of LLVM-IR, a deductive verification proof-system, and tools that use these formal descriptions, creating an effective deductive verifier for LLVM-IR.


== Research Goals

With that, the main research goal of this thesis is:\
`RG` - _Creating a deductive verification tool for partial correctness of LLVM-IR programs within Isabelle/HOL._

This can be achieved through the following sub-goals, producing a minimum viable product:\
`SG1` - _Defining the structure and semantics of a targeted subset of LLVM-IR in Isabelle to represent LLVM-IR programs in Isabelle._\
`SG2` - _Implementing Hoare-Floyd style deductive verification infrastructure that works with these semantics._\
`SG3` - _Creating tools to efficiently and effectively verify LLVM-IR programs._\
`SG4` - _Using these tools on selected examples to show their efficacy._

On top of those main sub-goals, we have several extension goals:\
`EG1` - _Extending the defined subset of LLVM-IR to support more of its features, instructions, and intrinsics, such as floating-point values or arrays._\
`EG2.1` - _Creating a tool to port LLVM-IR output into the verifier's representation and vice versa._\
`EG2.2` - _Verifying importing and exporting LLVM-IR is a fully lossless process._\
`EG3` - _Extending the verifier to prove total correctness rather than partial correctness._\
These extension goals are not strictly necessary to achieve the main research goal, but do enhance the functionality of the created tool.


== Proposal Contents

Work has already begun implementing the tool described in this proposal.
Specifically, goals `SG1`, `SG2`, and `SG3` have been mostly achieved with some room for improvement, described in @sec-preliminary-results.
This means the proposal is larger than it would otherwise have been.

Furthermore, @sec-background gives background information on techniques and technologies used in this thesis,
@sec-related-work covers existing literature in this space to take inspiration from,
and finally @sec-planning gives a rough planning on how work will proceed from this point forward to complete the proposed tool, as well as some implementation risks and mitigation strategies should they arise.
