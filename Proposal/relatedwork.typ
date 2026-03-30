= Related Work (WIP)
<sec-related-work>

This section will cover, among others, the following work:

- Framework for VCGs using theorem provers @vcg-via-tp
- Exporting from Isabelle to LLVM@peter-isabelle-to-llvm
- Deductive verification backend@dedver-viper
- Write program in Dafny, verify, and then compile to your preferred language@dedver-dafny

Deductive Verifiers:
- Verifying x86 binaries@peter-x86-verification
- RESOLVE@dedver-resolve
- Whiley@dedver-whiley
- Frama-C@dedver-framac
- KIV@dedver-kiv
- OpenJML@dedver-jml
- VeriFast@dedver-verifast
- VerCors@dedver-vercors
  - WIP LLVM frontend@vercors-llvm
...

/*

 Existing imperative program verifiers


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





*/
