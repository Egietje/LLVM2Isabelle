= Related Work
<sec-related-work>

There exist quite a few deductive verifiers for specific purposes, toolchains, and languages.
Many of them only support a single language or language family.
For example, Frama-C focuses on the C language, with its WP plugin providing deductive verification of C programs based on weakest-precondition calculus just like our verifier.@dedver-framac

Others, like Viper, take an approach similar in philosophy to LLVM, where a common verification backend is established for which different frontends can be created to support new languages.@dedver-viper
Viper defines its own intermediate language which it is able to verify, making it possible to compile other languages to this language to verify them.
Its verification is based on verification condition generation or symbolic execution depending on the user's preferences.

Alongside first-party Viper frontends for specific languages like Python, Rust, and Go, there is also the VerCors frontend.@dedver-vercors
VerCors is a deductive verification tool made specifically for concurrent and parallel programs, supporting a variety of source languages like Java and OpenCL.
Interestingly, there exists a project within VerCors, PALLAS, to support the verification of LLVM-IR.@vercors-llvm
However, this project is still being worked on and not ready to be used.

Dafny flips this logic, instead providing a source language to create and verify programs in, which can then be compiled to different programming languages.@dedver-dafny
It uses Boogie internally for verification, which itself comes with another intermediate verification language.
While this approach works well for new programs that are verified from the start, this does not address the need to verify existing programs.

Like Viper, $KK$ is a semantic framework that aims to solve the issue of creating a verification tool for each programming language.@dedver-kk
It uses the deductive proof assistant KIV which is also based on weakest precondition calculus.@dedver-kiv
$KK$ allows describing the syntax and semantics of languages, from which algebraic specifications to be used in KIV can be derived.

All previously mentioned verifiers mainly focus on verifying programs using their source code.
Of course, there are also cases where a program's source code is no longer available, but its binary needs to be verified.
There exist different verifiers for these purposes, such as for memory preservation of x86-64 binaries based on symbolic execution and Floyd-style verification.@peter-x86-verification
A somewhat related verifier has also been created to check source-level specifications within the produced x86 binary, based also on Floyd's method.@dedver-x86-source

In conclusion, most if not all existing deductive verification tools involve similar methods as used in this thesis: weakest precondition calculus, Hoare logic, Floyd-style verification, and/or verification condition generation.
Additionally, many of them aim to tackle the same problem: how to get around the need to define new verifiers for each programming language.
This thesis differs from most literature in the way it aims to solve this problem, by creating a verifier for LLVM-IR, which most programming languages can be compiled to.
Furthermore, due to its low-level nature, it is relatively easy to decompile program binaries into LLVM-IR.
While other initiatives for this purpose exists, they are not yet in a production-ready state.

