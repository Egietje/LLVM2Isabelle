#import "functions.typ": fig
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import fletcher.shapes: diamond

== Deductive Verification
<sec-ded-ver>

Deductive verification is a method to mathematically verify that a concrete implementation of a program satisfies specified conditions.
There exist many different deductive verifiers for different languages and toolchains, but they share the following foundational principles.


=== Hoare Triples
<sec-hoare-triples>

At the core of deductive verification lie pre-conditions, commands, and post-conditions.
The combination of the three, known as Hoare triples, allows one to reason about programs.
The pre-conditions, $P$, represent some conditions that have to hold for the command, $c$, to execute properly, while the post-conditions, $Q$, represent the intended result of the command.

#fig(
  ```C
/*@
requires a * b < 2^31
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
Specifically, the pre-conditions state that the inputs `a` and `b` multiplied should not exceed the signed 32-bit integer limit and `b` should be non-negative for the function to execute properly.
If this holds, then the post-condition states that the result will be the inputs `a` and `b` multiplied.

To prove that a post-condition follows from the pre-conditions and the command, the semantic meaning of the command has to be described formally.
Consider again the implementation of the `mult` function in @lst-mult-impl.
To prove anything about this function, the prover needs to know what exact effects the instructions have on the execution state: how values of the `int` type behave, how assigning variables behaves, how different operations such as `++` and `+=` interact these values, and how control-flow is impacted by the `for`-loop and `return` keyword.

Once the prover knows the semantics of different instructions, it can assume the pre-conditions hold for the inputs and execute the instructions of a program symbolically, keeping track of how execution state and flow have been impacted thus far.
When a return instruction is reached, the post-condition can be checked on the returned value and reached execution state.
If it holds for all possible executions, then the program satisfies the specification and is verified deductively.
Note that this only proves partial correctness: it might be possible for the program not to terminate, but if it does, then the post-condition holds.


=== Floyd's Method
<sec-floyds-method>

With that, it is crucial to know the control-flow of all possible executions of a program, as it does not suffice to show correctness for only some executions.
For this purpose, Floyd's method can be applied.
This involves creating a control-flow graph of the program and creating specifications for all branch-points in said graph.
What results is a number of instruction blocks, each annotated with some pre-conditions, and a graph containing the flow between these blocks.

Verification of programs using the annotated instruction blocks and their flow becomes straight-forward.
Starting with the first block, its pre-conditions are assumed to hold, and its instructions are executed symbolically.
From there, the resulting execution state has to be shown to satisfy the pre-conditions of all possible next instruction blocks.
This has to be repeated for all of the annotated blocks.
Finally, whenever a block ends by returning, the post-condition of the program has to be shown to hold from the pre-condition and execution of the block.
When this is done, the program has been verified to be (partially) correct.

Consider @lst-mult-impl-spec.
Since the for-loop represents a branch-point in control-flow, some pre-conditions have to be specified for these instruction blocks.
For this purpose, loop invariants have been added to the for-loop in the `mult` function.
The pre-conditions of the function become the pre-conditions of the initial instruction block, while the loop invariants become the pre-conditions for the loop and final instruction blocks.
This is visualized in @lst-mult-flow.

#fig(```C
/*@
requires a * b < 2^31;
requires b >= 0;
ensures \result == a * b;
*/
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
```,
  [C `mult` Function Implementation Annotated with ACSL Specifications]
)<lst-mult-impl-spec>

#fig([#diagram(
	  node-stroke: 1pt,
    node((0, 1), align(left)[int result = 0; \ int i = 0;]),
    node((0, 2), align(left)[result += a; \ i++;]),
    node((0, 3), align(left)[i < b?], shape: diamond),
    node((0, 4.5), align(left)[return result;]),

    edge((0,0), (0,1), "->", [`a` $*$ `b` $<$ $2^31$ \ `b` $>=$ $0$], label-side: left),
    edge((0,1), (0,2), "->", [$0$ $<=$ `i` $<=$ `b` \ `result` $=$ `a` $*$ `i`], label-side: left),
    edge((0,2), (0,3), "->"),
    edge((0,3), (1,3), (1,2), (0,2), "->", [`i` $<$ `b` \ $0$ $<=$ `i` $<=$ `b` \ `result` $=$ `a` $*$ `i`], label-side: right),
    edge((0,3), (0,4.5), "->", [`i` $>=$ `b` \ $0$ $<=$ `i` $<=$ `b` \ `result` $=$ `a` $*$ `i`], label-side: left)
  )],
  [Annotated `mult` Control Flow Graph]
)<lst-mult-flow>

With that, the goal of the deductive verification infrastructure is to:
- allow users to specify pre-conditions per block of instructions with linear control-flow and a general post-condition,
- allow for the symbolic execution of instruction blocks with some assumed conditions, obtaining the execution state,
- allow proving that the pre-conditions of all consequent instruction blocks hold for some obtained execution state, or the post-condition in case the block returned some value.
