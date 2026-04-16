#import "functions.typ": fig

= Preliminary Results
<sec-preliminary-results>

This section covers the preliminary results from work already done.
Specifically, it details how `SG1` has been achieved in @sec-llvm-in-isabelle,how much has been achieved for `SG2` in @sec-ver-infra, and how `SG3` and `SG4` will be tackled in @sec-ver-tools and @sec-ver-example.

== LLVM-IR in Isabelle
<sec-llvm-in-isabelle>

A subset of LLVM-IR's structure and semantics have been defined in Isabelle.
The chosen subset covers basic language features that allow simple programs, such as the `mult` function from @lst-mult-llvm, to be described and executed.
Specifically, the structure of some instructions, basic blocks, functions, and programs have been defined, as well as their semantics.

The structure has been defined as a deep embedding, using datatypes to represent its AST.
This means that representing LLVM-IR using our representation requires a conversion, which a shallow embedding would not necessarily have required.
However, this comes with the benefit of being more flexible in terms of what can be done with the embedded programs.
A shallow embedding would have been more limited in the ways we could analyze, execute, and reason about embedded programs, which would have relied on built-in Isabelle features.

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
It is made up of functions implementing different execution levels, each being made up of the functions of the level below it:
- state operations: reading from and writing to memory and registers,
- instructions: performing state operations and applying some additional logic,
- basic blocks: consecutively executing instructions, its definition is shown in @lst-block-exec,
- functions: executing basic blocks and handling control-flow. Note that this execution function is partial, which means it does not guarantee termination. It is possible for functions to loop forever.

At the core of this interpreter lies the `state`, a triple of registers, stack memory, and heap memory.
State operations directly interact with its internal definition, providing abstractions that make the easier to operate on and reason about.

Furthermore, it uses the `result` datatype, which can either represent successful execution containing some value, or erroneous execution containing an error message.
Monad laws have been defined on top of it, making it easy to chain together function calls that might produce an error.
This monad short-circuits execution when an error is encountered, or flows naturally when execution is successful.
An error is produced when some execution requirement of an instruction is not met, such as when the `load` instruction tries to load a value from uninitialized memory.

Together, the defined structure and semantics can be used to execute functions made up of the supported instructions.

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

== Verification Infrastructure
<sec-ver-infra>

Building on the defined semantics, we have already implemented verification infrastructure to achieve most of `SG2`.
At its core are weakest pre-conditions defined for the `result` type, shown in @lst-wp-def.
These can be used in lemmas to prove that given some pre-conditions, execution of some command `c` will always be successful, and some post-conditions hold for the return value of `c`.

#fig(```isabelle
definition wp :: "'a result ⇒ ('a ⇒ bool) ⇒ bool" where
  "wp c Q = (case c of ok v ⇒ Q v | err _ ⇒ False)"
```,
  [`wp` Definition]
)<lst-wp-def>

These conditions are specified using abstractions over the state for easy verification, `memory_`$alpha$ and `register_`$alpha$.
These abstractions can be used to assert whether some memory address is allocated or initialized or not, whether it contains a specific value, and whether specific registers contain any or a specific value.

For example, consider the `load` instruction.
It reads a value stored in memory from a pointer stored in a register into another register.
As such, to execute successfully, it needs the given register to contain a pointer, and corresponding memory address to be allocated and initialized.
Furthermore, when executed successfully, it leaves memory exactly as it was before, but updates a single register to the value read from memory.
These facts have been described using our weakest precondition definition in @lst-load-wp.
Here, the assumptions of the lemma are the pre-conditions, the first argument for `wp` is the command, and the second argument is the post-condition.

#fig(
```isabelle
lemma
  assumes "register_α s pointer = Some (addr a)"
  and "memory_α s a = Some (Some v)"
  shows "wp
    (execute_load name pointer s)
    (λs'. memory_α s' = memory_α s
    ∧ register_α s' = (register_α s)(reg name := Some v))"
```,
  [`load` Weakest Precondition Lemma]
)<lst-load-wp>

Such lemmas have been defined from the bottom up for all state operations, instructions, and basic blocks.
By combining these lemmas with a consequence rule it is possible to use them in proofs for higher-level weakest preconditions, yielding new sub-goals for each of the preconditions of the constituent commands.

For example, `execute_load` is made up of the state operations `get_register`, `get_memory`, and `set_register`, along with some logic to ensure `get_register` returned an address.
Applying their respective weakest pre-condition lemmas combined with the consequence rule, yields the following sub-goals for the lemma in @lst-load-wp:
- `get_register`'s precondition:\ `register_α s pointer ≠ None`
- `get_register`'s postcondition and proving its value is an address:\ `register_α s pointer = Some x ⟹ ∄xa. x = addr xa ⟹ False`
- `get_memory`'s precondition following from `get_register`'s postcondition:\ `register_α s pointer = Some x ⟹ x = addr xa ⟹ memory_α s xa ≠ None`
- `get_memory`'s precondition:\ `register_α s pointer = Some x ⟹ x = addr xa ⟹ memory_α s xa ≠ Some None`- `register_α s pointer = Some x ⟹ x = addr xa ⟹ memory_α s xa = Some (Some xb) ⟹ register_α xc = (register_α s)(reg name ↦ xb) ∧ memory_α xc = memory_α s ⟹ memory_α xc = memory_α s ∧ register_α xc = (register_α s)(reg name ↦ v)`\ (`get_register` and `get_memory`'s postconditions, with `execute_load`'s postcondition)
All of these can be proved to hold given the assumptions, so `execute_load` has been proven to always execute correctly given these assumptions. Moreover, given successful execution, the postcondition has also been proven to hold for the returned state.

The workings of these weakest preconditions are essentially the same as that of Hoare triples.
The connection becomes clear with our weakest preconditions expressed as `P ⟹ wp c Q`, representing the Hoare triple `P c Q`.
Because most literature is based on Hoare triples and being simpler to define, we have created a simple definition to create Hoare triples in terms of weakest preconditions.
This unfolds `hoare P c Q` to the form `P s ⟹ wp (c s) Q`, as shown in @lst-hoare-def.
What this means intuitively, is that we assert that for all states that satisfy the precondition `P`, applying the command `c` to that state yields a new state that satisfies the postcondition `Q`.

#fig(
  ```isabelle definition "hoare P c Q ≡ (∀s. P x ⟶ wp (c s) Q)"```, [Hoare Triple Definition]
)<lst-hoare-def>

With that, Hoare triples can be defined for the execution of basic blocks.
Using our weakest precondition rules, we can obtain sub-goals to prove that the basic block executes successfully, as well as an abstract representation of the state reached after the block has been executed.

On top of that, we have defined methods to extend this verification to entire functions based on Floyd's method, including creating a control-flow graph.
However, these remain unfinished, so we will need to finish these going forward to fully achieve `SG2`.

== Verification Tools
<sec-ver-tools>

Work has begun creating verification tools to use our Hoare triples intuitively and effectively.
For example, Eisbach methods have been created to automatically prove specific sub-goals for different instructions as well as handle multi-block proofs.
These are already effective at clearing sub-goals of the instructions within a block, leaving the user to deal with just the final proof goal, or any failing sub-goals which indicate missing pre-conditions.
While mostly functional, these remain incomplete and depend on the completion of `SG2` to finish, which means there is still some work to do to achieve `SG3`.


== Verification of Example programs
<sec-ver-example>

Finally, some simple example programs have been encoded into our LLVM-IR structure.
These have not been fully verified as we need `SG2` and `SG3` to be completed before that, but their basic blocks have been useful in testing the functionality of what has been implemented already.
One such program is the `mult` function from @lst-mult-llvm.
Of course, more programs of similar or higher complexity need to be defined and verified before `SG4` can be considered achieved.

