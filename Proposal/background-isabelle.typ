#import "functions.typ": fig

== Isabelle
<sec-isabelle>

Isabelle/HOL (referred to as just Isabelle from here) is an interactive theorem prover with higher-order logic features, allowing users to create and prove correct theorems consisting of lemmas.
These lemmas can contain several assumptions, and define a single conclusion from the assumptions.
Whenever a new lemma is defined using the keyword `lemma`, Isabelle prompts the user to prove one or more proof goals.
With provided tools, the user is able to simplify, break up, rewrite, and eventually prove these goals (assuming they are correct).
Once all proof goals have been proven, the lemma is added as correct to a theorem.

Isabelle is also a functional, statically-typed language, allowing users to create functions that can then be used in lemmas.
Functions can have several parameters of specific types, and always produce a result of a single type.
They can use pattern matching over the parameters to specify different function definitions depending on the input.
Simple recursive functions created using the keyword `fun` are automatically proven to terminate, but some non-recursive functions created using the keyword `function` or `partial_function` require the user to prove they terminate.
As an example, the `mult` function has been written in Isabelle as a recursive function over the second parameter in @lst-mult-isabelle.
Here, the parameters are natural numbers, which are defined as zero, `0`, or recursively as the successor of another natural number, `Suc n`.
If the second parameter is zero, then the result of the function is also zero, but if it is the successor of a natural number, `b`, the function recurses to `mult a b` (`a` being the first parameter) and adds `a` to that.

#fig(
  ```isabelle
fun mult where
  "mult a 0 = 0"
| "mult a (Suc b) = a + mult a b"
  ```,
  [Recursive Function `mult` in Isabelle]
)<lst-mult-isabelle>

Proving that the `mult` function indeed multiplies the two inputs is possible by creating a lemma that states `mult a b` is equal to `a * b`, and proving the resulting proof goals.
This has been done in @lst-mult-proof.
The proof works as follows:
- applying induction over `b` using `apply (induction b)`, to get two new sub-goals:
  - the base case: `mult a 0 = a * 0`
  - the inductive step: $⋀$`b. mult a b = a * b` $⟹$ `mult a (Suc b) = a * (Suc b)`
- applying the simplifier to the base case using `apply simp`, which internally does the following to the sub-goal:
  - rewrite `mult a 0` to its definition: `0`,
  - rewrite `a * 0` to `0` using an internal definition of multiplication of natural numbers,
  - prove the resulting sub-goal `0 = 0` by reflection.
- applying the simplifier to the inductive step using `apply simp`, which does the following:
  - rewrite `mult a (Suc b)` to its definition `a + mult a b`,
  - use the assumption (which is specified to hold for any b) to rewrite `mult a b` to `a * b`,
  - rewrite `a * (Suc b)` to `a + a * b` using an internal definition of multiplication of natural numbers,
  - prove the resulting sub-goal `a + a * b = a + a * b` by reflection.
- the lemma is added to the theorem with `done`, which can only be done when no sub-goals are left over.

#fig(
  ```isabelle
lemma "mult a b = a * b"
  apply (induction b)
  apply simp
  apply simp
  done
```,
  [Lemma for `mult` Function]
)<lst-mult-proof>

Moreover, Isabelle allows user to create custom datatypes to be used in functions and lemmas using the keyword `datatype`.
These datatypes can have any number of uniquely-named constructors which can consist of any number of values of different types.
It is also possible for datatypes to contain generic types, which can be instantiated with some type whenever they are used.
Examples of a custom natural number and list datatype are shown in @lst-datatypes.
Here, `custom_nat` is defined as either `custom_zero`, representing zero, or `custom_succ custom_nat`, representing the successor of another `custom_nat`.
The value shown below it represents the natural number `2`.
Furtermore, `custom_list` uses a generic type `'a`, which is defined as either `custom_nil`, representing an empty list, or `custom_cons`, representing a value of `'a` prepended to another `custom_list` instantiated with the same generic type.
The value shown below it represents the list with `[0, 1]`.

#fig(
  ```isabelle
datatype custom_nat = custom_zero | custom_succ "custom_nat"
value "custom_succ (custom_succ custom_zero)"

datatype 'a custom_list = custom_nil | custom_cons "'a" "'a custom_list"
value "custom_cons custom_zero (custom_cons (custom_succ custom_zero) custom_nil)"
```,
  [Isabelle Datatype Examples]
)<lst-datatypes>

As previously mentioned, Isabelle provides different reasoning tools to simplify, break up, and prove sub-goals.
One such example is the Simplifier, as invoked in @lst-mult-proof, which supports higher-order rewriting.
Additional tools include the classical reasoner, classical tableau prover, Metis prover, and Sledghammer.
Users can use such tools, but also directly apply rules to rewrite or prove goals if their conditions for application are met.
For example, the rule `refl` can prove sub-goals by reflection if the goal is of the form `x = x` for some `x`.

Moreover, users can define their own proof methods using Eisbach, Isabelle's built-in proof method language.
With Eisbach, invoked with the `method` keyword, it is possible to combine different rules and reasoning tools for specific use-cases.
Such user-defined methods can be applied the same way as other pre-defined proof methods, using the `apply` keyword followed by the specified method name.
For example, the rule `asm_rl` can be applied, which only succeeds for sub-goals of a specific form, followed by another proof method capable of solving or simplifying that specific sub-goal.
It also features built-in sub-goal pattern matching for this end, which is more powerful as it then allows using variables from matched sub-goal for proof methods.

The first technique to apply certain proof-methods for specific subgoals is used in @lst-custom-methods, where a similar proof as @lst-mult-proof is given.
Here, the method `example_base` can only be used for the base step of the induction proof, as applying `rule asm_rl[of "mult _ 0 = _"]` only succeeds when a sub-goal of that form is present.
Similarly, the method `example_inductive` can only be used for the inductive step, as it needs a sub-goal where the second parameter of `mult` is a successor of another natural number.
Trying to apply the methods to other sub-goals fails.

#fig(
  ```isabelle
method example_base = rule asm_rl[of "mult _ 0 = _"], simp
method example_inductive = rule asm_rl[of "mult _ (Suc _) = _"], simp

lemma "mult a b = a * b"
  apply (induction b)
  apply example_base
  apply example_inductive
  done
```,
  [Custom Proof Methods in `mult` Lemma]
)<lst-custom-methods>
