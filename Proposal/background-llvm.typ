#import "functions.typ": fig

== LLVM and LLVM-IR
<sec-llvm>

LLVM is a toolkit for the construction of compilers, optimizers, and run-time environments.
At its core is its own intermediate representation, LLVM-IR, a low-level programming language similar to assembly.
It can be used to develop front-ends for any programming language, and back-ends for any target architecture.
Currently it supports compiling many source languages, including C, C++, Haskell, and Rust, to a wide range of target architectures, including x86-64, ARM, and RISC-V.


=== LLVM-IR Structure
<sec-llvm-structure>

LLVM-IR is composed at the highest level of different modules, which themselves are made up of functions, global variables, and symbol table entries.
The functions consist of an outer definition, including its parameters and return type, and inner basic blocks.
These basic blocks are made up of a block label (which are local identifiers), followed by zero or more phi instructions, then some regular instructions, and finally one terminal instruction.
Control-flow between basic blocks is determined only by these terminal instructions, as they either specify a local identifier to branch to, or return from the function.
The other instructions can only affect the outer control-flow by, for example, calling another function, but not the inner control-flow of the function being executed.

LLVM-IR has two different ways of storing data: in registers, and in memory.
Its registers are function-local single-static-assignment values, accessible via identifiers.
In other words, they can only be assigned once statically, and their values only remain accessible within the function they are defined in.
Their values can however be overwritten when the instruction that assigns them is executed again.
Meanwhile, its memory is accessible via specific instructions such as `load` and `store`.
These instructions are given the memory addresses to operate on using registers.

Identifiers start with `%` for these local identifiers, and `@` for global identifiers (used for functions and global variables).
They have to be unique, either at a local level for local identifiers, or globally for global identifiers.
Whenever a value is used as an operand for an instruction, it can either be specified as the identifier of a register, or a constant value.

As an example of a function in LLVM-IR, @lst-mult-llvm shows the `mult` function from @lst-mult-impl compiled to LLVM-IR.
Its definition specifies its return type is `i32`, and has two `i32` parameters, accessible in registers `%a` and `%b`.
It contains 5 different basic blocks: `entry`, `for.cond`, `for.body`, `for.inc`, and `for.end`.
None of these blocks contain phi instructions, and are made up of the instructions `alloca`, `store`, `load`, `icmp`, and `add`.
They contain the terminal instructions `br` (both the direct `label` and conditional `i1` branch variants) and `ret`.
The syntax of these instructions is given in @llvm-instr-syntax.

#fig(
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

#fig(
  ```llvm
<result> = phi [fast-math-flags] <ty> [ <val0>, <label0>], ...

<result> = alloca [inalloca] <type> [, <ty> <NumElements>] [, align <alignment>] [, addrspace(<num>)]
store [volatile] <ty> <value>, ptr <pointer>[, align <alignment>]
<result> = load [volatile] <ty>, ptr <pointer>[, align <alignment>]
<result> = add [nuw] [nsw] <ty> <op1>, <op2>
<result> = icmp [samesign] <cond> <ty> <op1>, <op2>

br i1 <cond>, label <iftrue>, label <iffalse>
br label <dest>

ret <type> <value>
ret void
```,
  [Syntax of LLVM-IR Instructions]
)<llvm-instr-syntax>


=== LLVM-IR Semantics
<sec-llvm-semantics>

When executing functions, its first instruction block (which is the only one where a label is not mandatory) is executed first.
From there, the terminal instructions of blocks dictate whether another block is executed, or the function returns.
Within blocks, instructions are executed in-order.
As this thesis will only encapsulate a sub-set of LLVM-IR instructions, only the semantics of those included will be shown here, which are: `phi`, `alloca`, `store`, `load`, `add`, `icmp`, `br`, and `ret`.
As the scope of the thesis increases to cover more instructions, this section will grow to also explain their semantics.

The fact that LLVM-IR functions are already subdivided into basic blocks with straight-forward control-flow makes it ideal for graph-based deductive verification.
Each basic block can only lead to one other predetermined basic block, or to one of two based on a boolean value, so constructing a control-flow graph is simple.
With that, the biggest challenge for the design of the verifier is how to annotate basic blocks with pre-conditions and how to symbolically execute instructions from there, keeping track of register and memory state modifications.


==== Phi Instructions

The `phi` instructions always have to appear at the start of an instruction block.
They assign some value from the list `[ <val0>, <label0>], ...` to the register `<result>`, specified by the pair corresponding to the predecessor block that branched to this block.
As such, it allows for a conditional register assignment which is a valid SSA-value.


==== Regular Instructions

`alloca` instructions allocate memory on the stack frame of the current function, which is released automatically when the function returns.
They yield a pointer to the newly allocated memory, which is stored in the register `<result>`.

`store` instructions store a value (from a register or a constant value) at some memory address from a pointer (e.g. an address space in a register, as return by `alloca`).
It does not yield any value.

`load` instructions read a value at a memory address from a pointer.
It yields the read value to be stored into the register `<result>`.

`add` instructions add together two values of the same type, `<op1>` and `<op2>` and yields the result to be stored into `<result>`.
Depending on whether `nuw`, no unsigned wrap, or `nsw`, no signed wrap, were specified, and either an unsigned or signed overflow occurred respectively, a poison value is produced.
Such a poison value propagates whenever it is used in any computations, and leads to undefined behavior when it is used for certain instructions, for example those that affect control-flow and memory addressing.

`icmp` instructions compare two integer values according to the specified comparison operand `<cond>`.
This is one of `eq` for equal, `ne` for not equal, `ugt` for unsigned greater than, `uge` for unsigned greater or equal, `ult` for unsigned less than, and `ule` for unsigned less or equal comparisons, or `sgt`, `sge`, `slt`, and `sle` for their signed counterparts.
If `samesign` was specified then the operation produces a poison value if the operands are not of the same sign.
It yields a single-bit integer (a boolean) for the comparison to be stored into `<result>`.


==== Terminal Instructions

`br label` instructions branch to the basic block with the specified label unconditionally, while `br i1` branches to the block with the first label if the value `<cond>` is true, or the block with the second label if it is false.
This has undefined behavior is `<cond>` is a poison value.

`ret` returns from a function with the specified `<value>`, or with no value if the type is `void`.
