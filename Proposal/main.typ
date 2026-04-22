#let title-page(title:[], subtitle:[], email:[], name:[], supervisors: [], body) = {
  set page(margin: (top: 3cm, bottom: 3cm, left: 4cm, right: 4cm))
  set text(size: 14pt)
  set heading(numbering: "1.1.1")

  line(start: (0%, 0%), end: (8.5in, 0%), stroke: (thickness: 2pt))

  align(left)[
    #v(1.2cm)
    #text(size: 24pt, weight: "bold")[#title] \
    #v(0.5em)
    #text(size: 20pt, weight: "semibold")[#subtitle]
    #v(0.8em)
    #text(weight: "semibold", fill: luma(64))[Research Topics]
  ]

  v(1fr)

  columns(2)[
    #text(weight: "semibold", fill: gray)[Author] #v(0.3cm)
    #text(name) \
    #link(email)
    
  #colbreak()
    
    #align(right)[
      #text(weight: "semibold", fill: gray)[Supervisors] #v(0.3cm)
      #supervisors
    ]
  ]


  pagebreak()

  set page(fill: none, margin: auto)

  align(center)[
    #outline(indent: auto, depth: 2)
  ]

  pagebreak()

  body
}

#show: body => title-page(
  title: "IsabeLLeVM",
  subtitle: "Deductive verification of LLVM-IR programs in Isabelle",
  email: "mailto:t.s.kas@student.utwente.nl",
  name: "Thomas Kas",
  supervisors: [dr. P. Lammich \ E. Putti],
  body
)

#set page(margin: 1.5cm)
#set par(
  justify: true,
)

#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()

#codly(languages: codly-languages)

#include("intro.typ")

#include("background.typ")

#include("results.typ")

#include("relatedwork.typ")

#include("planning.typ")

#pagebreak()



/*
= Outline

- Introduction
  - why software verification
  - motivating example
  - which methods will be used (1-2 sentences why)
    - dedver
    - LLVM-IR
    - isabelle
  - research goals
- Background
  - Deductive verification
  - LLVM(-IR)
  - Isabelle
- Preliminary Results
  - LLVM-IR semantics in Isabelle
  - Deductive verification infrastructure
  - Tools to efficiently verify programs
  - Small working examples
- Related Work
- Planning


- LLVM-IR
  - describe syntax
    - program made up of functions
    - functions made up of instruction blocks
    - instruction blocks made up of a label, phi nodes, instructions, and terminal instructions
    - C -> LLVM-IR example
  - describe semantics
    - function executed -> first block executed
    - instructions executed sequentially
    - terminal instruction branches to a different block, or returns a value from the function
    - phi nodes assign values to a register depending on the previous block
- LLVM-IR in Isabelle (preliminary results)
  - how is syntax implemented
    - datatypes and type-synonyms
  - how are semantics implemented
    - interpreter over the IR
    - functions are executed from the first block onwards
    - blocks are executed by sequentially executing each instruction
    - flow is handled using terminator instructions, either executing another block or returning a value
    - instructions alter the state according to the semantics defined in the language reference#footnote("https://llvm.org/docs/LangRef.html")
  - ! the semantics cannot be verified to be accurate, so it is trusted: assumed to be correct !
- deductive verification of LLVM-IR (TODO)
  - flow-graph of blocks constructed
  - pre- and post-conditions for any diverging blocks
  - given the pre-condition of a block, show the post-condition of the next diverging endpoint holds
  - where to define these pre- and post-conditions
  - instructions have some effect on state - described in weakest precondition rules
  - verification condition generator takes the pre- and post-conditions, and provides goals to prove
  - only partial correctness
- related works
- planning for completion of the thesis
  - implement separation logic
  - support arrays
  - create control-flow graphs of functions
  - implement VCG for multiple blocks strung together
  - allow annotating blocks with pre- and post-conditions
    - determine diverging paths
    - instantiate phi-nodes based on previous blocks
  - create a translation tool from native LLVM-IR to IsabeLLVM
    - if time permits, create a parser for it within Isabelle
    - otherwise, a simple Rust script will do
    - perhaps also the other way around

    - define MVP
    - risk analysis

*/

#bibliography("references.bib", style: "ieee")
