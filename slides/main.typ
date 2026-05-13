#import "@preview/touying:0.7.3": *
#import themes.stargazer: *

#import "@preview/numbly:0.1.0": numbly

#import "@preview/simplebnf:0.1.2": *

#import "@preview/prooflists:0.1.0": prooflist
#import "@preview/curryst:0.6.0": rule-set
#import "@preview/fontawesome:0.2.1": *

#show: stargazer-theme.with(
  aspect-ratio: "16-9",
  config-info(
    title: [Epicycles - A Bidirectional DSL],
    subtitle: [],
    author: [Alexander Wood],
    date: datetime.today(),
    institution: [University of Bristol],
  ),
  config-common(show-bibliography-as-footnote: bibliography("../writing/references.bib")),
)
#set heading(numbering: numbly("{1}.", default: "1.1"))

#title-slide()

// #outline-slide()

= Introduction

== Objectives

#columns(2)[
  - Make a *bidirectional* DSL for making geometric art
    - _TidalCycles_ for graphics
    - Edit the output and get new code!
  #colbreak()
  #image(
    "basic.png",
  )
]


= Background

- Updates are often ambiguous
  - e.g. "move this point right by 5 pixels"
  - How does the code change?
  - _View-Update Problem_ 🗃️
- Existing solutions push ambiguity to the user
  - e.g. _Sketch-n-Sketch_@hempel_sketch-n-sketch_2019 asks the user to choose between multiple options
  - Updates feel clunky

== Possible Solutions

=== 🔎 Lenses

- Well-studied, easy to reason about...
#pause
- ... don't handle sharing well
#pause
=== 🧮 Heuristics

- Handles sharing better than lenses
#pause
- Can feel unpredictable to the user

#pause
=== ⛰️ Automatic Differentiation

- Use gradients to find the best update
#pause
- Very domain specific, not very PL-y

#pause

=== 🔗 Domain Restriction

- Can we remove the ambiguity altogether...?

== Domain Restriction

- Design a system where updates are (mostly) unambiguous by design
- View-Update problem comes from View being too separate from the Source
- Make the view and source the same thing!
- Affects syntax _and_ UI design

#pause

Make DSL for _Fourier Series_
- Each term is a circle
- View $<-->$ Source, so updates are unambiguous

= My DSL

== Syntax

#bnf(
  Prod(
    $e$,
    annot: $sans("Expr")$,
    {
      Or[$x$][_variable_]
      Or[$n in QQ$][_literal_]
      Or[$e_1 + e_2$][_add_]
      Or[$e_1 * e_2$][_mul_]
      Or[$e_1^(-1)$][_recip_]
      Or[let $x = e_1 "in" o$][_let_]
    },
  ),

  Prod(
    $c$,
    annot: $sans("Curve")$,
    {
      Or[$"epicycle"(e_r, e_omega, e_phi)$][_epicycle_]
      Or[$c_1 xor c_2$][_concat_]
    },
  ),

  Prod(
    $o$,
    annot: $sans("CurveOrExpr")$,
    {
      Or[$c$][_curve_]
      Or[$e$][_expr_]
    },
  ),
)

An $"epicycle"$ term represents a spinning circle with radius $e_r$, rotation frequency $e_omega$, and phase shift $e_phi$.

Concatenating two curves $c_1$ and $c_2$ with $xor$: draw $c_1$ with $c_2$ centered at the trace of $c_1$

Let bindings _only_ bind numeric values!



#let litInt = prooflist[
  / #smallcaps[T-LitInt]: $Gamma tack n : ZZ$
    + $n in ZZ$
]

#let litRat = prooflist[
  / #smallcaps[T-LitRat]: $Gamma tack n : QQ$
    + $n in QQ$
]

#let tVar = prooflist[
  / #smallcaps[T-Var]: $Gamma tack x : tau$
    + $x : tau in Gamma$
]

#let add = prooflist[
  / #smallcaps[T-Add]: $Gamma tack e_1 + e_2 : tau$
    + $Gamma tack e_1 : tau$
    + $Gamma tack e_2 : tau$
]

#let tLet = prooflist[
  / #smallcaps[T-Let]: $Gamma tack "let" x = e_1 "in" o : tau$
    + $Gamma tack e_1 : eta$
    + $Gamma, x : eta tack o : tau$
]

#let tEpicycle = prooflist[
  / #smallcaps[T-Epicycle]: $Gamma tack "epicycle"(e_r, e_omega, e_phi) : "Curve"$
    + $Gamma tack e_r : eta$
    + $Gamma tack e_omega : ZZ$
    + $Gamma tack e_phi : eta$
]

#let concat = prooflist[
  / #smallcaps[T-Concat]: $Gamma tack c_1 xor c_2 : "Curve"$
    + $Gamma tack c_1 : "Curve"$
    + $Gamma tack c_2 : "Curve"$
]

#[
  #set text(size: 0.8em)
  #set block(spacing: 1em)

  == Statics

  #grid(
    columns: (1fr, 1fr),
    column-gutter: 2em,
    row-gutter: 2.5em,
    align: center + horizon,

    grid(
      columns: 2,
      column-gutter: 3em,
      bnf(Prod($eta$, {
        Or[$ZZ$][]
        Or[$QQ$][]
      })),
      bnf(Prod($tau$, {
        Or[$eta$][]
        Or[Curve][]
      })),
    ),
    rule-set(tLet),

    rule-set(litInt, litRat), rule-set(tEpicycle),
    rule-set(tVar, add), rule-set(concat),
  )
]

== Implementation

- Deeply Embedded DSL in Haskell
- Use _Embedding by Unembedding_@matsuda_embedding_2023 for HOAS frontend, FOAS backend
- _Trees that Grow_ for type safety


```haskell
curve :: (CurveExpr e) => e SCurve
curve =
  let_ 60 $ \a ->
    epicycle a 1 0
      <> epicycle (a * recip 3) 3 0
```


== Forward Semantics

#let tLitInt = prooflist[
  / #smallcaps[E-LitInt]: $sigma, t tack n : ZZ arrow.b.double n$
]

#let tLitRat = prooflist[
  / #smallcaps[E-LitRat]: $sigma, t tack n : QQ arrow.b.double n$
]

#let eVar = prooflist[
  / #smallcaps[E-Var]: $sigma, t tack x : tau arrow.b.double sigma(x)$
    + $x : tau in sigma$
]

#let eAdd = prooflist[
  / #smallcaps[E-Add]: $sigma, t tack e_1 + e_2 : eta arrow.b.double v_1 + v_2$
    + $sigma, t tack e_1 : eta arrow.b.double v_1$
    + $sigma, t tack e_2 : eta arrow.b.double v_2$
]

#let eLet = prooflist[
  / #smallcaps[E-Let]: $sigma, t tack "let" x = e_1 "in" o : tau arrow.b.double v$
    + $sigma, t tack e_1 : eta arrow.b.double v_1$
    + $sigma[x |-> v_1], t tack o : tau arrow.b.double v$
]

#let eEpi = prooflist[
  / #smallcaps[E-Epicycle]: $sigma, t tack "epicycle"(e_r, e_omega, e_phi) : "Curve" arrow.b.double v_r dot e^(i (v_omega dot t + v_phi))$
    + $sigma, t tack e_r : QQ arrow.b.double v_r$
    + $sigma, t tack e_omega : ZZ arrow.b.double v_omega$
    + $sigma, t tack e_phi : QQ arrow.b.double v_phi$
]

#let eConcat = prooflist[
  / #smallcaps[E-Concat]: $sigma, t tack c_1 xor c_2 : "Curve" arrow.b.double v_1 + v_2$
    + $sigma, t tack c_1 : "Curve" arrow.b.double v_1$
    + $sigma, t tack c_2 : "Curve" arrow.b.double v_2$
]

#align(center, rule-set(eVar, eAdd, eLet, eEpi, eConcat))

== Backward Semantics

We have removed amguity, how do we update?
#pause
Implement and compare two different backward semantics:
- 🔀 Sketch-n-Sketch style + heuristics@hempel_sketch-n-sketch_2019
- 🔺 Delta-based with program synthesis@zhang_fusing_2024


== Sketch-n-Sketch Style Heuristics

#columns(2)[
  A slightly simplified version of Sketch-n-Sketch's semantics@mayer_bidirectional_2018:
  - Non-deterministic!
  - Updates $x + y$ by fixing either $x$ or $y$ and updating the other to match
  - Evaluate all candidates with a cost function
  #pause
  - Intuitive for the user... but violates correctness 🙁
  #pause
  - In production, requires outsourcing to Computer Algebra System 😢#footnote("e.g. MATLAB, Maple, etc")

  #colbreak()

  #table(
    columns: (1fr, 1fr),
  )[ *Rule* ][*Holds?*][#smallcaps[GetPut]][✅][#smallcaps[PutGet]][🥲][#smallcaps[PutPut]][🪦]
]

== 🔺 Delta-Based with Program Synthesis

#columns(2)[
  - Based on @zhang_fusing_2024 -- use a separate delta language to represent updates
  - Turn deltas into program rewrites when conflicts arise
    - $"let" r = 10 "in" r * r mapsto "let" r = 10 "in" (r + 1.1) * r$
  - Deterministic - left biased
  - Much more well-behaved, correctness guaranteed
  #colbreak()
  #table(
    columns: (1fr, 1fr),
  )[ *Rule* ][*Holds?*][#smallcaps[GetPut]][✅][#smallcaps[PutGet]][✅][#smallcaps[PutPut]][✅]
]
== Expressivity



#columns(2)[
  - Changing a few parameters creates variety of interesting patterns
  - *Discrete Fourier Transform* lets us represent any (continuous) curve as a sum of epicycles!
  - Can approximate text, images, etc

  #colbreak()

  #grid(
    columns: (1fr, 1fr),
    row-gutter: 1em,
    column-gutter: 1em,
    align:center,
    image("snowflake.png", height: 35%), image("decay.png", height: 35%),
  image("guilloche.png", height: 35%), image("asymm.png", height: 35%)
  )
]


= Evaluation

== The Tradeoffs

#grid(
  columns: (1fr, 1fr),
  column-gutter: 2em,

  [
    === 🔀 Sketch-n-Sketch
    #table(
      columns: (auto, auto),
      stroke: none,
      [🧑‍🎨], [🙂 Intuitive edits (usually)],
      [👨‍💻], [🙁 $approx 6%$  #smallcaps("PutPut") failure, common #smallcaps("PutGet") failure ],
    )
    - $"let" r = 10 "in" r * r mapsto 💥$
  ],
  [
    === 🔺 Delta-Based
    #table(
      columns: (auto, auto),
      stroke: none,
      [🧑‍🎨], [🥲 Mutates AST shape],
      [👨‍💻], [🙂 Correctness guaranteed],
    )

    - Bounded AST growth (max $approx 1.4times$)
    - Much harder to prove formally!
  ],
)

== Conclusions & Future Work

#list(
  marker: fa-check-circle(fill: green),
  [Mechanically verified properties in Lean (Delta proofs assisted by LLM).],
  [Proved DSL normal form & delta growth reaches a fixed point.],
)
#list(
  marker: fa-arrow-right(fill: blue),
  [*Conclusion:* Delta semantics are superior, but good UX isn't always correct.],
)
#list(
  marker: fa-rocket(fill: orange),
  [*Future Work:* Move away from embedding, new target domain, allow "unlocks" for shared vars],
)

== Thank You!


- 🔗 = 🗃️ ✅
- 🔀 = 🧑‍🎨 🙂 + 👨‍💻😦
- 🔺 = 🧑‍🎨 🥲 + 👨‍💻🙂
