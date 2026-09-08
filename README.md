# Erdős Problem #917: twelve-critical graphs with $(2/5+o(1))n^2$ edges

The AEHK family is constructed in Lean over finite fields.
[exists_prime_power_model](Erdos917/AEHK/Family.lean) proves Lemma 4 for every
prime power $Q\ge4$, including saturation and the exact maximum degree.
The Lean development formalizes the $k=12$ result; the manuscript also records
an extension to other chromatic numbers.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos917
```

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Lemma 2: active colors, prescribed singleton, module-edge deletions | [Module.lean](Erdos917/Module.lean) |
| Eleven-color impossibility | [Assembly.lean](Erdos917/Assembly.lean), `not_eleven_colorable` |
| Proposition 3: criticality and edge bounds | [Conversion.lean](Erdos917/Conversion.lean), [EdgeCount.lean](Erdos917/EdgeCount.lean) |
| Density limit from the edge formula | [Density.lean](Erdos917/Density.lean), `density_limit_of_parameters` |
| Lemma 4: finite geometry, clique exclusion, saturation | [Geometry.lean](Erdos917/AEHK/Geometry.lean), [Cliques.lean](Erdos917/AEHK/Cliques.lean), [Triangles.lean](Erdos917/AEHK/Triangles.lean) |
| Lemma 4: order and exact degrees | [Degrees.lean](Erdos917/AEHK/Degrees.lean) |
| Theorem 1 and the extremal-function consequence | [Family.lean](Erdos917/AEHK/Family.lean) |

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.
[`checks/Check.lean`](checks/Check.lean) guards the axiom dependencies to `propext`,
`Classical.choice`, and `Quot.sound`.

## Use of generative AI

GPT-6 Astra proposed the argument and generated the Lean formalization.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The author completed the manuscript and is responsible for the content.
