# Erdős Problem #917: twelve-critical graphs with $(2/5+o(1))n^2$ edges

Preprint disproving the general asymptotic conjecture in
[Erdős Problem #917](https://www.erdosproblems.com/917) at $k=12$, the first case in the
residue class $3\mid k$.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
lake env lean -DwarningAsError=true checks/FormalConjecturesBridge.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos917
```

## Exact statement

The main theorem is
[`Erdos917.f12_not_density_below_two_fifths`](Erdos917/AEHK/Family.lean):
for every real $c < 2/5$, $f_{12}(n)/n^2$ does not converge to $c$.
Its statement uses three project-specific definitions:

- [`edgeCount`](Erdos917/EdgeCount.lean): the number of unordered edges.
- [`IsEdgeCritical`](Erdos917/Extremal.lean): criticality under Problem 917's edge-deletion convention.
- [`f12`](Erdos917/Extremal.lean): the maximum edge count of a twelve-critical graph on $n$ vertices under this convention, or $0$ when the class is empty.

[`checks/Check.lean`](checks/Check.lean) verifies that the axiom dependencies are
`propext`, `Classical.choice`, and `Quot.sound`.
[`Erdos917.not_density_three_eighths`](Erdos917/AEHK/Family.lean)
gives the particular case $c = 3/8$ proposed in Problem 917.

The AEHK family is constructed in Lean over finite fields, so the main theorem
carries no external mathematical hypothesis. The manuscript's final remark extends
the construction to other chromatic numbers; the Lean development covers $k=12$.

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Lemma 2: active colors, prescribed singleton, module-edge deletions | [Module.lean](Erdos917/Module.lean) |
| Eleven-color impossibility | [Assembly.lean](Erdos917/Assembly.lean), `not_eleven_colorable` |
| Proposition 3, exact edge formula and lower bound | [EdgeCount.lean](Erdos917/EdgeCount.lean), `conversion_edgeCount` |
| Density limit from the edge formula | [Density.lean](Erdos917/Density.lean), `density_limit_of_parameters` |
| Lemma 4: finite geometry, clique exclusion, saturation | [Geometry.lean](Erdos917/AEHK/Geometry.lean), [Cliques.lean](Erdos917/AEHK/Cliques.lean), [Triangles.lean](Erdos917/AEHK/Triangles.lean) |
| Lemma 4: order and exact degrees | [Degrees.lean](Erdos917/AEHK/Degrees.lean) |
| Theorem 1 and the extremal-function consequence | [Family.lean](Erdos917/AEHK/Family.lean) |

## Community statements

[Prepared contributions](submissions/README.md) include the Formal Conjectures
statement, a [proved bridge](checks/FormalConjecturesBridge.lean), and the proposed
Erdős database update. Run `python3 submissions/check_bridge.py` to check that
the definitions and linked theorem types agree.

## Use of generative AI

The proofs and the first draft were generated with GPT-6 Astra;
GPT-5.6 Sol and Claude Opus 5 were used for editorial review;
the explicit verification of the AEHK construction and the Lean formalization
were developed with OpenAI Codex (GPT-6).
The author checked the arguments and is responsible for the content.
