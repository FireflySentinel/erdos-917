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
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos917
```

`leanchecker Erdos917` checks every compiled module with that name prefix;
`-v` lists the modules in the CI log.

## Exact statement

[`Erdos917.conversion_twelve_critical`](Erdos917/Main.lean) proves that the five-module
construction is twelve-critical: chromatic number 12, and every proper subgraph, including
those missing vertices, is 11-colorable. [`Erdos917.AEHK.canonical_counterexample_density`](Erdos917/AEHK/Family.lean)
gives the limit $e/N^2\to2/5$. [`Erdos917.f12_not_density_below_two_fifths`](Erdos917/AEHK/Family.lean)
rules out any limit below $2/5$ for $f_{12}(n)/n^2$, with $f_{12}$ defined under
Problem 917's edge-deletion convention.

The AEHK family is constructed in Lean over finite fields.
[`exists_prime_power_model`](Erdos917/AEHK/Family.lean) proves Lemma 4 for every
prime power $Q \ge 4$, including saturation and the exact maximum degree.
[`Erdos917.not_density_three_eighths`](Erdos917/AEHK/Family.lean) has no external
mathematical hypothesis.
The manuscript's final remark extends the construction to other chromatic numbers;
the Lean development covers $k=12$.

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

## Use of generative AI

The proofs and the first draft were generated with GPT-6 Astra;
GPT-5.6 Sol and Claude Opus 5 were used for editorial review;
the explicit verification of the AEHK construction and the Lean formalization
were developed with OpenAI Codex (GPT-6).
The author checked the arguments and is responsible for the content.
