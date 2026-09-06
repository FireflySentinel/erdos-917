# Lean formalization of Erdős #917

The project formalizes **Lemma 2 and the full Proposition 3**, together with the parameter choice and asymptotic deduction in **Theorem 1** of the manuscript. The existence of the AEHK family of saturated graphs is the external mathematical input.

## Conversion theorem

For a finite graph H with v ≥ 5 vertices, the construction is `conversionGraph H h hv`. Under Proposition 3's assumptions (K5 saturation, odd h ≥ 11, degrees at most d < v − 1, and 40hd < v), the following theorems establish:

- `conversion_twelve_critical`: chromatic number 12 and every proper subgraph 11-colorable;
- `conversion_order`: N = 5(2hv + h + 2v);
- `conversion_edgeCount`: e(G) = 10((2hv)² − 8h²m) + 5(4hv + 9h + 16v − 79), where m = e(H);
- `conversion_edgeCount_lower`: e(G) ≥ 10(2hv)²(1 − d/v).

The edge counts are proved for the same graph used in the criticality theorem. `edgeCount` is the cardinality of the unordered edge set, with `edgeCount_eq_card_edgeFinset` identifying it with mathlib's `edgeFinset.card`. The exact formula uses real subtraction.

S is K8 joined to C_(h−8), and T is K7 joined to C_(2v−7). The count splits into structural edges, two edges at each active vertex, and edges retained between distinct active parts. The labeling equivalence supplies exactly 2h occurrences of each H vertex per active part.

## Asymptotic counterexample and external input

[`AEHK.Family`](Erdos917/Counterexample.lean) states the required instance of the AEHK result: for each s ≥ 0, a K5-saturated graph on v_s vertices with degrees at most d_s, where

```text
h_s = 3^(s+4),   v_s = 13h_s⁴ + 12h_s²,   d_s = 22h_s² − 3.
```

This is Lemma 4 specialized to Q = h_s². Its existence proof is not formalized. The parameter inequalities, oddness, and limits used to apply Proposition 3 are proved in [`Parameters.lean`](Erdos917/Parameters.lean).

For `F : AEHK.Family`, `AEHK.counterexample F s` is the actual conversion graph. The project proves its twelve-criticality and that its orders tend to infinity. The density theorem is:

```lean
theorem counterexample_density (F : Family) :
    Tendsto (fun s => (edgeCount (counterexample F s) : ℝ) /
      (Fintype.card (Vertex s) : ℝ) ^ 2) atTop (𝓝 (2 / 5 : ℝ))
```

`AEHK.not_density_three_eighths` then excludes a density limit of 3/8 for any function f satisfying f(N_s) ≥ e(G_s), as the extremal function f₁₂ does. Thus the asymptotic counterexample is formalized conditional on the stated AEHK input. The separate k = 6 question is outside the paper's result.

## Proof correspondence

| Manuscript argument | Lean source and theorem |
|---|---|
| Odd-cycle criticality and arbitrary cycle-edge deletion | [OddCycle.lean](Erdos917/OddCycle.lean) |
| Joining a clique preserves criticality | [Cone.lean](Erdos917/Cone.lean) |
| Lemma 2: active colors, prescribed singleton, four module-edge deletion cases | [Module.lean](Erdos917/Module.lean) |
| Standard saturation gives a common-neighbor triangle | [SaturationDefinition.lean](Erdos917/SaturationDefinition.lean) |
| Saturation lift, equal labels, transversal K4, degree bound | [Saturation.lean](Erdos917/Saturation.lean) |
| Eleven-color impossibility | [Assembly.lean](Erdos917/Assembly.lean), `not_eleven_colorable` |
| All cross-part and internal edge-deletion colorings | [Deletion.lean](Erdos917/Deletion.lean) |
| Proper subgraphs and chromatic number | [Critical.lean](Erdos917/Critical.lean), [Main.lean](Erdos917/Main.lean) |
| Proposition 3, exact edge formula (3.4) and lower bound (3.3) | [EdgeCount.lean](Erdos917/EdgeCount.lean), `conversion_edgeCount`, `conversion_edgeCount_lower` |
| Choice h = 3^s and all numerical hypotheses | [Parameters.lean](Erdos917/Parameters.lean) |
| Density limit from the edge formula and degree-sum bound | [Density.lean](Erdos917/Density.lean), `density_limit_of_parameters` |
| Theorem 1 and the extremal-function consequence | [Counterexample.lean](Erdos917/Counterexample.lean) |

## Build

The original manuscript baseline is commit `5e5ecf9edeaf21a7171988532ffaff2a3e452a93`. The current chromatic lower-bound proof uses the same direct pigeonhole argument and ten private colors as `Assembly.lean`. Lean is pinned to `v4.33.0-rc2`, and `lake-manifest.json` pins mathlib to `51e6992efd06126df61a496bebf8f49482a4e129`.

```sh
lake exe cache get
lake build
lake env lean Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos917
```

[`Check.lean`](Check.lean) guards the axiom dependencies of the main results. The [GitHub workflow](https://github.com/FireflySentinel/erdos-917/actions/workflows/lean.yml) runs the build, axiom checks, and kernel replay.
