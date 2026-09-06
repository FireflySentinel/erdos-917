# Lean formalization of criticality in Erdős #917

The criticality argument of **Lemma 2 and Proposition 3** in manuscript v3 is formalized in Lean 4. The source manuscript is `FireflySentinel/erdos-917` at commit `5e5ecf9edeaf21a7171988532ffaff2a3e452a93` (5 September 2026). The Lean code was developed against that GitHub revision. `PROOF.tex` and `PROOF.pdf` are unchanged.

## Main result

[`conversion_twelve_critical`](Erdos917/Main.lean) proves that the actual five-module construction is twelve-critical for **every** finite graph H and every parameter h satisfying Proposition 3's assumptions:

- v = |V(H)| ≥ 5, h ≥ 11, and h odd;
- H has no K5, and adding any missing edge creates a K5;
- every degree in H is at most d, with d < v − 1;
- 40hd < v.

The conclusion uses the following explicit definition:

```lean
def IsCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ Q : G.Subgraph, Q ≠ ⊤ → Q.coe.Colorable (k-1)
```

Thus it quantifies over **all proper subgraphs, including those missing vertices**. It is stronger than checking edge counts, a particular finite example, or only vertex deletion. `conversion_chromaticNumber` states χ(G) = 12 separately. `conversion_delete_edge_colorable` states that deleting **any edge** gives an eleven-colorable graph; this latter conclusion does not require the size inequality 40hd < v.

`conversionGraph` constructs the modules and their cross edges explicitly. S is K8 joined to C_(h−8), T is K7 joined to C_(2v−7). Successive additions of universal vertices implement the joins. The T vertices are identified with V(H) × Bool by a finite equivalence. The eleven-color palette is `Option (Fin 5 × Bool)`: two private colors per part, and one shared color. `conversion_order` also verifies the vertex count 5(2hv + h + 2v).

## Correspondence with the paper

| Manuscript argument | Lean source |
|---|---|
| Odd-cycle criticality, including deletion of any cycle edge | [OddCycle.lean](Erdos917/OddCycle.lean) |
| Joining a clique preserves criticality | [Cone.lean](Erdos917/Cone.lean) |
| U(S,T): at least three active colors; prescribed singleton active color; all four internal edge-deletion cases | [Module.lean](Erdos917/Module.lean) |
| Standard saturation gives a common-neighbor triangle | [SaturationDefinition.lean](Erdos917/SaturationDefinition.lean) |
| Lifting saturation, including equal-label endpoints; transversal K4; degree bound | [Saturation.lean](Erdos917/Saturation.lean) |
| Eleven-color impossibility using large private color classes | [Assembly.lean](Erdos917/Assembly.lean) |
| All cross-module and internal edge-deletion colorings | [Deletion.lean](Erdos917/Deletion.lean) |
| No isolated vertices; all proper subgraphs; exact chromatic number | [Critical.lean](Erdos917/Critical.lean) |
| Instantiation with the manuscript's S, T, H and h | [Main.lean](Erdos917/Main.lean) |

The lower-bound proof selects two large colors in each part. They are ten distinct private colors; Lemma 2 forces every part to use the unique remaining color. This gives the forbidden transversal K5. This formulation avoids needing the additional statement that each part has exactly two large colors, while proving the same obstruction.

The auxiliary `Scaffold` and `CriticalData` structures organize proofs. They are **proved for the construction**, not additional hypotheses of `conversion_twelve_critical`. In particular, the theorem's saturation input is the standard statement about H ⊔ edge z w, not an assumed transversal-completion lemma.

## Scope and external input

This completes the criticality component requested here. The existence of the AEHK family of saturated graphs, its degree and order formulas, the edge-count formula, and the asymptotic density argument are **not formalized in this project**. The result is a fully proved conditional conversion theorem; it does not by itself provide an unconditional Lean proof of the entire asymptotic counterexample. It says nothing about the separate k = 6 question.

There are no `sorry`, `admit`, custom `axiom` declarations, `native_decide`, or external solver certificates in the project. The main results use only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Saturation and the numerical assumptions are ordinary quantified hypotheses, not axioms.

## Reproduce verification

Lean is pinned to `v4.33.0-rc2`; `lake-manifest.json` pins mathlib to `51e6992efd06126df61a496bebf8f49482a4e129` and records its transitive dependencies. With elan installed, run from this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker -v Erdos917
```

`Check.lean` guards the axiom lists of the final results and the central supporting theorems. `leanchecker` replays all project declarations through Lean's kernel; it is an additional check using the same Lean implementation, not an independent proof assistant or human review. The GitHub Actions workflow performs the build, axiom checks, and kernel replay.

The development checkout reuses an existing local mathlib cache through an ignored `.lake/packages` symlink. No project source depends on that path; a fresh checkout uses the pinned dependency manifest.

Local verification on 2026-09-06T00:05:39.646174+00:00: `lake build` completed without warnings, `Check.lean` passed, and `leanchecker` replayed all eleven project modules with exit code 0. GitHub CI has been configured but was not run remotely during this task.
