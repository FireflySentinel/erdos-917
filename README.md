# Dense critical graphs and Erdős Problem #917

Lean 4 formalization of a construction of $k$-critical graphs for every $k\ge8$.
[dense_critical_graphs](Erdos917/General/Main.lean) gives graph sequences whose
orders tend to infinity and whose edge densities tend to $(k-4)/(2(k-2))$ for
even $k$, and $(k-5)/(2(k-3))$ for odd $k$.
For every $k\ge8$, $k\ne9$, the density improves Toft's lower bound.
For $3\mid k$ and $k\ge12$, it disproves the asymptotic formula in Problem #917;
Toft had already disproved the formula when $3\nmid k$.
At $k=9$, the construction matches both coefficients at $1/3$.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake test
LEAN_NUM_THREADS=2 lake env leanchecker Erdos917 Check FormalConjecturesBridge
```

## Proof correspondence

| Manuscript argument | Lean source |
|---|---|
| Theorem 1: every $k\ge8$ | [Main.lean](Erdos917/General/Main.lean), `dense_critical_graphs` |
| Corollary 2: coefficient comparisons and failure of the proposed asymptotic formula | [Comparisons.lean](Erdos917/General/Comparisons.lean), `corollary_two` |
| Lemma 3: module colorings for any palette of at least three colors | [Module.lean](Erdos917/General/Module.lean) |
| Proposition 4: criticality, order, and edge bounds | [Conversion.lean](Erdos917/General/Conversion.lean), [EdgeCount.lean](Erdos917/General/EdgeCount.lean) |
| Saturated graphs used in Theorem 1 | [PrimePowerModel.lean](Erdos917/General/PrimePowerModel.lean), `exists_prime_power_exact_model` |
| Any limiting density is at least the constructed density, for every $k\ge8$ | [Extremal.lean](Erdos917/General/Extremal.lean), `fk_not_density_below` |

The paper invokes AEHK Theorem 7. The Lean proof constructs the needed
saturated graphs over finite fields, including the triangle-free case,
and proves their saturation and exact maximum degree directly.
[Definitions.lean](Erdos917/Definitions.lean) contains `IsCritical`,
`IsEdgeCritical`, `edgeCount`, and `fk`; the plane geometry is in
[Geometry.lean](Erdos917/Geometry.lean).

The [proof bridge](checks/FormalConjecturesBridge.lean) proves the density lower
bound for every $k\ge8$ and both coefficient improvements and failure of the
asymptotic formula for every $k\ge8$, $k\ne9$, using the problem's
edge-deletion convention. It is included in `lake test`.
[`checks/Check.lean`](checks/Check.lean) checks the main theorem's type and guards
the axiom dependencies to `propext`, `Classical.choice`, and `Quot.sound`.

## Use of generative AI

GPT-6 Astra proposed the construction of critical graphs and the density estimates,
drafted the manuscript, and generated the Lean formalization.
GPT-5.6 Sol and Claude Opus 5 were used to organize earlier research material
and to review the Lean code.
The author checked the arguments, completed the final manuscript, and takes
full responsibility for the content.
