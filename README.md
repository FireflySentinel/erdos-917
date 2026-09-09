# Dense critical graphs and Erdős Problem #917

Lean 4 formalization of a construction of $k$-critical graphs for every $k\ge8$.
[dense_critical_graphs](Erdos917/General/Main.lean) gives graph sequences whose
orders tend to infinity and whose edge densities tend to $(k-4)/(2(k-2))$ for
even $k$, and $(k-5)/(2(k-3))$ for odd $k$.
For every $k\ge8$, $k\ne9$, the density exceeds both the coefficient proposed
in Problem #917 and Toft's coefficient. At $k=9$, all three equal $1/3$.

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
| Theorem 1: every $k\ge8$ | [Main.lean](Erdos917/General/Main.lean), `dense_critical_graphs` |
| Corollary 2: coefficient comparisons and failure of the proposed asymptotic formula | [Comparisons.lean](Erdos917/General/Comparisons.lean), `corollary_two` |
| Lemma 3: module colorings for any palette of at least three colors | [Module.lean](Erdos917/General/Module.lean) |
| Proposition 4: criticality, order, and edge bounds | [Conversion.lean](Erdos917/General/Conversion.lean), [EdgeCount.lean](Erdos917/General/EdgeCount.lean) |
| Lemma 5: finite-field construction, saturation, and exact maximum degree | [PrimePowerModel.lean](Erdos917/General/PrimePowerModel.lean), `exists_prime_power_exact_model` |
| Corollary 6: $\limsup f_{12}(n)/n^2\ge2/5$ | [Extremal.lean](Erdos917/General/Extremal.lean), `f12_limsup_ge_two_fifths` |

The saturated graphs are constructed in Lean over finite fields, including
the separate triangle-free case. The proof uses no AEHK theorem as a hypothesis.
The earlier $k=12$ construction and its bound for every prime power $Q\ge4$
remain available in [AEHK/Family.lean](Erdos917/AEHK/Family.lean).

The [proof bridge](checks/FormalConjecturesBridge.lean) derives the corresponding
problem statements and is included in `lake test`.
[`checks/Check.lean`](checks/Check.lean) checks the main theorem's type and guards
the axiom dependencies to `propext`, `Classical.choice`, and `Quot.sound`.

## Use of generative AI

GPT-6 Astra proposed the argument and generated the Lean formalization.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The author completed the manuscript and is responsible for the content.
