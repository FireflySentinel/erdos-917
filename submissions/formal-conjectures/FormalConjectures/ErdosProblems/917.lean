/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 917

*References:*
- [erdosproblems.com/917](https://www.erdosproblems.com/917)
- [Di52] Dirac, G. A., A property of $4$-chromatic graphs and some remarks on
  critical graphs. J. London Math. Soc. (1952), 85–92.
- [Er69b] Erdős, P., Problems and results in chromatic graph theory.
  Proof Techniques in Graph Theory (1969), 27–35.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory.
  Quaestiones Math. (1993), 333–350.
- [LMY23] Luo, Cong and Ma, Jie and Yang, Tianchi, On the maximum number of edges
  in $k$-critical graphs. Combin. Probab. Comput. (2023), 900–911.
- [To70] Toft, B., On the maximal number of edges of critical $k$-chromatic graphs.
  Studia Sci. Math. Hungar. (1970), 461–470.
- [St87] Stiebitz, M., Subgraphs of colour-critical graphs. Combinatorica (1987), 303–312.
- [Gu26] Gu, Q., Twelve-critical graphs with $(2/5+o(1))n^2$ edges.
  https://github.com/FireflySentinel/erdos-917
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos917

/-- Edge-deletion criticality: every edge deletion decreases the chromatic number. -/
def IsEdgeCriticalGraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ u v, G.Adj u v →
    (G.deleteEdges {s(u, v)}).chromaticNumber < G.chromaticNumber

/-- The largest edge count of an edge-critical $k$-chromatic graph on $n$ vertices.
The value is zero when the class is empty. -/
noncomputable def extremalEdges (k n : ℕ) : ℕ :=
  sSup ((fun G : SimpleGraph (Fin n) => Nat.card G.edgeSet) ''
    {G | IsEdgeCriticalGraph G k})

/--
Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$
vertices which has chromatic number $k$ and is critical (i.e. deleting any edge
reduces the chromatic number).
Is it true that $f_k(n) \gg_k n^2$?

Toft [To70] proved that $f_k(n)\gg_k n^2$ for $k\geq 4$.
-/
@[category research solved, AMS 5]
theorem erdos_917.parts.i :
    answer(True) ↔ ∀ k : ℕ, 4 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (extremalEdges k n : ℝ) := by
  sorry

/--
Is it true that $f_6(n)\sim n^2/4$?
-/
@[category research open, AMS 5]
theorem erdos_917.parts.ii :
    answer(sorry) ↔
      Tendsto (fun n : ℕ => (extremalEdges 6 n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 (1 / 4 : ℝ)) := by
  sorry

/--
More generally, is it true that, for $k\geq 6$,
$f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$?

Stiebitz [St87] disproved the conjectured asymptotic for $k\not\equiv0\pmod3$.
Gu [Gu26] gives a counterexample at $k=12$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-917/blob/3a1409ca0f415b4c51287e46f0c8a5406fca0425/checks/FormalConjecturesBridge.lean#L64"]
theorem erdos_917.parts.iii :
    answer(False) ↔ ∀ k : ℕ, 6 ≤ k →
      Tendsto (fun n : ℕ => (extremalEdges k n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 ((1 / 2 : ℝ) * (1 - 1 / ((k / 3 : ℕ) : ℝ)))) := by
  sorry

/--
For every $c<2/5$, the quotient $f_{12}(n)/n^2$ does not converge to $c$ [Gu26].
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/FireflySentinel/erdos-917/blob/3a1409ca0f415b4c51287e46f0c8a5406fca0425/checks/FormalConjecturesBridge.lean#L52"]
theorem erdos_917.variants.k_twelve :
    ∀ c : ℝ, c < 2 / 5 →
      ¬Tendsto (fun n : ℕ => (extremalEdges 12 n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 c) := by
  sorry

end Erdos917
