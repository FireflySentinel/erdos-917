import Erdos917

/-! # Explicit statements for Erdős Problem 917

The extremal-function result refutes the general asymptotic formula at $k=12$.
Edge-criticality is expressed by a decrease in chromatic number after deleting an edge.
-/

noncomputable section

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

private theorem criticalGraph_twelve_iff {V : Type*} (G : SimpleGraph V) :
    IsEdgeCriticalGraph G 12 ↔ IsEdgeCritical G 12 := by
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun u v huv => ?_⟩
    apply chromaticNumber_le_iff_colorable.mp
    have hlt := h u v huv
    rw [hk] at hlt
    exact Order.le_of_lt_add_one (show
      (G.deleteEdges {s(u, v)}).chromaticNumber < (11 : ℕ∞) + 1 by norm_num; exact hlt)
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun u v huv => ?_⟩
    rw [hk]
    exact lt_of_le_of_lt (h u v huv).chromaticNumber_le (by norm_num)

private theorem extremalEdges_twelve (n : ℕ) : extremalEdges 12 n = f12 n := by
  simp only [extremalEdges, f12, fk, criticalGraph_twelve_iff]
  rfl

/-- The normalized extremal edge count at $k=12$ cannot converge below $2/5$. -/
theorem erdos_917.variants.k_twelve :
    ∀ c : ℝ, c < 2 / 5 →
      ¬Tendsto (fun n : ℕ => (extremalEdges 12 n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 c) := by
  intro c hc
  simpa only [extremalEdges_twelve] using f12_not_density_below_two_fifths hc

/-- info: 'Erdos917.erdos_917.variants.k_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos917.erdos_917.variants.k_twelve

/-- The proposed asymptotic formula fails at $k=12$, refuting its universal form. -/
theorem erdos_917.parts.iii :
    False ↔ ∀ k : ℕ, 6 ≤ k →
      Tendsto (fun n : ℕ => (extremalEdges k n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 ((1 / 2 : ℝ) * (1 - 1 / ((k / 3 : ℕ) : ℝ)))) := by
  constructor
  · exact False.elim
  · intro h
    have h12 := h 12 (by norm_num)
    have hnot := erdos_917.variants.k_twelve (3 / 8) (by norm_num)
    apply hnot
    convert h12 using 1; norm_num

/-- info: 'Erdos917.erdos_917.parts.iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos917.erdos_917.parts.iii

end Erdos917
