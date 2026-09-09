import Erdos917

/-! # Explicit statements for Erdős Problem 917

The statements cover every chromatic number in the main theorem.
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

theorem criticalGraph_iff (k : ℕ) (hk : 0 < k) {V : Type*} (G : SimpleGraph V) :
    IsEdgeCriticalGraph G k ↔ IsEdgeCritical G k := by
  have hs : ((k-1 : ℕ) : ℕ∞) + 1 = k := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ k by omega)
  constructor
  · rintro ⟨hG,h⟩
    refine ⟨hG,fun u v huv => ?_⟩
    apply chromaticNumber_le_iff_colorable.mp
    apply Order.le_of_lt_add_one
    rw [hs,← hG]
    exact h u v huv
  · rintro ⟨hG,h⟩
    refine ⟨hG,fun u v huv => ?_⟩
    rw [hG]
    exact lt_of_le_of_lt (h u v huv).chromaticNumber_le (by
      exact_mod_cast Nat.sub_lt hk (by decide : 0 < 1))

theorem extremalEdges_eq_fk (k : ℕ) (hk : 0 < k) (n : ℕ) :
    extremalEdges k n = fk k n := by
  simp only [extremalEdges,fk,criticalGraph_iff k hk]
  rfl

/-- The general density lower bound in the edge-deletion convention. -/
theorem erdos_917.variants.density_lower_bound (k : ℕ) (hk : 8 ≤ k) :
    constructionDensity k ≤
      limsup (fun n : ℕ => (extremalEdges k n : ℝ)/(n : ℝ)^2) atTop := by
  simpa only [extremalEdges_eq_fk k (by omega)] using fk_limsup_ge_density k hk

/-- No limiting density can lie below the construction, for any `k ≥ 8`. -/
theorem erdos_917.variants.no_limit_below (k : ℕ) (hk : 8 ≤ k) {c : ℝ}
    (hc : c < constructionDensity k) :
    ¬ Tendsto (fun n : ℕ => (extremalEdges k n : ℝ)/(n : ℝ)^2) atTop (𝓝 c) := by
  simpa only [extremalEdges_eq_fk k (by omega)] using fk_not_density_below k hk hc

/-- Corollary 2 in the extremal-function convention of the problem statement. -/
theorem erdos_917.variants.corollary (k : ℕ) (hk : 8 ≤ k) (h9 : k ≠ 9) :
    constructionDensity k ≤
      limsup (fun n : ℕ => (extremalEdges k n : ℝ)/(n : ℝ)^2) atTop ∧
    erdosCoefficient k < constructionDensity k ∧
    toftCoefficient k < constructionDensity k ∧
    ¬ Asymptotics.IsEquivalent atTop (fun n : ℕ => (extremalEdges k n : ℝ))
      (fun n : ℕ => erdosCoefficient k*(n : ℝ)^2) := by
  simpa only [extremalEdges_eq_fk k (by omega)] using corollary_two k hk h9

/-- info: 'Erdos917.erdos_917.variants.no_limit_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos917.erdos_917.variants.no_limit_below

/-- info: 'Erdos917.erdos_917.variants.corollary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos917.erdos_917.variants.corollary

/-- The general result refutes the universal formulation of part (iii). -/
theorem erdos_917.parts.iii :
    False ↔ ∀ k : ℕ, 6 ≤ k →
      Tendsto (fun n : ℕ => (extremalEdges k n : ℝ)/(n : ℝ)^2)
        atTop (𝓝 ((1/2 : ℝ)*(1-1/((k/3 : ℕ) : ℝ)))) := by
  constructor
  · exact False.elim
  · intro h
    exact erdos_917.variants.no_limit_below 8 (by decide)
      (erdosCoefficient_lt_density 8 (by decide) (by decide)) (h 8 (by decide))

/-- info: 'Erdos917.erdos_917.parts.iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos917.erdos_917.parts.iii

end Erdos917
