import Erdos917.General.Comparisons

/-! Consequences for the limiting density of the extremal function. -/
namespace Erdos917
open Filter Topology

/-- For every `k ≥ 8`, any limiting density is at least the constructed density. -/
theorem fk_not_density_below (k : ℕ) (hk : 8 ≤ k) {c : ℝ}
    (hc : c < constructionDensity k) :
    ¬ Tendsto (fun n : ℕ => (fk k n : ℝ)/(n : ℝ)^2) atTop (𝓝 c) := by
  intro h
  have hb := fk_limsup_ge_density k hk
  rw [h.limsup_eq] at hb
  exact (not_le_of_gt hc) hb

end Erdos917
