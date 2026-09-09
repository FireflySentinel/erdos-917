import Erdos917.General.Comparisons

/-! The twelve-critical specialization of the general extremal bound. -/
namespace Erdos917
open Filter Topology

lemma f12_le_square (n : ℕ) : f12 n ≤ n^2 := fk_le_square 12 n

lemma f12_density_le_one (n : ℕ) : (f12 n : ℝ)/(n : ℝ)^2 ≤ 1 :=
  fk_density_le_one 12 n

/-- The `k = 12` instance in Corollary 2. -/
theorem f12_limsup_ge_two_fifths :
    (2/5 : ℝ) ≤ limsup (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) atTop := by
  have h := fk_limsup_ge_density 12 (by decide)
  norm_num [constructionDensity,fk_twelve,Nat.even_iff] at h
  exact h

theorem f12_not_density_below_two_fifths {c : ℝ} (hc : c < 2/5) :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) atTop (𝓝 c) := by
  intro h
  have hb := f12_limsup_ge_two_fifths
  rw [h.limsup_eq] at hb
  exact (not_le_of_gt hc) hb

theorem not_density_three_eighths :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) atTop (𝓝 (3/8 : ℝ)) :=
  f12_not_density_below_two_fifths (by norm_num)

end Erdos917
