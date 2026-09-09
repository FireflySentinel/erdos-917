import Erdos917.General.Comparisons

/-! The twelve-critical specialization of the general extremal bound. -/
namespace Erdos917
open Filter Topology

lemma f12_le_square (n : ℕ) : f12 n ≤ n^2 := fk_le_square 12 n

lemma f12_density_le_one (n : ℕ) : (f12 n : ℝ)/(n : ℝ)^2 ≤ 1 :=
  fk_density_le_one 12 n

/-- Corollary 6 follows by taking `k = 12` in Theorem 1. -/
theorem f12_limsup_ge_two_fifths :
    (2/5 : ℝ) ≤ limsup (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) atTop := by
  have h := fk_limsup_ge_density 12 (by decide)
  norm_num [constructionDensity,fk_twelve,Nat.even_iff] at h
  exact h

end Erdos917
