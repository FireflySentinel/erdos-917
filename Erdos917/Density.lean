import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Erdos917
open Filter Topology

/-- Order and size formulas of Proposition 3, viewed over the reals. -/
def constructionOrder (h v : ℝ) : ℝ := 5 * (2 * h * v + h + 2 * v)
def constructionSize (h v m : ℝ) : ℝ :=
  10 * ((2 * h * v) ^ 2 - 8 * h ^ 2 * m) + 5 * (4 * h * v + 9 * h + 16 * v - 79)

/-- The density limit uses only the degree-sum bound and the three parameter limits. -/
theorem density_limit_of_parameters (h v d m : ℕ → ℝ)
    (hh : ∀ s, 0 < h s) (hv : ∀ s, 0 < v s) (hm : ∀ s, 0 ≤ m s)
    (hdegree : ∀ s, 2 * m s ≤ v s * d s)
    (hhinv : Tendsto (fun s => (h s)⁻¹) atTop (𝓝 0))
    (hvinv : Tendsto (fun s => (v s)⁻¹) atTop (𝓝 0))
    (hdv : Tendsto (fun s => d s / v s) atTop (𝓝 0)) :
    Tendsto (fun s => constructionSize (h s) (v s) (m s) /
      constructionOrder (h s) (v s) ^ 2) atTop (𝓝 (2 / 5 : ℝ)) := by
  have ht : Tendsto (fun s => 2 * m s / v s ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => div_nonneg (mul_nonneg (by norm_num) (hm s)) (sq_nonneg _)) _ hdv
    intro s
    apply (div_le_iff₀ (sq_pos_of_pos (hv s))).mpr
    have he : d s / v s * v s ^ 2 = v s * d s := by field_simp
    rw [he]
    exact hdegree s
  let F : ℝ × ℝ × ℝ → ℝ := fun p =>
    (10 * (1 - p.2.2) +
      5 * (2 + (9 / 2 : ℝ) * p.2.1 + 8 * p.1 - 79 * (p.1 * p.2.1 / 2)) *
        (p.1 * p.2.1 / 2)) / (25 * (1 + p.2.1 / 2 + p.1) ^ 2)
  have hF : ContinuousAt F (0, 0, 0) := by
    dsimp [F]
    fun_prop (disch := norm_num)
  have hlim := hF.tendsto.comp (hhinv.prodMk_nhds (hvinv.prodMk_nhds ht))
  convert! hlim using 1
  · ext s
    dsimp [F, constructionSize, constructionOrder, Function.comp_def]
    have hhpos := hh s
    have hvpos := hv s
    field_simp
    ring
  · norm_num [F]

end Erdos917
