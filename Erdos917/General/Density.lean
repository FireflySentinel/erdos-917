import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Erdos917.General
open Filter Topology

/-- Order and size formulas of Proposition 4, viewed over the reals. -/
def constructionOrder (n : ℕ) (h v : ℝ) : ℝ := (n+3) * (2 * h * v + h + 2 * v)
noncomputable def constructionSize (n : ℕ) (h v m : ℝ) : ℝ :=
  ((n+3)*(n+2)/2 : ℝ) * ((2 * h * v) ^ 2 - 8 * h ^ 2 * m) + (n+3) * (4*h*v+(2*n+5)*h+4*(n+2)*v-(4*(n : ℝ)^2+20*n+23))

/-- The density limit uses only the degree-sum bound and the three parameter limits. -/
theorem density_limit_of_parameters (n : ℕ) (h v d m : ℕ → ℝ)
    (hh : ∀ s, 0 < h s) (hv : ∀ s, 0 < v s) (hm : ∀ s, 0 ≤ m s)
    (hdegree : ∀ s, 2 * m s ≤ v s * d s)
    (hhinv : Tendsto (fun s => (h s)⁻¹) atTop (𝓝 0))
    (hvinv : Tendsto (fun s => (v s)⁻¹) atTop (𝓝 0))
    (hdv : Tendsto (fun s => d s / v s) atTop (𝓝 0)) :
    Tendsto (fun s => constructionSize n (h s) (v s) (m s) /
      constructionOrder n (h s) (v s) ^ 2) atTop (𝓝 ((n+2) / (2*(n+3)) : ℝ)) := by
  have ht : Tendsto (fun s => 2 * m s / v s ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => div_nonneg (mul_nonneg (by norm_num) (hm s)) (sq_nonneg _)) _ hdv
    intro s
    apply (div_le_iff₀ (sq_pos_of_pos (hv s))).mpr
    have he : d s / v s * v s ^ 2 = v s * d s := by field_simp
    rw [he]
    exact hdegree s
  let F : ℝ × ℝ × ℝ → ℝ := fun p =>
    (((n+3)*(n+2)/2 : ℝ) * (1 - p.2.2) +
      (n+3) * (2 + ((2*n+5)/2 : ℝ) * p.2.1 + 2*(n+2)*p.1 -
        (4*(n : ℝ)^2+20*n+23) * (p.1 * p.2.1 / 2)) *
        (p.1 * p.2.1 / 2)) / (((n : ℝ)+3)^2 * (1 + p.2.1 / 2 + p.1) ^ 2)
  have hF : ContinuousAt F (0, 0, 0) := by
    dsimp [F]
    fun_prop (disch := positivity)
  have hlim := hF.tendsto.comp (hhinv.prodMk_nhds (hvinv.prodMk_nhds ht))
  convert! hlim using 1
  · ext s
    dsimp [F, constructionSize, constructionOrder, Function.comp_def]
    have hhpos := hh s
    have hvpos := hv s
    field_simp
    ring
  · simp only [F, mul_zero, sub_zero, add_zero, zero_div, one_pow]
    congr 1
    have hn : (n : ℝ)+3 ≠ 0 := by positivity
    field_simp

end Erdos917.General
