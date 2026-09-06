import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Erdos917
open Filter Topology

namespace AEHK

/-- Reindex s ≥ 4 by the natural numbers. -/
def h (s : ℕ) : ℕ := 3 ^ (s + 4)
def v (s : ℕ) : ℕ := 13 * h s ^ 4 + 12 * h s ^ 2
def d (s : ℕ) : ℕ := 22 * h s ^ 2 - 3

lemma h_lower (s : ℕ) : 81 ≤ h s := by
  have hp : 0 < 3 ^ s := by positivity
  simp only [h, pow_add]
  norm_num
  omega

lemma h_odd (s : ℕ) : Odd (h s) := (by decide : Odd (3 : ℕ)).pow

lemma v_lower (s : ℕ) : 5 ≤ v s := by
  have hh := h_lower s
  dsimp [v]
  nlinarith [sq_nonneg (h s)]

lemma h_le_v (s : ℕ) : h s ≤ v s := by
  have hh := h_lower s
  dsimp [v]
  nlinarith [sq_nonneg (h s)]

lemma degree_small (s : ℕ) : d s < v s - 1 := by
  have hh := h_lower s
  have hs : 1 ≤ h s ^ 2 := by nlinarith
  have hfour : h s ^ 4 = (h s ^ 2) ^ 2 := by ring
  have hd : d s ≤ 22 * h s ^ 2 := Nat.sub_le _ _
  have ht := Nat.mul_le_mul_left (h s ^ 2) hs
  have hb : d s + 2 ≤ v s := by
    dsimp [v]
    rw [hfour]
    nlinarith only [hd, hs, ht]
  omega

lemma size_condition (s : ℕ) : 40 * h s * d s < v s := by
  have hh := h_lower s
  have hpos : 0 < h s ^ 3 := by positivity
  have hcmp := Nat.mul_lt_mul_of_pos_right (show 880 < 13 * h s by omega) hpos
  have hd : d s ≤ 22 * h s ^ 2 := Nat.sub_le _ _
  calc
    _ ≤ 40 * h s * (22 * h s ^ 2) := Nat.mul_le_mul_left _ hd
    _ = 880 * h s ^ 3 := by ring
    _ < 13 * h s ^ 4 := by nlinarith only [hcmp]
    _ ≤ v s := Nat.le_add_right _ _

lemma h_tendsto : Tendsto h atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3 : ℕ))).comp
    (tendsto_add_atTop_nat 4)

lemma v_tendsto : Tendsto v atTop atTop := tendsto_atTop_mono h_le_v h_tendsto

lemma degree_ratio_tendsto :
    Tendsto (fun s => (d s : ℝ) / v s) atTop (𝓝 0) := by
  have hinv : Tendsto (fun s => ((h s : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h_tendsto)
  have hmajor : Tendsto (fun s => (22 / 13 : ℝ) * ((h s : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (hinv.pow 2).const_mul (22 / 13 : ℝ)
  apply squeeze_zero (fun s => by positivity) _ hmajor
  intro s
  have hh : (0 : ℝ) < h s := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 81) (h_lower s))
  have hv : (0 : ℝ) < v s := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) (v_lower s))
  have hd : (d s : ℝ) ≤ 22 * (h s : ℝ) ^ 2 := by exact_mod_cast (Nat.sub_le (22 * h s ^ 2) 3)
  have he : (v s : ℝ) = 13 * (h s : ℝ) ^ 4 + 12 * (h s : ℝ) ^ 2 := by simp [v]
  apply (div_le_iff₀ hv).mpr
  rw [he]
  field_simp
  nlinarith [sq_nonneg ((h s : ℝ) ^ 2)]

end AEHK
end Erdos917
