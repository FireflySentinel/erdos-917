import Erdos917.General.PrimePowerModel
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos917.General
open Filter Topology

@[irreducible] def offset (n : ℕ) : ℕ := 4*(n+3)^3*(n+2)+2*(n+3)^2+2*n+10
@[irreducible] def h (n s : ℕ) : ℕ := 3^(s+offset n)
def v (n s : ℕ) : ℕ := baseOrder n (h n s ^ 2)
def d (n s : ℕ) : ℕ := baseBound n (h n s ^ 2)

lemma h_lower (n s : ℕ) : offset n < h n s := by
  have hp := Nat.lt_pow_self (n := s+offset n) (by decide : 1 < 3)
  unfold h
  omega

lemma h_large (n s : ℕ) : 2*n+7 ≤ h n s := by
  have hh := h_lower n s
  unfold offset at hh
  omega

lemma h_odd (n s : ℕ) : Odd (h n s) := by
  unfold h
  exact (by decide : Odd (3 : ℕ)).pow

lemma h_four_le_v (n s : ℕ) : h n s ^ 4 ≤ v n s := by
  dsimp [v,baseOrder]
  have he : h n s ^ 4 = (h n s ^ 2)^2 := by ring
  rw [he]
  omega

lemma h_le_v (n s : ℕ) : h n s ≤ v n s :=
  (Nat.le_pow (by decide : 0 < 4)).trans (h_four_le_v n s)

lemma v_lower (n s : ℕ) : n+3 ≤ v n s := by
  have := h_large n s
  have := h_le_v n s
  omega

lemma q_lower (n s : ℕ) : 2*(n+3) ≤ h n s ^ 2 := by
  have := h_large n s
  have hh : h n s ≤ h n s ^ 2 := Nat.le_pow (by decide : 0 < 2)
  omega

lemma size_condition (n s : ℕ) : 2*(n+3)*(n+2)*h n s*d n s < v n s := by
  have hh := h_lower n s
  have hb : 4*(n+3)^3*(n+2) < h n s := by unfold offset at hh; omega
  have hp : 0 < h n s ^ 3 := pow_pos (lt_of_lt_of_le (by omega : 0 < 2*n+7) (h_large n s)) _
  have hc := Nat.mul_lt_mul_of_pos_right hb hp
  calc
    _ = (4*(n+3)^3*(n+2))*h n s ^ 3 := by dsimp [d,baseBound]; ring
    _ < h n s ^ 4 := by nlinarith only [hc]
    _ ≤ v n s := h_four_le_v n s

lemma degree_small (n s : ℕ) : d n s < v n s-1 := by
  have hh := h_lower n s
  have hb : 2*(n+3)^2 < h n s := by unfold offset at hh; omega
  have hp : 0 < h n s ^ 2 := pow_pos (lt_of_lt_of_le (by omega : 0 < 2*n+7) (h_large n s)) _
  have hd : d n s < h n s ^ 3 := by
    have hc := Nat.mul_lt_mul_of_pos_right hb hp
    dsimp [d,baseBound]
    nlinarith only [hc]
  have hh2 : 2 ≤ h n s := by have := h_large n s; omega
  have hc := Nat.mul_le_mul_right (h n s ^ 3) hh2
  have hpow : 2 ≤ h n s ^ 3 := hh2.trans (Nat.le_pow (by decide : 0 < 3))
  have hv := h_four_le_v n s
  have he : h n s ^ 3 + 2 ≤ v n s := by nlinarith only [hc,hpow,hv]
  omega

lemma h_tendsto (n : ℕ) : Tendsto (h n) atTop atTop := by
  unfold h
  exact (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3 : ℕ))).comp
    (tendsto_add_atTop_nat (offset n))

lemma v_tendsto (n : ℕ) : Tendsto (v n) atTop atTop :=
  tendsto_atTop_mono (h_le_v n) (h_tendsto n)

lemma degree_ratio_tendsto (n : ℕ) :
    Tendsto (fun s => (d n s : ℝ)/v n s) atTop (𝓝 0) := by
  have hinv : Tendsto (fun s => ((h n s : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (h_tendsto n))
  have hmajor : Tendsto (fun s => (2*((n : ℝ)+3)^2)*((h n s : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa using (hinv.pow 2).const_mul (2*((n : ℝ)+3)^2)
  apply squeeze_zero (fun s => by positivity) _ hmajor
  intro s
  have hh : (0 : ℝ) < h n s := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2*n+7) (h_large n s))
  have hv : (0 : ℝ) < v n s := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < n+3) (v_lower n s))
  have hb : (h n s : ℝ)^4 ≤ v n s := by exact_mod_cast h_four_le_v n s
  have hd : (d n s : ℝ) = 2*((n : ℝ)+3)^2*(h n s : ℝ)^2 := by simp [d,baseBound]
  rw [hd]
  apply (div_le_iff₀ hv).mpr
  have he : (2*((n : ℝ)+3)^2)*((h n s : ℝ)⁻¹)^2*(h n s : ℝ)^4 =
      2*((n : ℝ)+3)^2*(h n s : ℝ)^2 := by field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end Erdos917.General
