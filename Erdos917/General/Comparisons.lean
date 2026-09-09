import Erdos917.General.Main

/-! Comparisons with the coefficients of Erdős and Toft. -/
namespace Erdos917
open SimpleGraph Filter Topology

noncomputable def constructionDensity (k : ℕ) : ℝ :=
  if Even k then ((k : ℝ)-4)/(2*((k : ℝ)-2))
  else ((k : ℝ)-5)/(2*((k : ℝ)-3))

noncomputable def erdosCoefficient (k : ℕ) : ℝ :=
  1/2*(1-1/((k/3 : ℕ) : ℝ))

noncomputable def toftDelta (k : ℕ) : ℝ :=
  if k%3 = 0 then 0 else if k%3 = 1 then 8/7 else 44/23

noncomputable def toftCoefficient (k : ℕ) : ℝ :=
  1/2-3/(2*k-toftDelta k)

lemma toftDelta_bounds (k : ℕ) : 0 ≤ toftDelta k ∧ toftDelta k < 2 := by
  unfold toftDelta
  split_ifs <;> norm_num

private lemma density_reciprocal {x b : ℝ} (hb : x-b ≠ 0) :
    (x-(b+2))/(2*(x-b)) = 1/2-1/(x-b) := by
  field_simp
  ring

lemma erdosCoefficient_lt_density (k : ℕ) (hk : 8 ≤ k) (h9 : k ≠ 9) :
    erdosCoefficient k < constructionDensity k := by
  have hq : (0 : ℝ) < (k/3 : ℕ) := by exact_mod_cast (show 0 < k/3 by omega)
  have hc : erdosCoefficient k = 1/2-1/(2*((k/3 : ℕ) : ℝ)) := by
    unfold erdosCoefficient
    field_simp
  rw [hc]
  unfold constructionDensity
  by_cases he : Even k
  · rw [if_pos he]
    have ha : 2*(k/3) < k-2 := by omega
    have hp : (0 : ℝ) < k-2 := by
      have : (8 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [show (k : ℝ)-4 = (k : ℝ)-(2+2) by ring,
      density_reciprocal (ne_of_gt hp)]
    apply sub_lt_sub_left _ _
    apply one_div_lt_one_div_of_lt (by positivity)
    have hh : (2*((k/3 : ℕ) : ℝ)) < ((k-2 : ℕ) : ℝ) := by exact_mod_cast ha
    simpa only [Nat.cast_sub (by omega : 2 ≤ k),Nat.cast_ofNat] using hh
  · rw [if_neg he]
    have ho : k%2 = 1 := by rw [Nat.even_iff] at he; omega
    have ha : 2*(k/3) < k-3 := by omega
    have hp : (0 : ℝ) < k-3 := by
      have : (8 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [show (k : ℝ)-5 = (k : ℝ)-(3+2) by ring,
      density_reciprocal (ne_of_gt hp)]
    apply sub_lt_sub_left _ _
    apply one_div_lt_one_div_of_lt (by positivity)
    have hh : (2*((k/3 : ℕ) : ℝ)) < ((k-3 : ℕ) : ℝ) := by exact_mod_cast ha
    simpa only [Nat.cast_sub (by omega : 3 ≤ k),Nat.cast_ofNat] using hh

lemma toftCoefficient_lt_density (k : ℕ) (hk : 8 ≤ k) (h9 : k ≠ 9) :
    toftCoefficient k < constructionDensity k := by
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨hd0,hd2⟩ := toftDelta_bounds k
  have hd : (0 : ℝ) < 2*k-toftDelta k := by linarith
  unfold toftCoefficient constructionDensity
  by_cases he : Even k
  · rw [if_pos he]
    have hp : (0 : ℝ) < k-2 := by linarith
    rw [show (k : ℝ)-4 = (k : ℝ)-(2+2) by ring,
      density_reciprocal (ne_of_gt hp)]
    apply sub_lt_sub_left _ _
    exact (div_lt_div_iff₀ hp hd).mpr (by nlinarith)
  · rw [if_neg he]
    have ho : k%2 = 1 := by rw [Nat.even_iff] at he; omega
    have hk11 : (11 : ℝ) ≤ k := by exact_mod_cast (show 11 ≤ k by omega)
    have hp : (0 : ℝ) < k-3 := by linarith
    rw [show (k : ℝ)-5 = (k : ℝ)-(3+2) by ring,
      density_reciprocal (ne_of_gt hp)]
    apply sub_lt_sub_left _ _
    exact (div_lt_div_iff₀ hp hd).mpr (by nlinarith)

lemma coefficients_nine : constructionDensity 9 = 1/3 ∧
    erdosCoefficient 9 = 1/3 ∧ toftCoefficient 9 = 1/3 := by
  norm_num [constructionDensity,erdosCoefficient,toftCoefficient,toftDelta,Nat.even_iff]

/-- The edge-deletion version of the extremal function, with empty value zero. -/
noncomputable def fk (k n : ℕ) : ℕ :=
  sSup (edgeCount '' {G : SimpleGraph (Fin n) | IsEdgeCritical G k})

lemma fk_twelve (n : ℕ) : fk 12 n = f12 n := rfl

lemma edgeCount_le_fk {k n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsCritical G k) : edgeCount G ≤ fk k n := by
  apply le_csSup ((Set.toFinite _).image edgeCount).bddAbove
  exact ⟨G,hG.edgeCritical,rfl⟩

lemma fk_le_square (k n : ℕ) : fk k n ≤ n^2 := by
  classical
  apply csSup_le'
  rintro m ⟨G,_,rfl⟩
  rw [edgeCount_eq_card_edgeFinset]
  exact G.card_edgeFinset_le_card_choose_two.trans (by simpa using Nat.choose_le_pow n 2)

lemma fk_density_le_one (k n : ℕ) : (fk k n : ℝ)/(n : ℝ)^2 ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · apply (div_le_iff₀ (sq_pos_of_ne_zero (by exact_mod_cast hn))).mpr
    simpa using (show (fk k n : ℝ) ≤ (n : ℝ)^2 from by exact_mod_cast fk_le_square k n)

lemma fk_limsup_ge_density (k : ℕ) (hk : 8 ≤ k) :
    constructionDensity k ≤ limsup (fun n : ℕ => (fk k n : ℝ)/(n : ℝ)^2) atTop := by
  obtain ⟨N,G,hN,hG,hd⟩ := dense_critical_graphs k hk
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (fk k n : ℝ)/(n : ℝ)^2) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fk_density_le_one k))
  apply le_limsup_of_le hb
  intro b hbound
  apply le_of_tendsto hd
  filter_upwards [hN.eventually hbound] with s hs
  exact (div_le_div_of_nonneg_right
    (show (edgeCount (G s) : ℝ) ≤ fk k (N s) from by exact_mod_cast edgeCount_le_fk (hG s))
    (sq_nonneg _)).trans hs

lemma quadratic_asymptotic_density {f : ℕ → ℝ} {c : ℝ}
    (h : Asymptotics.IsEquivalent atTop f (fun n : ℕ => c*(n : ℝ)^2)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^2) atTop (𝓝 c) := by
  have hd := h.div (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)^2))
  apply hd.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [hn0]

/-- Corollary 2: strict improvements over both coefficients and failure of (1.1). -/
theorem corollary_two (k : ℕ) (hk : 8 ≤ k) (h9 : k ≠ 9) :
    constructionDensity k ≤ limsup (fun n : ℕ => (fk k n : ℝ)/(n : ℝ)^2) atTop ∧
    erdosCoefficient k < constructionDensity k ∧ toftCoefficient k < constructionDensity k ∧
    ¬ Asymptotics.IsEquivalent atTop (fun n : ℕ => (fk k n : ℝ))
      (fun n : ℕ => erdosCoefficient k*(n : ℝ)^2) := by
  have he := (erdosCoefficient_lt_density k hk h9).trans_le (fk_limsup_ge_density k hk)
  refine ⟨fk_limsup_ge_density k hk,erdosCoefficient_lt_density k hk h9,
    toftCoefficient_lt_density k hk h9,?_⟩
  intro h
  exact (ne_of_gt he) (quadratic_asymptotic_density h).limsup_eq

end Erdos917
