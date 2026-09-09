import Erdos917.AEHK.Family

/-! The explicit limsup consequence for the extremal function in Problem 917. -/
namespace Erdos917
open SimpleGraph Filter Topology

lemma f12_le_square (n : ℕ) : f12 n ≤ n^2 := by
  classical
  apply csSup_le'
  rintro m ⟨G,_,rfl⟩
  rw [edgeCount_eq_card_edgeFinset]
  exact G.card_edgeFinset_le_card_choose_two.trans (by simpa using Nat.choose_le_pow n 2)

lemma f12_density_le_one (n : ℕ) : (f12 n : ℝ)/(n : ℝ)^2 ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · apply (div_le_iff₀ (sq_pos_of_ne_zero (by exact_mod_cast hn))).mpr
    simpa using (show (f12 n : ℝ) ≤ (n : ℝ)^2 from by exact_mod_cast f12_le_square n)

/-- The limsup inequality in the manuscript's final calculation. -/
theorem f12_limsup_ge_two_fifths :
    (2/5 : ℝ) ≤ limsup (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) atTop := by
  let F := AEHK.canonicalFamily
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (f12 n : ℝ)/(n : ℝ)^2) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall f12_density_le_one)
  apply le_limsup_of_le hb
  intro b hbound
  apply le_of_tendsto (AEHK.counterexample_density F)
  filter_upwards [AEHK.counterexample_order_tendsto.eventually hbound] with s hs
  exact (div_le_div_of_nonneg_right
    (show (edgeCount (AEHK.counterexample F s) : ℝ) ≤ f12 (Fintype.card (AEHK.Vertex s)) from
      by exact_mod_cast AEHK.counterexample_edgeCount_le_f12 F s) (sq_nonneg _)).trans hs

end Erdos917
