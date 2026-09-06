import Erdos917.Extremal
import Erdos917.Density
import Erdos917.Parameters

namespace Erdos917
open SimpleGraph Filter Topology

namespace AEHK

/-- Manuscript Lemma 4, specialized to Q = (3^(s+4))²: AEHK, Example 2
(Section 4), with k = 5 and one added vertex per truncated-plane line.
This gives 12Q(Q+1) core vertices and Q² line vertices. Their respective degrees
are 22Q-3 and 12(Q+1), so the latter is at most the former for Q ≥ 4.
Existence of this family is the external input. -/
structure Family where
  graph : (s : ℕ) → SimpleGraph (Fin (v s))
  free : ∀ s, (graph s).CliqueFree 5
  saturated : ∀ s z w, z ≠ w → ¬ (graph s).Adj z w →
    ¬ (graph s ⊔ edge z w).CliqueFree 5
  degree : ∀ s z, Nat.card ((graph s).neighborSet z) ≤ d s

abbrev Vertex (s : ℕ) := AssemblyVertex (SVertex (h s)) (TVertex (Fintype.card (Fin (v s))))

noncomputable def counterexample (F : Family) (s : ℕ) : SimpleGraph (Vertex s) :=
  conversionGraph (F.graph s) (h s) (by simpa using v_lower s)

lemma family_degree (F : Family) (s : ℕ) [DecidableRel (F.graph s).Adj] :
    ∀ z, (F.graph s).degree z ≤ d s := by
  intro z
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← Nat.card_eq_fintype_card]
  exact F.degree s z

/-- Every member of the family is twelve-critical, including the proper-subgraph condition. -/
theorem counterexample_critical (F : Family) (s : ℕ) :
    IsCritical (counterexample F s) 12 := by
  classical
  exact conversion_twelve_critical (F.graph s) (h s) (d s)
    (by simpa using v_lower s) (by have := h_lower s; omega) (h_odd s)
    (F.free s) (F.saturated s) (family_degree F s)
    (by simpa using degree_small s) (by simpa using size_condition s)

lemma counterexample_order (s : ℕ) :
    Fintype.card (Vertex s) = 5 * (2 * h s * v s + h s + 2 * v s) := by
  simpa using conversion_order (V := Fin (v s)) (by simpa using v_lower s)
    (by have := h_lower s; omega : 11 ≤ h s)

lemma counterexample_order_real (s : ℕ) :
    (Fintype.card (Vertex s) : ℝ) = constructionOrder (h s) (v s) := by
  rw [counterexample_order]
  simp [constructionOrder]

lemma counterexample_size (F : Family) (s : ℕ) :
    (edgeCount (counterexample F s) : ℝ) =
      constructionSize (h s) (v s) (edgeCount (F.graph s)) := by
  change (edgeCount (conversionGraph (F.graph s) (h s) _) : ℝ) = _
  rw [conversion_edgeCount (F.graph s) _ (by have := h_lower s; omega)]
  simp only [Fintype.card_fin, constructionSize]

/-- The orders tend to infinity, so the family supplies an asymptotic subsequence. -/
theorem counterexample_order_tendsto :
    Tendsto (fun s => Fintype.card (Vertex s)) atTop atTop := by
  apply tendsto_atTop_mono _ h_tendsto
  intro s
  rw [counterexample_order]
  omega

/-- Theorem 1: edge density tends to 2/5, conditional only on the stated AEHK family. -/
theorem counterexample_density (F : Family) :
    Tendsto (fun s => (edgeCount (counterexample F s) : ℝ) /
      (Fintype.card (Vertex s) : ℝ) ^ 2) atTop (𝓝 (2 / 5 : ℝ)) := by
  classical
  simp_rw [counterexample_size, counterexample_order_real]
  apply density_limit_of_parameters (fun s => (h s : ℝ)) (fun s => (v s : ℝ))
    (fun s => (d s : ℝ)) (fun s => (edgeCount (F.graph s) : ℝ))
  · intro s; exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 81) (h_lower s))
  · intro s; exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) (v_lower s))
  · intro s; positivity
  · intro s; simpa using degree_sum_bound (F.graph s) (family_degree F s)
  · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h_tendsto)
  · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp v_tendsto)
  · exact degree_ratio_tendsto

/-- Any density limit of a function dominating the constructed graphs is at least 2/5. -/
theorem density_limit_ge_two_fifths (F : Family) (f : ℕ → ℝ)
    (hf : ∀ s, (edgeCount (counterexample F s) : ℝ) ≤ f (Fintype.card (Vertex s))) :
    ∀ {c : ℝ}, Tendsto (fun n : ℕ => f n / (n : ℝ) ^ 2) atTop (𝓝 c) → 2 / 5 ≤ c := by
  intro c hlim
  have hsub := hlim.comp counterexample_order_tendsto
  exact le_of_tendsto_of_tendsto' (counterexample_density F) hsub
    (fun s => div_le_div_of_nonneg_right (hf s) (sq_nonneg _))

lemma counterexample_edgeCount_le_f12 (F : Family) (s : ℕ) :
    edgeCount (counterexample F s) ≤ f12 (Fintype.card (Vertex s)) :=
  edgeCount_le_f12 (counterexample_critical F s)

/-- The extremal function in the problem cannot have any density limit below 2/5. -/
theorem f12_not_density_below_two_fifths (F : Family) {c : ℝ} (hc : c < 2 / 5) :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 c) := by
  intro hlim
  have hb := density_limit_ge_two_fifths F (fun n => (f12 n : ℝ))
    (fun s => by exact_mod_cast counterexample_edgeCount_le_f12 F s) hlim
  exact (not_le_of_gt hc) hb

/-- The problem's proposed asymptotic formula fails at k = 12. -/
theorem not_density_three_eighths (F : Family) :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (3 / 8 : ℝ)) :=
  f12_not_density_below_two_fifths F (by norm_num)

end AEHK
end Erdos917
