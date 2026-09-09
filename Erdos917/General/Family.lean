import Erdos917.General.Parameters
import Erdos917.General.EdgeCount
import Erdos917.General.Density

/-! Explicit saturated graphs and the resulting critical graphs for every even chromatic number at least eight. -/
namespace Erdos917.General
open SimpleGraph Filter Topology

lemma base_model_exists (n s : ℕ) :
    ∃ G : SimpleGraph (Fin (v n s)), Saturated n G ∧
      ∀ z, Nat.card (G.neighborSet z) ≤ d n s := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have he : 3^(2*(s+offset n)) = h n s ^ 2 := by
    unfold h
    rw [Nat.mul_comm 2 (s+offset n),pow_mul]
  have hn : 2*(s+offset n) ≠ 0 := by unfold offset; omega
  have hm := exists_prime_power_model n 3 (2*(s+offset n)) hn (by rw [he]; exact q_lower n s)
  rw [he] at hm
  exact hm

noncomputable def baseGraph (n s : ℕ) : SimpleGraph (Fin (v n s)) :=
  (base_model_exists n s).choose

lemma baseGraph_saturated (n s : ℕ) : Saturated n (baseGraph n s) :=
  (base_model_exists n s).choose_spec.1

lemma baseGraph_degree (n s : ℕ) [DecidableRel (baseGraph n s).Adj] :
    ∀ z, (baseGraph n s).degree z ≤ d n s := by
  intro z
  rw [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  exact (base_model_exists n s).choose_spec.2 z

abbrev Vertex (n s : ℕ) := AssemblyVertex n (SVertex n (h n s)) (TVertex n (Fintype.card (Fin (v n s))))

noncomputable def graph (n s : ℕ) : SimpleGraph (Vertex n s) :=
  conversionGraph n (baseGraph n s) (h n s) (by simpa using v_lower n s)

theorem graph_critical (n s : ℕ) : IsCritical (graph n s) (2*n+8) := by
  classical
  have hs := baseGraph_saturated n s
  exact conversion_critical (baseGraph n s) (h n s) (d n s)
    (by simpa using v_lower n s) (h_large n s) (h_odd n s)
    hs.free hs.add_edges (baseGraph_degree n s)
    (by simpa using degree_small n s) (by simpa using size_condition n s)

lemma graph_order (n s : ℕ) :
    Fintype.card (Vertex n s) = (n+3)*(2*h n s*v n s+h n s+2*v n s) := by
  simpa only [Vertex,Fintype.card_fin] using conversion_order (V := Fin (v n s)) (by simpa using v_lower n s) (h_large n s)

lemma graph_order_real (n s : ℕ) :
    (Fintype.card (Vertex n s) : ℝ) = constructionOrder n (h n s) (v n s) := by
  rw [graph_order]
  simp [constructionOrder]

lemma graph_size (n s : ℕ) :
    (edgeCount (graph n s) : ℝ) = constructionSize n (h n s) (v n s) (edgeCount (baseGraph n s)) := by
  change (edgeCount (conversionGraph n (baseGraph n s) (h n s) _) : ℝ) = _
  rw [conversion_edgeCount _ _ (h_large n s)]
  simp only [Fintype.card_fin,constructionSize]

lemma graph_order_tendsto (n : ℕ) :
    Tendsto (fun s => Fintype.card (Vertex n s)) atTop atTop := by
  apply tendsto_atTop_mono _ (h_tendsto n)
  intro s
  rw [graph_order]
  calc
    h n s ≤ 2*h n s*v n s+h n s+2*v n s := by omega
    _ ≤ (n+3)*(2*h n s*v n s+h n s+2*v n s) :=
      Nat.le_mul_of_pos_left _ (by omega)

theorem graph_density (n : ℕ) :
    Tendsto (fun s => (edgeCount (graph n s) : ℝ)/(Fintype.card (Vertex n s) : ℝ)^2)
      atTop (𝓝 ((n+2)/(2*(n+3)) : ℝ)) := by
  classical
  simp_rw [graph_size,graph_order_real]
  apply density_limit_of_parameters n (fun s => (h n s : ℝ)) (fun s => (v n s : ℝ))
    (fun s => (d n s : ℝ)) (fun s => (edgeCount (baseGraph n s) : ℝ))
  · intro s; exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2*n+7) (h_large n s))
  · intro s; exact_mod_cast (lt_of_lt_of_le (by omega : 0 < n+3) (v_lower n s))
  · intro s; positivity
  · intro s; simpa using degree_sum_bound (baseGraph n s) (baseGraph_degree n s)
  · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (h_tendsto n))
  · exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (v_tendsto n))
  · exact degree_ratio_tendsto n

end Erdos917.General
