import Erdos917.General.Cone
import Erdos917.Definitions

/-! Theorem 1, stated for finite graphs and every chromatic number at least eight. -/
namespace Erdos917
open SimpleGraph Filter Topology

namespace General

lemma finite_family {V : ℕ → Type} [∀ s, Fintype (V s)]
    (G : ∀ s, SimpleGraph (V s)) {k : ℕ} {c : ℝ}
    (hcrit : ∀ s, IsCritical (G s) k)
    (hN : Tendsto (fun s => Fintype.card (V s)) atTop atTop)
    (hd : Tendsto (fun s => (edgeCount (G s) : ℝ)/(Fintype.card (V s) : ℝ)^2)
      atTop (𝓝 c)) :
    ∃ (N : ℕ → ℕ) (H : ∀ s, SimpleGraph (Fin (N s))),
      Tendsto N atTop atTop ∧ (∀ s, IsCritical (H s) k) ∧
      Tendsto (fun s => (edgeCount (H s) : ℝ)/(N s : ℝ)^2) atTop (𝓝 c) := by
  classical
  let e (s : ℕ) := Fintype.equivFin (V s)
  let H (s : ℕ) := (G s).comap (e s).symm
  let i (s : ℕ) : G s ≃g H s := { e s with map_rel_iff' := by simp [H] }
  have he (s : ℕ) : edgeCount (H s) = edgeCount (G s) := (Nat.card_congr (i s).mapEdgeSet).symm
  refine ⟨fun s => Fintype.card (V s),H,hN,fun s => (hcrit s).iso (i s),?_⟩
  simpa only [he] using hd

lemma even_family (n : ℕ) :
    ∃ (N : ℕ → ℕ) (G : ∀ s, SimpleGraph (Fin (N s))),
      Tendsto N atTop atTop ∧ (∀ s, IsCritical (G s) (2*n+8)) ∧
      Tendsto (fun s => (edgeCount (G s) : ℝ)/(N s : ℝ)^2)
        atTop (𝓝 ((n+2)/(2*(n+3)) : ℝ)) :=
  finite_family (graph n) (graph_critical n) (graph_order_tendsto n) (graph_density n)

lemma odd_family (n : ℕ) :
    ∃ (N : ℕ → ℕ) (G : ∀ s, SimpleGraph (Fin (N s))),
      Tendsto N atTop atTop ∧ (∀ s, IsCritical (G s) (2*n+9)) ∧
      Tendsto (fun s => (edgeCount (G s) : ℝ)/(N s : ℝ)^2)
        atTop (𝓝 ((n+2)/(2*(n+3)) : ℝ)) := by
  apply finite_family (fun s => cone (graph n s)) (cone_graph_critical n) _ (cone_graph_density n)
  exact tendsto_atTop_mono (fun s => by simp) (graph_order_tendsto n)

end General

/-- For every `k ≥ 8`, there are arbitrarily large `k`-critical graphs with the
limiting edge density stated in Theorem 1. -/
theorem dense_critical_graphs (k : ℕ) (hk : 8 ≤ k) :
    ∃ (N : ℕ → ℕ) (G : ∀ s, SimpleGraph (Fin (N s))),
      Tendsto N atTop atTop ∧ (∀ s, IsCritical (G s) k) ∧
      Tendsto (fun s => (edgeCount (G s) : ℝ)/(N s : ℝ)^2) atTop
        (𝓝 (if Even k then ((k : ℝ)-4)/(2*((k : ℝ)-2))
          else ((k : ℝ)-5)/(2*((k : ℝ)-3)))) := by
  by_cases he : Even k
  · rw [if_pos he]
    have hm : k%2 = 0 := Nat.even_iff.mp he
    have hk' : k = 2*((k-8)/2)+8 := by omega
    obtain ⟨N,G,hN,hG,hd⟩ := General.even_family ((k-8)/2)
    refine ⟨N,G,hN,fun s => hk' ▸ hG s,?_⟩
    have hr : (k : ℝ) = 2*((((k-8)/2 : ℕ) : ℝ))+8 := by exact_mod_cast hk'
    have hcoef : ((k : ℝ)-4)/(2*((k : ℝ)-2)) =
        (((k-8)/2 : ℕ)+2)/(2*((((k-8)/2 : ℕ) : ℝ)+3)) := by
      rw [hr]
      calc
        _ = (2*(((((k-8)/2 : ℕ) : ℝ))+2))/(2*(2*(((((k-8)/2 : ℕ) : ℝ))+3))) := by congr 1 <;> ring
        _ = _ := mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
    rw [hcoef]
    exact hd
  · rw [if_neg he]
    have hm : k%2 = 1 := by rw [Nat.even_iff] at he; omega
    have hk' : k = 2*((k-9)/2)+9 := by omega
    obtain ⟨N,G,hN,hG,hd⟩ := General.odd_family ((k-9)/2)
    refine ⟨N,G,hN,fun s => hk' ▸ hG s,?_⟩
    have hr : (k : ℝ) = 2*((((k-9)/2 : ℕ) : ℝ))+9 := by exact_mod_cast hk'
    have hcoef : ((k : ℝ)-5)/(2*((k : ℝ)-3)) =
        (((k-9)/2 : ℕ)+2)/(2*((((k-9)/2 : ℕ) : ℝ)+3)) := by
      rw [hr]
      calc
        _ = (2*(((((k-9)/2 : ℕ) : ℝ))+2))/(2*(2*(((((k-9)/2 : ℕ) : ℝ))+3))) := by congr 1 <;> ring
        _ = _ := mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)
    rw [hcoef]
    exact hd

end Erdos917
