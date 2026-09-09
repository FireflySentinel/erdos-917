import Erdos917.General.Saturation
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Erdos917.General
open Finset SimpleGraph
variable {n : ℕ}

lemma cliqueFree_no_pairwise {V : Type*} (H : SimpleGraph V) (hH : H.CliqueFree (n+3))
    (c : Fin (n+3) → V) (hc : ∀ i j,i ≠ j → H.Adj (c i) (c j)) : False := by
  let f : Copy (completeGraph (Fin (n+3))) H := {
    toHom := { toFun := c, map_rel' := fun {i j} h => hc i j h }
    injective' := by intro i j he; by_contra hij; exact H.ne_of_adj (hc i j hij) he }
  exact (cliqueFree_iff.mp hH).false f

/-- Recover the common-neighbor clique from the usual definition of saturation.
The added-edge clique must use both endpoints; the other vertices form the common clique. -/
theorem Saturated.of_add_edges {V : Type*} (H : SimpleGraph V)
    (hfree : H.CliqueFree (n+3))
    (hadd : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree (n+3)) : Saturated n H := by
  classical
  refine ⟨hfree,?_⟩
  intro z w hzw hn
  let c := topEmbeddingOfNotCliqueFree (hadd z w hzw hn)
  have hc (i j : Fin (n+3)) (hij : i ≠ j) : (H ⊔ edge z w).Adj (c i) (c j) := c.toHom.map_rel hij
  have hz : ∃ i,c i = z := by
    by_contra! h
    apply cliqueFree_no_pairwise H hfree c
    intro i j hij
    rcases hc i j hij with h'|h'
    · exact h'
    · have hh := (edge_adj z w (c i) (c j)).mp h'
      rcases hh.1 with ⟨hi,_⟩|⟨_,hj⟩
      · exact False.elim (h i hi)
      · exact False.elim (h j hj)
  have hw : ∃ i,c i = w := by
    by_contra! h
    apply cliqueFree_no_pairwise H hfree c
    intro i j hij
    rcases hc i j hij with h'|h'
    · exact h'
    · have hh := (edge_adj z w (c i) (c j)).mp h'
      rcases hh.1 with ⟨_,hj⟩|⟨hi,_⟩
      · exact False.elim (h j hj)
      · exact False.elim (h i hi)
  obtain ⟨i,hi⟩ := hz
  obtain ⟨j,hj⟩ := hw
  have hij : i ≠ j := by intro h; exact hzw (hi.symm.trans ((congrArg c h).trans hj))
  let R : Finset (Fin (n+3)) := univ \ {i,j}
  have hR : R.card = n+1 := by simp [R,card_sdiff_of_subset (subset_univ _),hij]
  let idx : Fin (n+1) ≃ R := (R.equivFinOfCardEq hR).symm
  let t : Fin (n+1) → V := fun k => c (idx k).val
  have hti (k : Fin (n+1)) : (idx k).val ≠ i := by
    have hh := (idx k).property
    exact (by simpa using (mem_sdiff.mp hh).2 : (idx k).val ≠ i ∧ (idx k).val ≠ j).1
  have htj (k : Fin (n+1)) : (idx k).val ≠ j := by
    have hh := (idx k).property
    exact (by simpa using (mem_sdiff.mp hh).2 : (idx k).val ≠ i ∧ (idx k).val ≠ j).2
  have htz (k : Fin (n+1)) : t k ≠ z := by
    intro he
    exact hti k (c.injective (he.trans hi.symm))
  have htw (k : Fin (n+1)) : t k ≠ w := by
    intro he
    exact htj k (c.injective (he.trans hj.symm))
  have old_edge (v : V) (k : Fin (n+1)) (h : (H ⊔ edge z w).Adj v (t k)) : H.Adj v (t k) := by
    rcases h with h|h
    · exact h
    · have hh := (edge_adj z w v (t k)).mp h
      exact False.elim (hh.1.elim (fun h => htw k h.2) (fun h => htz k h.2))
  refine ⟨t,?_,?_⟩
  · intro k l hkl
    apply old_edge
    apply hc
    intro he
    exact hkl (idx.injective (Subtype.ext he))
  · intro k
    constructor
    · apply old_edge
      simpa only [hi] using hc i (idx k).val (hti k).symm
    · apply old_edge
      simpa only [hj] using hc j (idx k).val (htj k).symm

end Erdos917.General

namespace Erdos917.General
open SimpleGraph

lemma pairwise_cons {V : Type*} {m : ℕ} (G : SimpleGraph V) (x : V) (f : Fin m → V)
    (hx : ∀ i, G.Adj x (f i)) (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    ∀ i j : Fin (m+1), i ≠ j → G.Adj (Fin.cases x f i) (Fin.cases x f j) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact False.elim (hij rfl)
    · intro _; exact hx j
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _; exact (hx i).symm
    · intro hij; exact hf i j (fun h => hij (congrArg Fin.succ h))

lemma Saturated.add_edges {n : ℕ} {V : Type*} {H : SimpleGraph V}
    (hH : Saturated n H) (x y : V) (hxy : x ≠ y) (hn : ¬ H.Adj x y) :
    ¬ (H ⊔ edge x y).CliqueFree (n+3) := by
  obtain ⟨t, ht, hxyT⟩ := hH.common x y hxy hn
  let G := H ⊔ edge x y
  have hxy' : G.Adj x y := Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩)
  have hx (i : Fin (n+1)) : G.Adj x (t i) := Or.inl (hxyT i).1
  have hy (i : Fin (n+1)) : G.Adj y (t i) := Or.inl (hxyT i).2
  have htt (i j : Fin (n+1)) (hij : i ≠ j) : G.Adj (t i) (t j) := Or.inl (ht i j hij)
  intro hfree
  apply cliqueFree_no_pairwise G hfree (Fin.cases x (Fin.cases y t))
  exact pairwise_cons G x _ (fun i => Fin.cases hxy' hx i) (pairwise_cons G y t hy htt)

end Erdos917.General
