import Erdos917.Saturation
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Erdos917
open Finset SimpleGraph

lemma cliqueFree_no_pairwise {V : Type*} (H : SimpleGraph V) (hH : H.CliqueFree 5)
    (c : Fin 5 → V) (hc : ∀ i j,i ≠ j → H.Adj (c i) (c j)) : False := by
  let f : Copy (completeGraph (Fin 5)) H := {
    toHom := { toFun := c, map_rel' := fun {i j} h => hc i j h }
    injective' := by intro i j he; by_contra hij; exact H.ne_of_adj (hc i j hij) he }
  exact (cliqueFree_iff.mp hH).false f

/-- Recover the common-neighbor triangle from the usual definition of K5 saturation.
The added-edge clique must use both endpoints; its remaining three vertices are the triangle. -/
theorem SaturatedK5.of_add_edges {V : Type*} (H : SimpleGraph V)
    (hfree : H.CliqueFree 5)
    (hadd : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree 5) : SaturatedK5 H := by
  classical
  refine ⟨hfree,?_⟩
  intro z w hzw hn
  let c := topEmbeddingOfNotCliqueFree (hadd z w hzw hn)
  have hc (i j : Fin 5) (hij : i ≠ j) : (H ⊔ edge z w).Adj (c i) (c j) := c.toHom.map_rel hij
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
  let R : Finset (Fin 5) := univ \ {i,j}
  have hR : R.card = 3 := by simp [R,card_sdiff_of_subset (subset_univ _),hij]
  let idx : Fin 3 ≃ R := (R.equivFinOfCardEq hR).symm
  let t : Fin 3 → V := fun k => c (idx k).val
  have hti (k : Fin 3) : (idx k).val ≠ i := by
    have hh := (idx k).property
    exact (by simpa using (mem_sdiff.mp hh).2 : (idx k).val ≠ i ∧ (idx k).val ≠ j).1
  have htj (k : Fin 3) : (idx k).val ≠ j := by
    have hh := (idx k).property
    exact (by simpa using (mem_sdiff.mp hh).2 : (idx k).val ≠ i ∧ (idx k).val ≠ j).2
  have htz (k : Fin 3) : t k ≠ z := by
    intro he
    exact hti k (c.injective (he.trans hi.symm))
  have htw (k : Fin 3) : t k ≠ w := by
    intro he
    exact htj k (c.injective (he.trans hj.symm))
  have old_edge (v : V) (k : Fin 3) (h : (H ⊔ edge z w).Adj v (t k)) : H.Adj v (t k) := by
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

end Erdos917
