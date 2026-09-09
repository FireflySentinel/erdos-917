import Erdos917.General.Cliques
import Erdos917.General.CommonCliques
import Erdos917.General.Degrees
import Erdos917.General.SaturationDefinition

/-! The saturated graph of clique order `r + 4`, including its exact parameters. -/

namespace Erdos917.General
open SimpleGraph Erdos917.Geometry
variable {q : ℕ} [NeZero q]

theorem planeGraph_saturated (r : ℕ) (P : Plane q) (hq : 2*(r+2) ≤ q) :
    Saturated (r+1) (planeGraph r P) :=
  ⟨planeGraph_cliqueFree r P hq,
    fun x y _ hn => planeGraph_commonClique P (by omega) x y hn⟩

theorem exists_finite_model (r : ℕ) (P : Plane q) (hq : 2*(r+2) ≤ q) :
    ∃ G : SimpleGraph (Fin ((r+2)*(r+3)*(q^2+q)+q^2)),
      Saturated (r+1) G ∧
      (∀ z, Nat.card (G.neighborSet z) ≤ q*((r+2)*(2*r+5)+1)-(r+2)) ∧
      ∃ z, Nat.card (G.neighborSet z) = q*((r+2)*(2*r+5)+1)-(r+2) := by
  classical
  let e : Fin ((r+2)*(r+3)*(q^2+q)+q^2) ≃ PlaneVertex r P :=
    (Fintype.equivFinOfCardEq (planeVertex_card r P)).symm
  let G := planeGraph r P
  let H := G.comap e
  let f : H ≃g G := Iso.comap e G
  have hs := planeGraph_saturated r P hq
  refine ⟨H, ⟨CliqueFree.comap f.isContained hs.free, ?_⟩, ?_, ?_⟩
  · intro x y hxy hn
    obtain ⟨t,ht,hxt⟩ := hs.common (e x) (e y) (e.injective.ne hxy) hn
    exact ⟨fun i => e.symm (t i), by simpa [H] using ht, by simpa [H] using hxt⟩
  · intro z
    calc
      Nat.card (H.neighborSet z) = Nat.card (G.neighborSet (e z)) := Nat.card_congr (f.mapNeighborSet z)
      _ = G.degree (e z) := by rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
      _ ≤ _ := planeGraph_degree_le P (by omega) (e z)
  · let x : CoreVertex q r := ⟨0,0,0,0⟩
    refine ⟨e.symm (.inl x), ?_⟩
    rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, ← f.degree_eq]
    change G.degree (e (e.symm (.inl x))) = _
    rw [e.apply_symm_apply]
    exact core_degree P (by omega) x

end Erdos917.General
