import Erdos917.AEHK.Cliques
import Erdos917.AEHK.Triangles
import Erdos917.SaturationDefinition

/-! Saturation in the standard added-edge formulation. -/

namespace Erdos917.AEHK
open SimpleGraph

variable {q : ℕ} [NeZero q]

/-- Adding any missing edge to the AEHK graph creates a five-clique. -/
theorem planeGraph_saturated (P : Plane q) (hq : 4 ≤ q) (x y : PlaneVertex P)
    (hxy : x ≠ y) (hn : ¬ (planeGraph P).Adj x y) :
    ¬ (planeGraph P ⊔ edge x y).CliqueFree 5 := by
  obtain ⟨t, ht, hxyT⟩ := planeGraph_commonTriangle P hq x y hn
  let G := planeGraph P ⊔ edge x y
  have hxy' : G.Adj x y := Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩)
  have hx (i : Fin 3) : G.Adj x (t i) := Or.inl (hxyT i).1
  have hy (i : Fin 3) : G.Adj y (t i) := Or.inl (hxyT i).2
  have htt (i j : Fin 3) (hij : i ≠ j) : G.Adj (t i) (t j) := Or.inl (ht i j hij)
  intro hfree
  apply cliqueFree_no_pairwise G hfree ![x,y,t 0,t 1,t 2]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [G.adj_comm]

/-- The common-neighborhood and added-edge definitions agree for this construction. -/
theorem planeGraph_saturatedK5 (P : Plane q) (hq : 4 ≤ q) : SaturatedK5 (planeGraph P) :=
  ⟨planeGraph_cliqueFree P hq, fun x y _ hn => planeGraph_commonTriangle P hq x y hn⟩

end Erdos917.AEHK
