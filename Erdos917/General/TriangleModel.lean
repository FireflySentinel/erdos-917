import Erdos917.General.PlanePairs
import Erdos917.General.SaturationDefinition

/-! The three-saturated case has no edges between different core levels. -/
namespace Erdos917.General
open Finset SimpleGraph Erdos917.Geometry
variable {q : ℕ} [NeZero q]

abbrev TriangleCore (q : ℕ) := Fin (q+1) × ZMod q × Bool
abbrev TriangleVertex (P : Plane q) := TriangleCore q ⊕ P.Line

def triangleAdj (x y : TriangleCore q) : Prop :=
  x.1 = y.1 ∧ x.2.1 ≠ y.2.1 ∧ x.2.2 ≠ y.2.2

def triangleGraph (P : Plane q) : SimpleGraph (TriangleVertex P) where
  Adj
    | .inl x, .inl y => triangleAdj x y
    | .inl x, .inr l => P.point l x.1 = x.2.1
    | .inr l, .inl x => P.point l x.1 = x.2.1
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (x|l) (y|m) h
    · exact ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by rintro (x|l) h; exact h.2.1 rfl; exact h⟩

instance (P : Plane q) : DecidableRel (triangleGraph P).Adj := by
  rintro (x|l) (y|m) <;> unfold triangleGraph triangleAdj <;> infer_instance

lemma triangleGraph_free (P : Plane q) : (triangleGraph P).CliqueFree 3 := by
  classical
  intro C hC
  have hc := hC.isClique
  have hcAdj : (C.toLeft : Set (TriangleCore q)).Pairwise triangleAdj := by
    intro x hx y hy hxy
    exact hc (mem_toLeft.mp hx) (mem_toLeft.mp hy) (Sum.inl_injective.ne hxy)
  have hcore : C.toLeft.card ≤ 2 := by
    have hi : Set.InjOn (fun x : TriangleCore q => x.2.2) C.toLeft := by
      intro x hx y hy he
      by_contra hn
      exact (hcAdj hx hy hn).2.2 he
    calc
      C.toLeft.card = (C.toLeft.image (fun x => x.2.2)).card := (card_image_of_injOn hi).symm
      _ ≤ Fintype.card Bool := card_le_univ _
      _ = 2 := by simp
  have hline : C.toRight.card ≤ 1 := by
    apply card_le_one.mpr
    intro l hl m hm
    by_contra hn
    exact hc (mem_toRight.mp hl) (mem_toRight.mp hm) (Sum.inr_injective.ne hn)
  have hs := card_toLeft_add_card_toRight (u := C)
  have hn := hC.card_eq
  by_cases hb : C.toRight.Nonempty
  · obtain ⟨l,hl⟩ := hb
    have hleft : C.toLeft.card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra hxy
      have ha := hcAdj hx hy hxy
      have hxl : P.point l x.1 = x.2.1 := hc (mem_toRight.mp hl) (mem_toLeft.mp hx) (by simp)
      have hyl : P.point l y.1 = y.2.1 := hc (mem_toRight.mp hl) (mem_toLeft.mp hy) (by simp)
      exact ha.2.1 (by rw [← hxl,← hyl,ha.1])
    omega
  · have hz : C.toRight.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hb)
    omega

lemma triangleGraph_common (P : Plane q) (hP : HasTwoPoints P) (hq : 3 ≤ q)
    (x y : TriangleVertex P) (hn : ¬ (triangleGraph P).Adj x y) :
    ∃ z, (triangleGraph P).Adj x z ∧ (triangleGraph P).Adj y z := by
  classical
  rcases x with x|l <;> rcases y with y|m
  · by_cases hl : x.1 = y.1
    · by_cases hcopy : x.2.2 = y.2.2
      · have hplaces : (univ \ {x.2.1,y.2.1} : Finset (ZMod q)).Nonempty := by
          apply card_pos.mp
          rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card]
          have hb : ({x.2.1,y.2.1} : Finset (ZMod q)).card ≤ 2 := by
            by_cases he : x.2.1 = y.2.1 <;> simp [he]
          omega
        obtain ⟨j,hj⟩ := hplaces
        have hj' : j ≠ x.2.1 ∧ j ≠ y.2.1 := by simpa using (mem_sdiff.mp hj).2
        refine ⟨.inl (x.1,j,!x.2.2), ⟨rfl,hj'.1.symm,by simp⟩, ?_⟩
        exact ⟨hl.symm,hj'.2.symm,by simp [← hcopy]⟩
      · have hp : x.2.1 = y.2.1 := by
          by_contra hp
          exact hn ⟨hl,hp,hcopy⟩
        obtain ⟨l,hlp⟩ := P.through x.1 x.2.1
        exact ⟨.inr l,hlp,by change P.point l y.1 = y.2.1; rw [← hl,← hp]; exact hlp⟩
    · obtain ⟨l,hx,hy⟩ := hP x.1 y.1 hl x.2.1 y.2.1
      exact ⟨.inr l,hx,hy⟩
  · exact ⟨.inl (x.1,P.point m x.1,!x.2.2),⟨rfl,Ne.symm hn,by simp⟩,rfl⟩
  · exact ⟨.inl (y.1,P.point l y.1,!y.2.2),rfl,⟨rfl,Ne.symm hn,by simp⟩⟩
  · obtain ⟨i,hi⟩ := P.meet l m
    exact ⟨.inl (i,P.point l i,false),rfl,hi.symm⟩

lemma triangleGraph_saturated (P : Plane q) (hP : HasTwoPoints P) (hq : 3 ≤ q) :
    Saturated 0 (triangleGraph P) := by
  refine ⟨triangleGraph_free P, ?_⟩
  intro x y _ hn
  obtain ⟨z,hxz,hyz⟩ := triangleGraph_common P hP hq x y hn
  exact ⟨fun _ => z,fun i j hij => False.elim (hij (Fin.ext (by omega))),fun _ => ⟨hxz,hyz⟩⟩

private def triangleCoreNeighbors (x : TriangleCore q) :
    {y // triangleAdj x y} ≃ {j : ZMod q // j ≠ x.2.1} where
  toFun y := ⟨y.1.2.1,y.2.2.1.symm⟩
  invFun j := ⟨(x.1,j.1,!x.2.2),⟨rfl,j.2.symm,by simp⟩⟩
  left_inv y := by
    apply Subtype.ext
    refine Prod.ext y.2.1 (Prod.ext rfl ?_)
    have h := y.2.2.2
    change (!x.2.2) = y.1.2.2
    cases hx : x.2.2 <;> cases hy : y.1.2.2 <;> simp_all
  right_inv _ := rfl

private def triangleAllNeighbors (P : Plane q) (x : TriangleCore q) :
    (triangleGraph P).neighborSet (.inl x) ≃
      {y // triangleAdj x y} ⊕ {l // P.point l x.1 = x.2.1} where
  toFun y := match y with
    | ⟨.inl y,h⟩ => .inl ⟨y,h⟩
    | ⟨.inr l,h⟩ => .inr ⟨l,h⟩
  invFun y := match y with
    | .inl ⟨y,h⟩ => ⟨.inl y,h⟩
    | .inr ⟨l,h⟩ => ⟨.inr l,h⟩
  left_inv := by rintro ⟨y,h⟩; cases y <;> rfl
  right_inv := by intro y; cases y <;> rfl

lemma triangleCore_degree (P : Plane q) (x : TriangleCore q) :
    (triangleGraph P).degree (.inl x) = 2*q-1 := by
  classical
  rw [← card_neighborSet_eq_degree,Fintype.card_congr (triangleAllNeighbors P x),
    Fintype.card_sum,Fintype.card_congr (triangleCoreNeighbors x),P.card_through]
  simp only [Fintype.card_subtype_compl,Fintype.card_unique,ZMod.card]
  have := NeZero.pos q
  omega

private def triangleLineNeighbors (P : Plane q) (l : P.Line) :
    (triangleGraph P).neighborSet (.inr l) ≃ Fin (q+1) × Bool where
  toFun y := match y with
    | ⟨.inl x,h⟩ => (x.1,x.2.2)
    | ⟨.inr _,h⟩ => False.elim h
  invFun p := ⟨.inl (p.1,P.point l p.1,p.2),rfl⟩
  left_inv := by
    rintro ⟨x,h⟩
    cases x with
    | inl x =>
      apply Subtype.ext
      apply congrArg Sum.inl
      exact Prod.ext rfl (Prod.ext h rfl)
    | inr l => exact False.elim h
  right_inv _ := rfl

lemma triangleLine_degree (P : Plane q) (l : P.Line) :
    (triangleGraph P).degree (.inr l) = 2*(q+1) := by
  classical
  rw [← card_neighborSet_eq_degree,Fintype.card_congr (triangleLineNeighbors P l)]
  simp [mul_comm]

lemma triangle_degree_le (P : Plane q) (_hq : 3 ≤ q) (z : TriangleVertex P) :
    (triangleGraph P).degree z ≤ 2*(q+1) := by
  cases z with
  | inl x => rw [triangleCore_degree]; omega
  | inr l => rw [triangleLine_degree]

lemma triangleVertex_card (P : Plane q) :
    Fintype.card (TriangleVertex P) = 3*q^2+2*q := by
  simp only [TriangleVertex,TriangleCore,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,ZMod.card,Fintype.card_bool,P.card_lines]
  ring

theorem exists_triangle_model (P : Plane q) (hP : HasTwoPoints P) (hq : 3 ≤ q) :
    ∃ G : SimpleGraph (Fin (3*q^2+2*q)), Saturated 0 G ∧
      (∀ z, Nat.card (G.neighborSet z) ≤ 2*(q+1)) ∧
      ∃ z, Nat.card (G.neighborSet z) = 2*(q+1) := by
  classical
  let e : Fin (3*q^2+2*q) ≃ TriangleVertex P :=
    (Fintype.equivFinOfCardEq (triangleVertex_card P)).symm
  let G := triangleGraph P
  let H := G.comap e
  let f : H ≃g G := Iso.comap e G
  have hs := triangleGraph_saturated P hP hq
  refine ⟨H, ⟨CliqueFree.comap f.isContained hs.free, ?_⟩, ?_, ?_⟩
  · intro x y hxy hn
    obtain ⟨t,ht,hxt⟩ := hs.common (e x) (e y) (e.injective.ne hxy) hn
    exact ⟨fun i => e.symm (t i),by simp [H],by simpa [H] using hxt⟩
  · intro z
    calc
      Nat.card (H.neighborSet z) = Nat.card (G.neighborSet (e z)) := Nat.card_congr (f.mapNeighborSet z)
      _ = G.degree (e z) := by rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
      _ ≤ _ := triangle_degree_le P hq (e z)

  · obtain ⟨l,_⟩ := P.through 0 0
    refine ⟨e.symm (.inr l),?_⟩
    rw [Nat.card_congr (f.mapNeighborSet _),Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
    change G.degree (e (e.symm (.inr l))) = _
    rw [e.apply_symm_apply]
    exact triangleLine_degree P l

end Erdos917.General
