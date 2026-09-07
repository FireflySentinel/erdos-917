import Erdos917.AEHK.Core

/-! Exact vertex counts and both vertex degrees in the AEHK graph. -/

namespace Erdos917.AEHK
open Finset SimpleGraph

variable {q : ℕ} [NeZero q]

private abbrev Fiber (x : CoreVertex q) (i : Fin (q + 1)) :=
  {p : ZMod q × ZMod 3 × Fin 4 // coreAdj x ⟨i, p.1, p.2.1, p.2.2⟩}

private def sameFiber (x : CoreVertex q) : Fiber x x.level ≃
    {c : Fin 4 // x.copy ≠ c} × {p : ZMod q × ZMod 3 // (x.place, x.kind) ≠ p} where
  toFun p :=
    let h := (coreAdj_same (x := x) (y := ⟨x.level,p.1.1,p.1.2.1,p.1.2.2⟩) rfl).mp p.2
    (⟨p.1.2.2, h.1⟩, ⟨(p.1.1, p.1.2.1), by
      intro he
      exact h.2.elim (fun h => h (congrArg Prod.fst he)) (fun h => h (congrArg Prod.snd he))⟩)
  invFun p := ⟨(p.2.1.1, p.2.1.2, p.1.1), Or.inl ⟨rfl, p.1.2, by
    by_contra h
    push Not at h
    exact p.2.2 (Prod.ext h.1 h.2)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def upperFiber (x : CoreVertex q) (i : Fin (q + 1)) (hi : x.level < i) :
    Fiber x i ≃ successors x.place × Fin 4 where
  toFun p :=
    (⟨p.1.1, ((coreAdj_lt (x := x) (y := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) hi).mp p.2).2⟩, p.1.2.2)
  invFun p := ⟨(p.1.1, x.kind + 1, p.2), Or.inr (Or.inl ⟨hi, rfl, p.1.2⟩)⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    exact ((coreAdj_lt (x := x) (y := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) hi).mp p.2).1.symm
  right_inv _ := rfl

private def lowerFiber (x : CoreVertex q) (i : Fin (q + 1)) (hi : i < x.level) :
    Fiber x i ≃ predecessors x.place × Fin 4 where
  toFun p :=
    (⟨p.1.1, mem_predecessors_iff.mpr
      ((coreAdj_lt (x := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) (y := x) hi).mp (coreAdj_symm p.2)).2⟩,
      p.1.2.2)
  invFun p := ⟨(p.1.1, x.kind - 1, p.2), Or.inr (Or.inr
    ⟨hi, by dsimp; ring, mem_predecessors_iff.mp p.1.2⟩)⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    have h := ((coreAdj_lt (x := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) (y := x) hi).mp (coreAdj_symm p.2)).1
    dsimp
    linear_combination h
  right_inv _ := rfl

private lemma fiber_card_same (x : CoreVertex q) :
    Fintype.card (Fiber x x.level) = 3 * (3 * q - 1) := by
  rw [Fintype.card_congr (sameFiber x)]
  simp [Fintype.card_prod, Fintype.card_subtype_compl, mul_comm]

private lemma fiber_card_other (hq : 4 ≤ q) (x : CoreVertex q) (i : Fin (q + 1))
    (hi : i ≠ x.level) : Fintype.card (Fiber x i) = 12 := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · rw [Fintype.card_congr (lowerFiber x i hi)]
    simp [Fintype.card_prod, predecessors_card hq]
  · rw [Fintype.card_congr (upperFiber x i hi)]
    simp [Fintype.card_prod, successors_card hq]

private def coreNeighborEquiv (x : CoreVertex q) :
    {y // coreAdj x y} ≃ (i : Fin (q + 1)) × Fiber x i where
  toFun y := ⟨y.1.level, ⟨(y.1.place, y.1.kind, y.1.copy), y.2⟩⟩
  invFun p := ⟨⟨p.1, p.2.1.1, p.2.1.2.1, p.2.1.2.2⟩, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma core_neighbor_card (hq : 4 ≤ q) (x : CoreVertex q) :
    Fintype.card {y // coreAdj x y} = 3 * (3 * q - 1) + 12 * q := by
  rw [Fintype.card_congr (coreNeighborEquiv x), Fintype.card_sigma]
  have he : ∀ i, Fintype.card (Fiber x i) = if i = x.level then 3 * (3 * q - 1) else 12 := by
    intro i
    split_ifs with hi
    · subst i; exact fiber_card_same x
    · exact fiber_card_other hq x i hi
  simp_rw [he]
  rw [sum_ite]
  simp [filter_eq', filter_ne', mul_comm]

private def coreAllNeighbors (P : Plane q) (x : CoreVertex q) :
    (planeGraph P).neighborSet (.inl x) ≃
      {y // coreAdj x y} ⊕ {l // P.point l x.level = x.place} where
  toFun y := match y with
    | ⟨.inl y, h⟩ => .inl ⟨y, h⟩
    | ⟨.inr l, h⟩ => .inr ⟨l, h⟩
  invFun y := match y with
    | .inl ⟨y,h⟩ => ⟨.inl y,h⟩
    | .inr ⟨l,h⟩ => ⟨.inr l,h⟩
  left_inv := by rintro ⟨y,h⟩; cases y <;> rfl
  right_inv := by intro y; cases y <;> rfl

/-- Every core vertex has the same degree. -/
theorem core_degree (P : Plane q) (hq : 4 ≤ q) (x : CoreVertex q) :
    (planeGraph P).degree (.inl x) = 22 * q - 3 := by
  classical
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (coreAllNeighbors P x),
    Fintype.card_sum, core_neighbor_card hq, P.card_through]
  omega

private def lineNeighbors (P : Plane q) (l : P.Line) :
    (planeGraph P).neighborSet (.inr l) ≃ Fin (q + 1) × ZMod 3 × Fin 4 where
  toFun y := match y with
    | ⟨.inl x, _⟩ => (x.level, x.kind, x.copy)
    | ⟨.inr _, h⟩ => False.elim h
  invFun p := ⟨.inl ⟨p.1, P.point l p.1, p.2.1, p.2.2⟩, rfl⟩
  left_inv := by
    rintro ⟨x,h⟩
    cases x with
    | inl x =>
      apply Subtype.ext
      apply congrArg Sum.inl
      cases x
      simp only [CoreVertex.mk.injEq]
      exact ⟨trivial,h,trivial,trivial⟩
    | inr _ => exact False.elim h
  right_inv _ := rfl

/-- Every added line vertex has degree `12 (q + 1)`. -/
theorem line_degree (P : Plane q) (l : P.Line) :
    (planeGraph P).degree (.inr l) = 12 * (q + 1) := by
  classical
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (lineNeighbors P l)]
  simp [Fintype.card_prod]
  ring

lemma planeVertex_card (P : Plane q) : Fintype.card (PlaneVertex P) = 13 * q ^ 2 + 12 * q := by
  let e : CoreVertex q ≃ Fin (q + 1) × ZMod q × ZMod 3 × Fin 4 := {
    toFun := fun x => (x.level, x.place, x.kind, x.copy)
    invFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_sum, Fintype.card_congr e, P.card_lines]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  ring

lemma planeGraph_degree_le (P : Plane q) (hq : 4 ≤ q) (z : PlaneVertex P) :
    (planeGraph P).degree z ≤ 22 * q - 3 := by
  cases z with
  | inl x => exact (core_degree P hq x).le
  | inr l => rw [line_degree]; omega


/-- The maximum is attained at every core vertex. -/
theorem planeGraph_maxDegree (P : Plane q) (hq : 4 ≤ q) :
    (planeGraph P).maxDegree = 22 * q - 3 := by
  apply le_antisymm
  · exact (planeGraph P).maxDegree_le_of_forall_degree_le _ (planeGraph_degree_le P hq)
  · have h := (planeGraph P).degree_le_maxDegree (.inl ⟨0,0,0,0⟩)
    rwa [core_degree P hq] at h

end Erdos917.AEHK
