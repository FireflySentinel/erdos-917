import Erdos917.General.Core

/-! Exact vertex counts and both vertex degrees in the AEHK graph. -/

namespace Erdos917.General
open Finset SimpleGraph Erdos917.Geometry

variable {q r : ℕ} [NeZero q]

private abbrev Fiber (x : CoreVertex q r) (i : Fin (q + 1)) :=
  {p : ZMod q × ZMod (r+2) × Fin (r+3) // coreAdj x ⟨i, p.1, p.2.1, p.2.2⟩}

private def sameFiber (x : CoreVertex q r) : Fiber x x.level ≃
    {c : Fin (r+3) // x.copy ≠ c} × {p : ZMod q × ZMod (r+2) // (x.place, x.kind) ≠ p} where
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

private def upperFiber (x : CoreVertex q r) (i : Fin (q + 1)) (hi : x.level < i) :
    Fiber x i ≃ successors (r+2) x.place × Fin (r+3) where
  toFun p :=
    (⟨p.1.1, ((coreAdj_lt (x := x) (y := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) hi).mp p.2).2⟩, p.1.2.2)
  invFun p := ⟨(p.1.1, x.kind + 1, p.2), Or.inr (Or.inl ⟨hi, rfl, p.1.2⟩)⟩
  left_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    exact ((coreAdj_lt (x := x) (y := ⟨i,p.1.1,p.1.2.1,p.1.2.2⟩) hi).mp p.2).1.symm
  right_inv _ := rfl

private def lowerFiber (x : CoreVertex q r) (i : Fin (q + 1)) (hi : i < x.level) :
    Fiber x i ≃ predecessors (r+2) x.place × Fin (r+3) where
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

private lemma fiber_card_same (x : CoreVertex q r) :
    Fintype.card (Fiber x x.level) = (r+2) * ((r+2) * q - 1) := by
  rw [Fintype.card_congr (sameFiber x)]
  simp [Fintype.card_prod, Fintype.card_subtype_compl, mul_comm]

private lemma fiber_card_other (hq : r+3 ≤ q) (x : CoreVertex q r) (i : Fin (q + 1))
    (hi : i ≠ x.level) : Fintype.card (Fiber x i) = (r+2)*(r+3) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · rw [Fintype.card_congr (lowerFiber x i hi)]
    simp [Fintype.card_prod, predecessors_card (by omega : r+2 < q)]
  · rw [Fintype.card_congr (upperFiber x i hi)]
    simp [Fintype.card_prod, successors_card (by omega : r+2 < q)]

private def coreNeighborEquiv (x : CoreVertex q r) :
    {y // coreAdj x y} ≃ (i : Fin (q + 1)) × Fiber x i where
  toFun y := ⟨y.1.level, ⟨(y.1.place, y.1.kind, y.1.copy), y.2⟩⟩
  invFun p := ⟨⟨p.1, p.2.1.1, p.2.1.2.1, p.2.1.2.2⟩, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma core_neighbor_card (hq : r+3 ≤ q) (x : CoreVertex q r) :
    Fintype.card {y // coreAdj x y} = (r+2) * ((r+2) * q - 1) + (r+2)*(r+3) * q := by
  rw [Fintype.card_congr (coreNeighborEquiv x), Fintype.card_sigma]
  have he : ∀ i, Fintype.card (Fiber x i) = if i = x.level then (r+2) * ((r+2) * q - 1) else (r+2)*(r+3) := by
    intro i
    split_ifs with hi
    · subst i; exact fiber_card_same x
    · exact fiber_card_other hq x i hi
  simp_rw [he]
  rw [sum_ite]
  simp [filter_eq', filter_ne', mul_comm]

private def coreAllNeighbors (P : Plane q) (x : CoreVertex q r) :
    (planeGraph r P).neighborSet (.inl x) ≃
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
theorem core_degree (P : Plane q) (hq : r+3 ≤ q) (x : CoreVertex q r) :
    (planeGraph r P).degree (.inl x) = q*((r+2)*(2*r+5)+1)-(r+2) := by
  classical
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (coreAllNeighbors P x),
    Fintype.card_sum, core_neighbor_card hq, P.card_through]
  have hs := Nat.sub_add_cancel (show 1 ≤ (r+2)*q by have := NeZero.pos q; nlinarith)
  have he : (r+2)*((r+2)*q-1)+(r+2)*(r+3)*q+q+(r+2) =
      q*((r+2)*(2*r+5)+1) := by
    nlinarith only [congrArg (fun z : ℕ => (r+2)*z) hs]
  omega

private def lineNeighbors (P : Plane q) (l : P.Line) :
    (planeGraph r P).neighborSet (.inr l) ≃ Fin (q + 1) × ZMod (r+2) × Fin (r+3) where
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

/-- Every added line vertex has degree `(r + 2) (r + 3) (q + 1)`. -/
theorem line_degree (r : ℕ) (P : Plane q) (l : P.Line) :
    (planeGraph r P).degree (.inr l) = (r+2)*(r+3) * (q + 1) := by
  classical
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (lineNeighbors P l)]
  simp [Fintype.card_prod]
  ring

lemma planeVertex_card (r : ℕ) (P : Plane q) : Fintype.card (PlaneVertex r P) = (r+2)*(r+3)*(q^2+q)+q^2 := by
  let e : CoreVertex q r ≃ Fin (q + 1) × ZMod q × ZMod (r+2) × Fin (r+3) := {
    toFun := fun x => (x.level, x.place, x.kind, x.copy)
    invFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_sum, Fintype.card_congr e, P.card_lines]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  ring

lemma planeGraph_degree_le (P : Plane q) (hq : r+3 ≤ q) (z : PlaneVertex r P) :
    (planeGraph r P).degree z ≤ q*((r+2)*(2*r+5)+1)-(r+2) := by
  cases z with
  | inl x => exact (core_degree P hq x).le
  | inr l =>
    rw [line_degree]
    have h1 := Nat.mul_le_mul_right ((r+2)^2+1) hq
    have h2 : (r+2)*(r+4) ≤ (r+3)*((r+2)^2+1) := by
      nlinarith [Nat.zero_le (r^3), Nat.zero_le (r^2)]
    have hb : (r+2)*(r+3)*(q+1)+(r+2) ≤ q*((r+2)*(2*r+5)+1) := by
      nlinarith only [h1,h2]
    omega


/-- The maximum is attained at every core vertex. -/
theorem planeGraph_maxDegree (r : ℕ) (P : Plane q) (hq : r+3 ≤ q) :
    (planeGraph r P).maxDegree = q*((r+2)*(2*r+5)+1)-(r+2) := by
  apply le_antisymm
  · exact (planeGraph r P).maxDegree_le_of_forall_degree_le _ (planeGraph_degree_le P hq)
  · have h := (planeGraph r P).degree_le_maxDegree (.inl ⟨0,0,0,0⟩)
    rwa [core_degree P hq] at h

end Erdos917.General
