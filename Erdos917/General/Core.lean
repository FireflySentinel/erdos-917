import Erdos917.General.CyclicIntervals
import Erdos917.Geometry

/-! The AEHK core and its independent line vertices. -/

namespace Erdos917.General
open Finset SimpleGraph Erdos917.Geometry

variable {q r : ℕ} [NeZero q]

structure CoreVertex (q r : ℕ) where
  level : Fin (q + 1)
  place : ZMod q
  kind : ZMod (r+2)
  copy : Fin (r+3)
  deriving DecidableEq

instance : Fintype (CoreVertex q r) :=
  Fintype.ofEquiv (Fin (q + 1) × ZMod q × ZMod (r+2) × Fin (r+3))
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun x => (x.level, x.place, x.kind, x.copy)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def coreAdj (x y : CoreVertex q r) : Prop :=
  (x.level = y.level ∧ x.copy ≠ y.copy ∧ (x.place ≠ y.place ∨ x.kind ≠ y.kind)) ∨
  (x.level < y.level ∧ y.kind = x.kind + 1 ∧ y.place ∈ successors (r+2) x.place) ∨
  (y.level < x.level ∧ x.kind = y.kind + 1 ∧ x.place ∈ successors (r+2) y.place)

instance (x y : CoreVertex q r) : Decidable (coreAdj x y) := by
  unfold coreAdj
  infer_instance

omit [NeZero q] in
lemma coreAdj_symm {x y : CoreVertex q r} (h : coreAdj x y) : coreAdj y x := by
  rcases h with ⟨hl,hc,hp | ht⟩ | h | h
  · exact Or.inl ⟨hl.symm, hc.symm, Or.inl hp.symm⟩
  · exact Or.inl ⟨hl.symm, hc.symm, Or.inr ht.symm⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

omit [NeZero q] in
lemma coreAdj_irrefl (x : CoreVertex q r) : ¬ coreAdj x x := by simp [coreAdj]

def coreGraph : SimpleGraph (CoreVertex q r) where
  Adj := coreAdj
  symm := ⟨fun _ _ h => coreAdj_symm h⟩
  loopless := ⟨coreAdj_irrefl⟩

abbrev PlaneVertex (r : ℕ) (P : Plane q) := CoreVertex q r ⊕ P.Line

def planeGraph (r : ℕ) (P : Plane q) : SimpleGraph (PlaneVertex r P) where
  Adj
    | .inl x, .inl y => coreAdj x y
    | .inl x, .inr l => P.point l x.level = x.place
    | .inr l, .inl x => P.point l x.level = x.place
    | .inr _, .inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact coreAdj_symm h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x
    cases x
    · exact coreAdj_irrefl _
    · exact id⟩

instance (P : Plane q) : DecidableRel (planeGraph r P).Adj := by
  intro x y
  cases x <;> cases y <;> unfold planeGraph coreAdj <;> infer_instance

omit [NeZero q] in
lemma coreAdj_same {x y : CoreVertex q r} (h : x.level = y.level) :
    coreAdj x y ↔ x.copy ≠ y.copy ∧ (x.place ≠ y.place ∨ x.kind ≠ y.kind) := by
  simp [coreAdj, h]

omit [NeZero q] in
lemma coreAdj_lt {x y : CoreVertex q r} (h : x.level < y.level) :
    coreAdj x y ↔ y.kind = x.kind + 1 ∧ y.place ∈ successors (r+2) x.place := by
  simp [coreAdj, ne_of_lt h, h, not_lt.mpr h.le]

omit [NeZero q] in
lemma no_three_levels {x y z : CoreVertex q r}
    (hxy : coreAdj x y) (hyz : coreAdj y z) (hxz : coreAdj x z)
    (hij : x.level < y.level) (hjk : y.level < z.level) : False := by
  have h1 := (coreAdj_lt hij).mp hxy
  have h2 := (coreAdj_lt hjk).mp hyz
  have h3 := (coreAdj_lt (lt_trans hij hjk)).mp hxz
  have h : (1 : ZMod (r+2)) = 0 := by linear_combination h3.1 - h1.1 - h2.1
  have hv := ZMod.one_eq_zero_iff.mp h
  omega

end Erdos917.General
