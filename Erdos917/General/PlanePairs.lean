import Erdos917.AEHK.Geometry

namespace Erdos917.General
open Erdos917.AEHK

lemma lineValue_two (F : Type) [Field F] (i j : Option F) (hij : i ≠ j) (a b : F) :
    ∃ l : F × F, lineValue F l i = a ∧ lineValue F l j = b := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some v => exact ⟨(a,b-a*v),rfl,by dsimp [lineValue]; ring⟩
  | some u =>
    cases j with
    | none => exact ⟨(b,a-b*u),by dsimp [lineValue]; ring,rfl⟩
    | some v =>
      have huv : u-v ≠ 0 := sub_ne_zero.mpr (fun h => hij (congrArg some h))
      refine ⟨((a-b)/(u-v),a-(a-b)/(u-v)*u), ?_, ?_⟩
      · dsimp [lineValue]; ring
      · dsimp [lineValue]; field_simp; ring

def HasTwoPoints {q : ℕ} [NeZero q] (P : Plane q) : Prop :=
  ∀ i j, i ≠ j → ∀ a b, ∃ l, P.point l i = a ∧ P.point l j = b

lemma ofField_hasTwoPoints {q : ℕ} [NeZero q] (F : Type) [Field F] [Fintype F]
    (hq : Fintype.card F = q) : HasTwoPoints (Plane.ofField F hq) := by
  classical
  let e : F ≃ ZMod q := Fintype.equivOfCardEq (by simpa using hq)
  let d : Fin (q+1) ≃ Option F := Fintype.equivOfCardEq (by simp [hq])
  intro i j hij a b
  obtain ⟨l,ha,hb⟩ := lineValue_two F (d i) (d j) (d.injective.ne hij) (e.symm a) (e.symm b)
  refine ⟨l, ?_, ?_⟩
  · change e (lineValue F l (d i)) = a
    rw [ha,e.apply_symm_apply]
  · change e (lineValue F l (d j)) = b
    rw [hb,e.apply_symm_apply]

end Erdos917.General
