import Mathlib

/-! A coordinate model of the truncated plane used by AEHK. -/

namespace Erdos917.Geometry

variable {q : ℕ} [NeZero q]

structure Plane (q : ℕ) [NeZero q] where
  Line : Type
  lineFintype : Fintype Line
  point : Line → Fin (q + 1) → ZMod q
  meet : ∀ l m, ∃ i, point l i = point m i
  through : ∀ i j, ∃ l, point l i = j
  card_lines : @Fintype.card Line lineFintype = q ^ 2
  card_through : ∀ i j, @Fintype.card {l // point l i = j}
    (by letI := lineFintype; exact inferInstance) = q

attribute [instance] Plane.lineFintype

variable (F : Type) [Field F] [Fintype F]

def lineValue (l : F × F) : Option F → F
  | none => l.1
  | some u => l.1 * u + l.2

private def lineFiber (i : Option F) (j : F) : F ≃ {l : F × F // lineValue F l i = j} :=
  match i with
  | none => {
      toFun := fun b => ⟨(j, b), rfl⟩
      invFun := fun l => l.1.2
      left_inv := fun _ => rfl
      right_inv := by intro l; apply Subtype.ext; exact Prod.ext l.2.symm rfl }
  | some u => {
      toFun := fun a => ⟨(a, j - a * u), by dsimp [lineValue]; ring⟩
      invFun := fun l => l.1.1
      left_inv := fun _ => rfl
      right_inv := by
        intro l
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rfl
        have h := l.2
        dsimp [lineValue] at h
        linear_combination -h }

noncomputable def Plane.ofField (hq : Fintype.card F = q) : Plane q := by
  classical
  let e : F ≃ ZMod q := Fintype.equivOfCardEq (by simpa using hq)
  let d : Fin (q + 1) ≃ Option F := Fintype.equivOfCardEq (by simp [hq])
  refine {
    Line := F × F
    lineFintype := inferInstance
    point := fun l i => e (lineValue F l (d i))
    meet := ?_
    through := ?_
    card_lines := by simp [Fintype.card_prod, hq, pow_two]
    card_through := ?_ }
  · intro l m
    by_cases h : l.1 = m.1
    · refine ⟨d.symm none, ?_⟩
      simp [lineValue, h]
    · refine ⟨d.symm (some ((m.2 - l.2) / (l.1 - m.1))), ?_⟩
      simp only [Equiv.apply_symm_apply, lineValue]
      apply congrArg e
      have hn : l.1 - m.1 ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring
  · intro i j
    exact ⟨(lineFiber F (d i) (e.symm j) 0).1,
      by rw [(lineFiber F (d i) (e.symm j) 0).2]; exact e.apply_symm_apply j⟩
  · intro i j
    let f : {l : F × F // e (lineValue F l (d i)) = j} ≃
        {l : F × F // lineValue F l (d i) = e.symm j} :=
      Equiv.subtypeEquivRight (fun l => e.apply_eq_iff_eq_symm_apply)
    calc
      _ = Fintype.card {l : F × F // lineValue F l (d i) = e.symm j} := Fintype.card_congr f
      _ = Fintype.card F := Fintype.card_congr (lineFiber F (d i) (e.symm j)).symm
      _ = q := hq

end Erdos917.Geometry
