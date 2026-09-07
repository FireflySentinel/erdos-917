import Mathlib

/-! The three consecutive places used in the AEHK core. -/

namespace Erdos917.AEHK
open Finset

variable {q : ℕ}

def successors (j : ZMod q) : Finset (ZMod q) := {j + 1, j + 2, j + 3}

def predecessors (j : ZMod q) : Finset (ZMod q) := {j - 1, j - 2, j - 3}

private lemma small_cast_ne {a b : ℕ} (ha : a < q) (hb : b < q) (hab : a ≠ b) :
    (a : ZMod q) ≠ (b : ZMod q) := by
  intro h
  have hv := congrArg ZMod.val h
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hab hv

lemma successors_card (hq : 4 ≤ q) (j : ZMod q) : (successors j).card = 3 := by
  have h12 : (1 : ZMod q) ≠ 2 := by
    simpa using small_cast_ne (q := q) (a := 1) (b := 2) (by omega) (by omega) (by omega)
  have h13 : (1 : ZMod q) ≠ 3 := by
    simpa using small_cast_ne (q := q) (a := 1) (b := 3) (by omega) (by omega) (by omega)
  have h23 : (2 : ZMod q) ≠ 3 := by
    simpa using small_cast_ne (q := q) (a := 2) (b := 3) (by omega) (by omega) (by omega)
  simp [successors, h12, h13, h23]

lemma not_mem_successors (hq : 4 ≤ q) (j : ZMod q) : j ∉ successors j := by
  have h1 : (0 : ZMod q) ≠ 1 := by
    simpa using small_cast_ne (q := q) (a := 0) (b := 1) (by omega) (by omega) (by omega)
  have h2 : (0 : ZMod q) ≠ 2 := by
    simpa using small_cast_ne (q := q) (a := 0) (b := 2) (by omega) (by omega) (by omega)
  have h3 : (0 : ZMod q) ≠ 3 := by
    simpa using small_cast_ne (q := q) (a := 0) (b := 3) (by omega) (by omega) (by omega)
  simp only [successors, mem_insert, mem_singleton]
  rintro (h | h | h) <;> [exact h1 (by linear_combination h);
    exact h2 (by linear_combination h); exact h3 (by linear_combination h)]

lemma successors_injective (hq : 4 ≤ q) : Function.Injective (successors (q := q)) := by
  intro a b h
  have hb : b + 1 ∈ successors a := by rw [h]; simp [successors]
  have hn : b ∉ successors a := by rw [h]; exact not_mem_successors hq b
  simp only [successors, mem_insert, mem_singleton] at hb
  rcases hb with he | he | he
  · exact (add_right_cancel he).symm
  · exfalso
    apply hn
    have hb' : b = a + 1 := by linear_combination he
    simp [hb', successors]
  · exfalso
    apply hn
    have hb' : b = a + 2 := by linear_combination he
    simp [hb', successors]

lemma mem_predecessors_iff {a b : ZMod q} : a ∈ predecessors b ↔ b ∈ successors a := by
  simp only [predecessors, successors, mem_insert, mem_singleton]
  constructor <;> rintro (h | h | h)
  · exact Or.inl (by linear_combination -h)
  · exact Or.inr (Or.inl (by linear_combination -h))
  · exact Or.inr (Or.inr (by linear_combination -h))
  · exact Or.inl (by linear_combination -h)
  · exact Or.inr (Or.inl (by linear_combination -h))
  · exact Or.inr (Or.inr (by linear_combination -h))

lemma neg_mem_successors_iff {a b : ZMod q} : -a ∈ successors (-b) ↔ a ∈ predecessors b := by
  simp only [predecessors, successors, mem_insert, mem_singleton]
  constructor <;> rintro (h | h | h)
  · exact Or.inl (by linear_combination -h)
  · exact Or.inr (Or.inl (by linear_combination -h))
  · exact Or.inr (Or.inr (by linear_combination -h))
  · exact Or.inl (by linear_combination -h)
  · exact Or.inr (Or.inl (by linear_combination -h))
  · exact Or.inr (Or.inr (by linear_combination -h))

lemma predecessors_eq_neg (j : ZMod q) :
    predecessors j = (successors (-j)).image Neg.neg := by
  ext x
  simp only [mem_image]
  constructor
  · intro h; exact ⟨-x, neg_mem_successors_iff.mpr h, neg_neg x⟩
  · rintro ⟨a, ha, rfl⟩
    exact neg_mem_successors_iff.mp (by simpa using ha)

lemma predecessors_card (hq : 4 ≤ q) (j : ZMod q) : (predecessors j).card = 3 := by
  rw [predecessors_eq_neg, card_image_of_injective _ neg_injective, successors_card hq]

lemma predecessors_injective (hq : 4 ≤ q) : Function.Injective (predecessors (q := q)) := by
  intro a b h
  apply neg_injective
  apply successors_injective hq
  ext x
  have he := Finset.ext_iff.mp h (-x)
  simpa only [← neg_mem_successors_iff, neg_neg] using he

end Erdos917.AEHK
