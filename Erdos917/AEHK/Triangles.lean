import Erdos917.AEHK.Core

/-! Explicit common-neighborhood triangles for every kind of missing edge. -/

namespace Erdos917.AEHK
open Finset SimpleGraph

variable {q : ℕ} [NeZero q]

noncomputable def kinds : Fin 3 ≃ ZMod 3 := Fintype.equivOfCardEq (by simp)

def CommonTriangle (P : Plane q) (x y : PlaneVertex P) : Prop :=
  ∃ t : Fin 3 → PlaneVertex P,
    (∀ i j, i ≠ j → (planeGraph P).Adj (t i) (t j)) ∧
    ∀ i, (planeGraph P).Adj x (t i) ∧ (planeGraph P).Adj y (t i)

lemma CommonTriangle.symm {P : Plane q} {x y : PlaneVertex P} (h : CommonTriangle P x y) :
    CommonTriangle P y x := by
  obtain ⟨t, ht, hxy⟩ := h
  exact ⟨t, ht, fun i => (hxy i).symm⟩

omit [NeZero q] in
private lemma on_level (i : Fin (q + 1)) (p : Fin 3 → ZMod q) (t : Fin 3 → ZMod 3)
    (c : Fin 3 ↪ Fin 4) (h : ∀ r s, r ≠ s → p r ≠ p s ∨ t r ≠ t s) :
    ∀ r s, r ≠ s → coreAdj (⟨i, p r, t r, c r⟩ : CoreVertex q) ⟨i, p s, t s, c s⟩ := by
  intro r s hrs
  exact Or.inl ⟨rfl, c.injective.ne hrs, h r s hrs⟩

private lemma from_three {P : Plane q} {x y a b c : PlaneVertex P}
    (hab : (planeGraph P).Adj a b) (hac : (planeGraph P).Adj a c) (hbc : (planeGraph P).Adj b c)
    (hx : (planeGraph P).Adj x a ∧ (planeGraph P).Adj x b ∧ (planeGraph P).Adj x c)
    (hy : (planeGraph P).Adj y a ∧ (planeGraph P).Adj y b ∧ (planeGraph P).Adj y c) :
    CommonTriangle P x y := by
  refine ⟨![a,b,c], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [(planeGraph P).adj_comm]
  · intro i
    fin_cases i <;> simp_all

lemma line_line_triangle (P : Plane q) (l m : P.Line) :
    CommonTriangle P (.inr l) (.inr m) := by
  obtain ⟨i, hi⟩ := P.meet l m
  let c := (0 : Fin 4).succAboveEmb
  refine ⟨fun r => .inl ⟨i, P.point l i, kinds r, c r⟩, ?_, ?_⟩
  · exact on_level i _ _ c (fun r s hrs => Or.inr (kinds.injective.ne hrs))
  · intro r
    exact ⟨rfl, hi.symm⟩

lemma line_core_triangle (P : Plane q) (x : CoreVertex q) (l : P.Line)
    (hn : ¬ (planeGraph P).Adj (.inl x) (.inr l)) :
    CommonTriangle P (.inl x) (.inr l) := by
  let c := x.copy.succAboveEmb
  refine ⟨fun r => .inl ⟨x.level, P.point l x.level, kinds r, c r⟩, ?_, ?_⟩
  · exact on_level x.level _ _ c (fun r s hrs => Or.inr (kinds.injective.ne hrs))
  · intro r
    exact ⟨Or.inl ⟨rfl, Fin.ne_succAbove x.copy r, Or.inl (Ne.symm hn)⟩, rfl⟩

lemma same_copy_triangle (P : Plane q) (hq : 4 ≤ q) (x y : CoreVertex q)
    (hl : x.level = y.level) (hc : x.copy = y.copy) :
    CommonTriangle P (.inl x) (.inl y) := by
  classical
  have hs : (univ \ {x.place, y.place} : Finset (ZMod q)).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
    have hp : ({x.place, y.place} : Finset (ZMod q)).card ≤ 2 := by
      by_cases h : x.place = y.place <;> simp [h]
    omega
  obtain ⟨j, hj⟩ := hs
  have hj' : j ≠ x.place ∧ j ≠ y.place := by simpa using (mem_sdiff.mp hj).2
  have hjx := hj'.1
  have hjy := hj'.2
  let c := x.copy.succAboveEmb
  refine ⟨fun r => .inl ⟨x.level, j, kinds r, c r⟩, ?_, ?_⟩
  · exact on_level x.level _ _ c (fun r s hrs => Or.inr (kinds.injective.ne hrs))
  · intro r
    constructor
    · exact Or.inl ⟨rfl, Fin.ne_succAbove x.copy r, Or.inl hjx.symm⟩
    · exact Or.inl ⟨hl.symm, by simp [c, ← hc, Fin.ne_succAbove],
        Or.inl hjy.symm⟩

lemma different_levels_triangle (P : Plane q) (hq : 4 ≤ q) (x y : CoreVertex q)
    (hl : x.level < y.level) (hn : ¬ coreAdj x y) :
    CommonTriangle P (.inl x) (.inl y) := by
  classical
  let places : Fin 3 ≃ predecessors y.place := (predecessors y.place).equivFinOfCardEq (predecessors_card hq _)|>.symm
  let c := x.copy.succAboveEmb
  let z : Fin 3 → CoreVertex q := fun r => ⟨x.level, places r, y.kind - 1, c r⟩
  refine ⟨fun r => .inl (z r), ?_, ?_⟩
  · apply on_level x.level _ _ c
    intro r s hrs
    exact Or.inl (fun he => hrs (places.injective (Subtype.ext he)))
  · intro r
    have hy : coreAdj (z r) y := (coreAdj_lt (x := z r) (y := y) hl).mpr
      ⟨by dsimp [z]; ring, mem_predecessors_iff.mp (places r).2⟩
    refine ⟨Or.inl ⟨rfl, Fin.ne_succAbove x.copy r, ?_⟩, coreAdj_symm hy⟩
    by_contra h
    push Not at h
    apply hn
    apply (coreAdj_lt hl).mpr
    exact ⟨by dsimp [z] at h; linear_combination -h.2,
      by rw [h.1]; exact mem_predecessors_iff.mp (places r).2⟩


private lemma embedding_avoiding {α : Type} [Fintype α] [DecidableEq α]
    (n : ℕ) (S : Finset α) (h : n + S.card ≤ Fintype.card α) :
    ∃ e : Fin n ↪ α, ∀ i, e i ∉ S := by
  classical
  let R := univ \ S
  have hr : Fintype.card (Fin n) ≤ Fintype.card R := by
    simp only [Fintype.card_fin, Fintype.card_coe, R, card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hr
  refine ⟨⟨fun i => (e i).1, fun i j he => e.injective (Subtype.ext he)⟩, ?_⟩
  intro i
  exact (mem_sdiff.mp (e i).2).2

lemma same_point_type_triangle (P : Plane q) (x y : CoreVertex q)
    (hl : x.level = y.level) (hp : x.place = y.place) (ht : x.kind = y.kind)
    (hc : x.copy ≠ y.copy) : CommonTriangle P (.inl x) (.inl y) := by
  classical
  obtain ⟨ts, hts⟩ := embedding_avoiding 2 ({x.kind} : Finset (ZMod 3)) (by simp)
  obtain ⟨cs, hcs⟩ := embedding_avoiding 2 ({x.copy, y.copy} : Finset (Fin 4)) (by simp [hc])
  let z : Fin 2 → CoreVertex q := fun r => ⟨x.level, x.place, ts r, cs r⟩
  obtain ⟨l, hlp⟩ := P.through x.level x.place
  have hcx (r : Fin 2) : x.copy ≠ cs r := by
    have hh := hcs r
    simp only [mem_insert, mem_singleton, not_or] at hh
    exact Ne.symm hh.1
  have hcy (r : Fin 2) : y.copy ≠ cs r := by
    have hh := hcs r
    simp only [mem_insert, mem_singleton, not_or] at hh
    exact Ne.symm hh.2
  have htx (r : Fin 2) : x.kind ≠ ts r := by simpa [eq_comm] using hts r
  have hx (r : Fin 2) : coreAdj x (z r) := Or.inl ⟨rfl, hcx r, Or.inr (htx r)⟩
  have hy (r : Fin 2) : coreAdj y (z r) :=
    Or.inl ⟨hl.symm, hcy r, Or.inr (by simpa [← ht] using htx r)⟩
  have hzz : coreAdj (z 0) (z 1) :=
    Or.inl ⟨rfl, cs.injective.ne (by decide), Or.inr (ts.injective.ne (by decide))⟩
  apply from_three (a := .inr l) (b := .inl (z 0)) (c := .inl (z 1))
  · exact hlp
  · exact hlp
  · exact hzz
  · exact ⟨hlp, hx 0, hx 1⟩
  · exact ⟨by change P.point l y.level = y.place; rw [← hl, ← hp]; exact hlp, hy 0, hy 1⟩

/-- Each missing edge has a triangle in its common neighborhood. -/
theorem planeGraph_commonTriangle (P : Plane q) (hq : 4 ≤ q)
    (x y : PlaneVertex P) (hn : ¬ (planeGraph P).Adj x y) : CommonTriangle P x y := by
  classical
  rcases x with x | l <;> rcases y with y | m
  · by_cases hl : x.level = y.level
    · by_cases hc : x.copy = y.copy
      · exact same_copy_triangle P hq x y hl hc
      · have hh : ¬ (x.place ≠ y.place ∨ x.kind ≠ y.kind) := fun h => hn (Or.inl ⟨hl, hc, h⟩)
        simp only [not_or, not_not] at hh
        exact same_point_type_triangle P x y hl hh.1 hh.2 hc
    · rcases lt_or_gt_of_ne hl with hl | hl
      · exact different_levels_triangle P hq x y hl hn
      · exact (different_levels_triangle P hq y x hl (fun h => hn (coreAdj_symm h))).symm
  · exact line_core_triangle P x m hn
  · exact (line_core_triangle P y l hn).symm
  · exact line_line_triangle P l m

end Erdos917.AEHK
