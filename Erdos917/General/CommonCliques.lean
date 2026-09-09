import Erdos917.General.Core

/-! Explicit common-neighborhood cliques for every kind of missing edge. -/

namespace Erdos917.General
open Finset SimpleGraph Erdos917.Geometry

variable {q r : ℕ} [NeZero q]

noncomputable def kinds : Fin (r+2) ≃ ZMod (r+2) := Fintype.equivOfCardEq (by simp)

def CommonClique (r : ℕ) (P : Plane q) (x y : PlaneVertex r P) : Prop :=
  ∃ t : Fin (r+2) → PlaneVertex r P,
    (∀ i j, i ≠ j → (planeGraph r P).Adj (t i) (t j)) ∧
    ∀ i, (planeGraph r P).Adj x (t i) ∧ (planeGraph r P).Adj y (t i)

lemma CommonClique.symm {P : Plane q} {x y : PlaneVertex r P} (h : CommonClique r P x y) :
    CommonClique r P y x := by
  obtain ⟨t, ht, hxy⟩ := h
  exact ⟨t, ht, fun i => (hxy i).symm⟩

omit [NeZero q] in
private lemma on_level (i : Fin (q + 1)) (p : Fin (r+2) → ZMod q) (t : Fin (r+2) → ZMod (r+2))
    (c : Fin (r+2) ↪ Fin (r+3)) (h : ∀ r s, r ≠ s → p r ≠ p s ∨ t r ≠ t s) :
    ∀ u v, u ≠ v → coreAdj (⟨i, p u, t u, c u⟩ : CoreVertex q r) ⟨i, p v, t v, c v⟩ := by
  intro u v huv
  exact Or.inl ⟨rfl, c.injective.ne huv, h u v huv⟩

lemma line_line_clique (P : Plane q) (l m : P.Line) :
    CommonClique r P (.inr l) (.inr m) := by
  obtain ⟨i, hi⟩ := P.meet l m
  let c := (0 : Fin (r+3)).succAboveEmb
  refine ⟨fun r => .inl ⟨i, P.point l i, kinds r, c r⟩, ?_, ?_⟩
  · exact on_level i _ _ c (fun r s hrs => Or.inr (kinds.injective.ne hrs))
  · intro r
    exact ⟨rfl, hi.symm⟩

lemma line_core_clique (P : Plane q) (x : CoreVertex q r) (l : P.Line)
    (hn : ¬ (planeGraph r P).Adj (.inl x) (.inr l)) :
    CommonClique r P (.inl x) (.inr l) := by
  let c := x.copy.succAboveEmb
  refine ⟨fun r => .inl ⟨x.level, P.point l x.level, kinds r, c r⟩, ?_, ?_⟩
  · exact on_level x.level _ _ c (fun r s hrs => Or.inr (kinds.injective.ne hrs))
  · intro r
    exact ⟨Or.inl ⟨rfl, Fin.ne_succAbove x.copy r, Or.inl (Ne.symm hn)⟩, rfl⟩

lemma same_copy_clique (P : Plane q) (hq : r+3 ≤ q) (x y : CoreVertex q r)
    (hl : x.level = y.level) (hc : x.copy = y.copy) :
    CommonClique r P (.inl x) (.inl y) := by
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

lemma different_levels_clique (P : Plane q) (hq : r+3 ≤ q) (x y : CoreVertex q r)
    (hl : x.level < y.level) (hn : ¬ coreAdj x y) :
    CommonClique r P (.inl x) (.inl y) := by
  classical
  let places : Fin (r+2) ≃ predecessors (r+2) y.place := (predecessors (r+2) y.place).equivFinOfCardEq (predecessors_card (by omega : r+2 < q) _)|>.symm
  let c := x.copy.succAboveEmb
  let z : Fin (r+2) → CoreVertex q r := fun r => ⟨x.level, places r, y.kind - 1, c r⟩
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

lemma same_point_type_clique (P : Plane q) (x y : CoreVertex q r)
    (hl : x.level = y.level) (hp : x.place = y.place) (ht : x.kind = y.kind)
    (hc : x.copy ≠ y.copy) : CommonClique r P (.inl x) (.inl y) := by
  classical
  obtain ⟨ts, hts⟩ := embedding_avoiding (r+1) ({x.kind} : Finset (ZMod (r+2))) (by simp)
  obtain ⟨cs, hcs⟩ := embedding_avoiding (r+1) ({x.copy, y.copy} : Finset (Fin (r+3))) (by simp [hc])
  let z : Fin (r+1) → CoreVertex q r := fun r => ⟨x.level, x.place, ts r, cs r⟩
  obtain ⟨l, hlp⟩ := P.through x.level x.place
  have hcx (r : Fin (r+1)) : x.copy ≠ cs r := by
    have hh := hcs r
    simp only [mem_insert, mem_singleton, not_or] at hh
    exact Ne.symm hh.1
  have hcy (r : Fin (r+1)) : y.copy ≠ cs r := by
    have hh := hcs r
    simp only [mem_insert, mem_singleton, not_or] at hh
    exact Ne.symm hh.2
  have htx (r : Fin (r+1)) : x.kind ≠ ts r := by simpa [eq_comm] using hts r
  have hx (r : Fin (r+1)) : coreAdj x (z r) := Or.inl ⟨rfl, hcx r, Or.inr (htx r)⟩
  have hy (r : Fin (r+1)) : coreAdj y (z r) :=
    Or.inl ⟨hl.symm, hcy r, Or.inr (by simpa [← ht] using htx r)⟩
  let f : Fin (r+2) → PlaneVertex r P := Fin.cases (.inr l) (fun j => .inl (z j))
  refine ⟨f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact False.elim (hij rfl)
      · intro _; exact hlp
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; exact hlp
      · intro hij
        exact Or.inl ⟨rfl, cs.injective.ne (fun h => hij (congrArg Fin.succ h)),
          Or.inr (ts.injective.ne (fun h => hij (congrArg Fin.succ h)))⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨hlp, by change P.point l y.level = y.place; rw [← hl, ← hp]; exact hlp⟩
    · exact ⟨hx i, hy i⟩

/-- Each missing edge has the required common-neighborhood clique. -/
theorem planeGraph_commonClique (P : Plane q) (hq : r+3 ≤ q)
    (x y : PlaneVertex r P) (hn : ¬ (planeGraph r P).Adj x y) : CommonClique r P x y := by
  classical
  rcases x with x | l <;> rcases y with y | m
  · by_cases hl : x.level = y.level
    · by_cases hc : x.copy = y.copy
      · exact same_copy_clique P hq x y hl hc
      · have hh : ¬ (x.place ≠ y.place ∨ x.kind ≠ y.kind) := fun h => hn (Or.inl ⟨hl, hc, h⟩)
        simp only [not_or, not_not] at hh
        exact same_point_type_clique P x y hl hh.1 hh.2 hc
    · rcases lt_or_gt_of_ne hl with hl | hl
      · exact different_levels_clique P hq x y hl hn
      · exact (different_levels_clique P hq y x hl (fun h => hn (coreAdj_symm h))).symm
  · exact line_core_clique P x m hn
  · exact (line_core_clique P y l hn).symm
  · exact line_line_clique P l m

end Erdos917.General
