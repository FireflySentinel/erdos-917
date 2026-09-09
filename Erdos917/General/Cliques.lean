import Erdos917.General.Core

/-! Clique bounds for the core and for a line neighborhood. -/

namespace Erdos917.General
open Finset SimpleGraph Erdos917.AEHK

variable {q r : ℕ}

lemma third_level {x y z : CoreVertex q r}
    (hxy : coreAdj x y) (hxz : coreAdj x z) (hyz : coreAdj y z)
    (hij : x.level < y.level) : z.level = x.level ∨ z.level = y.level := by
  by_cases hx : z.level = x.level
  · exact Or.inl hx
  by_cases hy : z.level = y.level
  · exact Or.inr hy
  exfalso
  rcases lt_or_gt_of_ne hx with h | h
  · exact no_three_levels (coreAdj_symm hxz) hxy (coreAdj_symm hyz) h hij
  · rcases lt_or_gt_of_ne hy with h' | h'
    · exact no_three_levels hxz (coreAdj_symm hyz) hxy h h'
    · exact no_three_levels hxy hyz hxz hij h'

lemma clique_levels {C : Finset (CoreVertex q r)} (hc : (C : Set (CoreVertex q r)).Pairwise coreAdj)
    {x y : CoreVertex q r} (hx : x ∈ C) (hy : y ∈ C) (hij : x.level < y.level) :
    ∀ z ∈ C, z.level = x.level ∨ z.level = y.level := by
  intro z hz
  by_cases hzx : z = x
  · exact Or.inl (congrArg CoreVertex.level hzx)
  by_cases hzy : z = y
  · exact Or.inr (congrArg CoreVertex.level hzy)
  exact third_level (hc hx hy (by intro h; exact (ne_of_lt hij) (congrArg CoreVertex.level h)))
    (hc hx hz (Ne.symm hzx)) (hc hy hz (Ne.symm hzy)) hij

lemma place_injective_of_opposite {C : Finset (CoreVertex q r)} (hc : (C : Set (CoreVertex q r)).Pairwise coreAdj)
    {i : Fin (q + 1)} {z : CoreVertex q r} (hz : z ∈ C) (hiz : i ≠ z.level) :
    Set.InjOn CoreVertex.place (↑(C.filter (fun x => x.level = i)) : Set (CoreVertex q r)) := by
  intro x hx y hy hplace
  obtain ⟨hx, hxi⟩ := mem_filter.mp hx
  obtain ⟨hy, hyi⟩ := mem_filter.mp hy
  have hxz : x ≠ z := by intro h; apply hiz; rw [← h, hxi]
  have hyz : y ≠ z := by intro h; apply hiz; rw [← h, hyi]
  have hkind : x.kind = y.kind := by
    rcases lt_or_gt_of_ne hiz with hi | hi
    · have h1 := ((coreAdj_lt (hxi ▸ hi)).mp (hc hx hz hxz)).1
      have h2 := ((coreAdj_lt (hyi ▸ hi)).mp (hc hy hz hyz)).1
      exact add_right_cancel (h1.symm.trans h2)
    · have h1 := ((coreAdj_lt (hxi ▸ hi)).mp (coreAdj_symm (hc hx hz hxz))).1
      have h2 := ((coreAdj_lt (hyi ▸ hi)).mp (coreAdj_symm (hc hy hz hyz))).1
      exact h1.trans h2.symm
  by_contra hxy
  have h := ((coreAdj_same (hxi.trans hyi.symm)).mp (hc hx hy hxy)).2
  exact h.elim (fun hp => hp hplace) (fun hk => hk hkind)

lemma coreClique_card_le (hq : 2*(r+2) ≤ q) {C : Finset (CoreVertex q r)}
    (hc : (C : Set (CoreVertex q r)).Pairwise coreAdj) : C.card ≤ r+3 := by
  classical
  by_cases hall : ∀ x ∈ C, ∀ y ∈ C, x.level = y.level
  · have hinj : Set.InjOn CoreVertex.copy (C : Set (CoreVertex q r)) := by
      intro x hx y hy he
      by_contra hn
      exact ((coreAdj_same (hall x hx y hy)).mp (hc hx hy hn)).1 he
    calc
      C.card = (C.image CoreVertex.copy).card := (card_image_of_injOn hinj).symm
      _ ≤ (univ : Finset (Fin (r+3))).card := card_le_card (subset_univ _)
      _ = r+3 := by simp
  push Not at hall
  obtain ⟨x, hx, y, hy, hxy⟩ := hall
  suffices h : ∀ x ∈ C, ∀ y ∈ C, x.level < y.level → C.card ≤ r+3 by
    rcases lt_or_gt_of_ne hxy with hxy | hxy
    · exact h x hx y hy hxy
    · exact h y hy x hx hxy
  intro x hx y hy hxy
  let A := C.filter (fun z => z.level = x.level)
  let B := C.filter (fun z => z.level = y.level)
  have hlevels := clique_levels hc hx hy hxy
  have hpart : A.card + B.card = C.card := by
    have he : B = C.filter (fun z => ¬ z.level = x.level) := by
      ext z
      simp only [B, mem_filter]
      constructor
      · rintro ⟨hz, he⟩; exact ⟨hz, by rw [he]; exact (ne_of_lt hxy).symm⟩
      · rintro ⟨hz, hn⟩; exact ⟨hz, (hlevels z hz).resolve_left hn⟩
    rw [he]
    exact card_filter_add_card_filter_not _
  have hAi := place_injective_of_opposite hc hy (ne_of_lt hxy)
  have hBi := place_injective_of_opposite hc hx (ne_of_lt hxy).symm
  have hAb : (A.image CoreVertex.place).Nonempty := ⟨x.place, mem_image.mpr ⟨x, by simp [A, hx], rfl⟩⟩
  have hBb : (B.image CoreVertex.place).Nonempty := ⟨y.place, mem_image.mpr ⟨y, by simp [B, hy], rfl⟩⟩
  have hrect := rectangle_bound (by omega : 0 < r+2) hq hAb hBb (by
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
    obtain ⟨hu, hui⟩ := mem_filter.mp hu
    obtain ⟨hv, hvi⟩ := mem_filter.mp hv
    have huv : u.level < v.level := by rw [hui, hvi]; exact hxy
    exact ((coreAdj_lt huv).mp (hc hu hv (by intro h; exact (ne_of_lt huv) (congrArg CoreVertex.level h)))).2)
  rw [card_image_of_injOn hAi, card_image_of_injOn hBi, hpart] at hrect
  exact hrect


variable [NeZero q]

lemma lineClique_card_le (P : Plane q) (l : P.Line) {C : Finset (CoreVertex q r)}
    (hc : (C : Set (CoreVertex q r)).Pairwise coreAdj)
    (hp : ∀ x ∈ C, P.point l x.level = x.place) : C.card ≤ r+2 := by
  classical
  by_cases hall : ∀ x ∈ C, ∀ y ∈ C, x.level = y.level
  · have hinj : Set.InjOn CoreVertex.kind (C : Set (CoreVertex q r)) := by
      intro x hx y hy he
      by_contra hn
      have hxy := hall x hx y hy
      have hplace : x.place = y.place := by rw [← hp x hx, ← hp y hy, hxy]
      exact ((coreAdj_same hxy).mp (hc hx hy hn)).2.elim
        (fun h => h hplace) (fun h => h he)
    calc
      C.card = (C.image CoreVertex.kind).card := (card_image_of_injOn hinj).symm
      _ ≤ (univ : Finset (ZMod (r+2))).card := card_le_card (subset_univ _)
      _ = r+2 := by simp
  push Not at hall
  obtain ⟨x, hx, y, hy, hxy⟩ := hall
  suffices h : ∀ x ∈ C, ∀ y ∈ C, x.level < y.level → C.card ≤ r+2 by
    rcases lt_or_gt_of_ne hxy with hxy | hxy
    · exact h x hx y hy hxy
    · exact h y hy x hx hxy
  intro x hx y hy hxy
  have hlevels := clique_levels hc hx hy hxy
  have hcard (i : Fin (q + 1)) (z : CoreVertex q r) (hz : z ∈ C) (hiz : i ≠ z.level) :
      (C.filter (fun w => w.level = i)).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    apply place_injective_of_opposite hc hz hiz hu hv
    rw [← hp u (mem_filter.mp hu).1, ← hp v (mem_filter.mp hv).1,
      (mem_filter.mp hu).2, (mem_filter.mp hv).2]
  have hA := hcard x.level y hy (ne_of_lt hxy)
  have hB := hcard y.level x hx (ne_of_lt hxy).symm
  have he : C.filter (fun z => z.level = y.level) = C.filter (fun z => ¬ z.level = x.level) := by
    ext z
    simp only [mem_filter]
    constructor
    · rintro ⟨hz, he⟩; exact ⟨hz, by rw [he]; exact (ne_of_lt hxy).symm⟩
    · rintro ⟨hz, hn⟩; exact ⟨hz, (hlevels z hz).resolve_left hn⟩
  rw [he] at hB
  have heq := card_filter_add_card_filter_not (s := C) (fun z => z.level = x.level)
  omega

/-- The complete AEHK graph contains no clique of order r+4. -/
theorem planeGraph_cliqueFree (r : ℕ) (P : Plane q) (hq : 2*(r+2) ≤ q) : (planeGraph r P).CliqueFree (r+4) := by
  classical
  intro C hC
  have hc := hC.isClique
  have hcore : (C.toLeft : Set (CoreVertex q r)).Pairwise coreAdj := by
    intro x hx y hy hxy
    exact hc (mem_toLeft.mp hx) (mem_toLeft.mp hy) (Sum.inl_injective.ne hxy)
  have hline : C.toRight.card ≤ 1 := by
    apply card_le_one.mpr
    intro l hl m hm
    by_contra h
    exact hc (mem_toRight.mp hl) (mem_toRight.mp hm) (Sum.inr_injective.ne h)
  have hsum := card_toLeft_add_card_toRight (u := C)
  by_cases he : C.toRight.Nonempty
  · obtain ⟨l, hl⟩ := he
    have hbound := lineClique_card_le P l hcore (by
      intro x hx
      exact hc (mem_toLeft.mp hx) (mem_toRight.mp hl) (by simp))
    have hsize := hC.card_eq
    omega
  · have hzero : C.toRight.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp he)
    have hbound := coreClique_card_le hq hcore
    have hsize := hC.card_eq
    omega

end Erdos917.General
