import Mathlib

/-! Consecutive cyclic intervals and the two-level clique bound. -/

namespace Erdos917.General
open Finset
variable {q m : ℕ}

def successors (m : ℕ) (a : ZMod q) : Finset (ZMod q) :=
  (Icc 1 m).image (fun j : ℕ => a + j)

def predecessors (m : ℕ) (b : ZMod q) : Finset (ZMod q) :=
  (Icc 1 m).image (fun j : ℕ => b - j)

lemma cast_injective_on_interval (hm : m < q) :
    Set.InjOn (fun j : ℕ => (j : ZMod q)) (Icc 1 m : Finset ℕ) := by
  intro i hi j hj he
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Icc.mp hi).2 hm),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Icc.mp hj).2 hm)] at hv
  exact hv

lemma successors_card (hm : m < q) (a : ZMod q) : (successors m a).card = m := by
  rw [successors, card_image_of_injOn]
  · simp
  · intro i hi j hj he
    exact cast_injective_on_interval hm hi hj (add_left_cancel he)

lemma predecessors_card (hm : m < q) (b : ZMod q) : (predecessors m b).card = m := by
  rw [predecessors, card_image_of_injOn]
  · simp
  · intro i hi j hj he
    exact cast_injective_on_interval hm hi hj (sub_right_injective he)

lemma mem_predecessors_iff {a b : ZMod q} :
    a ∈ predecessors m b ↔ b ∈ successors m a := by
  simp only [predecessors, successors, mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j,hj,sub_add_cancel _ _⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨j,hj,add_sub_cancel_right _ _⟩

/-- Lift the places relative to one successor. The assumption `2 m ≤ q`
keeps every sum of a predecessor displacement and a successor displacement below `q`. -/
lemma rectangle_bound (_hm : 0 < m) (hq : 2*m ≤ q)
    {A B : Finset (ZMod q)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, b ∈ successors m a) :
    A.card + B.card ≤ m+1 := by
  classical
  obtain ⟨b₀,hb₀⟩ := hB
  let S := (Icc 1 m).filter (fun s : ℕ => b₀ - s ∈ A)
  have hS : S.Nonempty := by
    obtain ⟨a,ha⟩ := hA
    obtain ⟨s,hs,he⟩ := mem_image.mp (mem_predecessors_iff.mpr (hAB a ha b₀ hb₀))
    exact ⟨s,mem_filter.mpr ⟨hs,he ▸ ha⟩⟩
  let s₀ := S.min' hS
  have hs₀ : s₀ ∈ S := min'_mem S hS
  have hs₀I := mem_Icc.mp (mem_filter.mp hs₀).1
  have ha₀ : b₀ - s₀ ∈ A := (mem_filter.mp hs₀).2
  let J := (Icc 1 m).filter (fun j : ℕ => b₀ - s₀ + j ∈ B)
  have hJ : J.Nonempty := by
    refine ⟨s₀, mem_filter.mpr ⟨(mem_filter.mp hs₀).1, ?_⟩⟩
    simpa using hb₀
  let s₁ := S.max' hS
  let j₁ := J.max' hJ
  have hs₁ : s₁ ∈ S := max'_mem S hS
  have hj₁ : j₁ ∈ J := max'_mem J hJ
  have hs₁I := mem_Icc.mp (mem_filter.mp hs₁).1
  have hj₁I := mem_Icc.mp (mem_filter.mp hj₁).1
  have hmin : s₀ ≤ s₁ := min'_le _ _ hs₁
  have hmax : j₁ + (s₁-s₀) ≤ m := by
    obtain ⟨u,hu,he⟩ := mem_image.mp
      (hAB _ (mem_filter.mp hs₁).2 _ (mem_filter.mp hj₁).2)
    have hc : ((j₁ + (s₁-s₀) : ℕ) : ZMod q) = u := by
      rw [Nat.cast_add, Nat.cast_sub hmin]
      linear_combination -he
    have hv := congrArg ZMod.val hc
    have hleft : j₁+(s₁-s₀) < q := by omega
    have hright : u < q := by have := mem_Icc.mp hu; omega
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hv
    exact hv ▸ (mem_Icc.mp hu).2
  have hAc : A.card ≤ s₁-s₀+1 := by
    have hsub : A ⊆ (Icc s₀ s₁).image (fun s : ℕ => b₀-s) := by
      intro a ha
      obtain ⟨s,hs,he⟩ := mem_image.mp (mem_predecessors_iff.mpr (hAB a ha b₀ hb₀))
      have hsS : s ∈ S := mem_filter.mpr ⟨hs,he ▸ ha⟩
      exact mem_image.mpr ⟨s,mem_Icc.mpr ⟨min'_le _ _ hsS, le_max' _ _ hsS⟩,he⟩
    have hc := (card_le_card hsub).trans (card_image_le)
    simp only [Nat.card_Icc] at hc
    omega
  have hBc : B.card ≤ j₁ := by
    have hsub : B ⊆ (Icc 1 j₁).image (fun j : ℕ => b₀-s₀+j) := by
      intro b hb
      obtain ⟨j,hj,he⟩ := mem_image.mp (hAB _ ha₀ b hb)
      have hjJ : j ∈ J := mem_filter.mpr ⟨hj,he ▸ hb⟩
      exact mem_image.mpr ⟨j,mem_Icc.mpr ⟨(mem_Icc.mp hj).1, le_max' _ _ hjJ⟩,he⟩
    have hc := (card_le_card hsub).trans (card_image_le)
    simpa using hc
  omega

end Erdos917.General
