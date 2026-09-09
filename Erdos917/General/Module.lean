import Erdos917.ModuleGraph

/-! The module coloring lemma for every finite palette with at least three colors. -/

namespace Erdos917.General
open Finset SimpleGraph

abbrev Palette (n : ℕ) := Option (Fin (n+3) × Bool)
@[simp] lemma card_palette (n : ℕ) : Fintype.card (Palette n) = 2*n+7 := by
  simp [Palette]
  omega

namespace Module
open ModuleVertex Erdos917.Module
variable {m : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
  {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y)
  (hcard : Fintype.card C = m+3)
include hcard

/-- Lemma 3(1): the active set cannot be contained in two colors. -/
theorem active_not_two (hS : ¬ S.Colorable (m+2)) (hT : ¬ T.Colorable (m+1))
    (f : (moduleGraph S T).Coloring C) (α β : C) (hαβ : α ≠ β) :
    ∃ p : X × Y, f (a p) ≠ α ∧ f (a p) ≠ β := by
  classical
  by_contra! h
  have hall : ∀ p : X × Y, f (a p) = α ∨ f (a p) = β := by
    intro p
    by_cases hp : f (a p) = α
    · exact Or.inl hp
    · exact Or.inr (h p hp)
  obtain ⟨xα,hxα⟩ := color_surjective S (by simp [hcard] : Fintype.card C = (m+2)+1) hS (restrictS S T f) α
  obtain ⟨xβ,hxβ⟩ := color_surjective S (by simp [hcard] : Fintype.card C = (m+2)+1) hS (restrictS S T f) β
  have htβ (y : Y) : f (t y) ≠ β := by
    have hadj : (moduleGraph S T).Adj (s xα) (a (xα,y)) := rfl
    have hcol : f (a (xα,y)) = β := (hall (xα,y)).resolve_left (by
      intro heq
      exact f.valid hadj (hxα.trans heq.symm))
    have hproper := f.valid (show (moduleGraph S T).Adj (t y) (a (xα,y)) from rfl)
    simpa only [hcol] using hproper
  have htα (y : Y) : f (t y) ≠ α := by
    have hadj : (moduleGraph S T).Adj (s xβ) (a (xβ,y)) := rfl
    have hcol : f (a (xβ,y)) = α := (hall (xβ,y)).resolve_right (by
      intro heq
      exact f.valid hadj (hxβ.trans heq.symm))
    have hproper := f.valid (show (moduleGraph S T).Adj (t y) (a (xβ,y)) from rfl)
    simpa only [hcol] using hproper
  have hc := colorable_of_palette T (restrictT S T f) (univ \ {α,β})
    (fun y => by change f (t y) ∈ univ \ {α,β}; simp [htα y,htβ y])
  apply hT
  have he : (univ \ {α,β} : Finset C).card = m+1 := by
    simp [card_sdiff_of_subset (subset_univ _), hαβ, hcard]
  rwa [he] at hc

section Assignments

variable [DecidableEq X] [DecidableEq Y]

/-- Lemma 3(2), with the colors of the two structural neighbors also recorded. -/
theorem singleton_active_coloring (hS : CriticalData S (m+2)) (hT : CriticalData T (m+1))
    (p₀ : X × Y) (α β γ : C) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∃ f : (moduleGraph S T).Coloring C,
      (∀ p,f (a p) = α ∨ f (a p) = β ∨ f (a p) = γ) ∧
      (∀ p,f (a p) = γ ↔ p = p₀) ∧ f (s p₀.1) = α ∧ f (t p₀.2) = β := by
  classical
  obtain ⟨cs,hs₀,hs⟩ := singleton_coloring S p₀.1 (hS.delete_vertex p₀.1) α (by simp [hcard])
  obtain ⟨ct,ht₀,ht,htα⟩ := singleton_coloring_avoiding T p₀.2 (hT.delete_vertex p₀.2)
    {α} β (by simpa using hαβ.symm) (by simp [hcard])
  have hgood := activeRule_good S T p₀ α β γ hαβ hαγ hβγ cs ct hs₀ hs ht₀ ht
    (fun y => by simpa using htα y)
  let f := coloringOfParts S T cs ct (activeRule p₀ α β γ) hgood.1 hgood.2
  refine ⟨f,?_,?_,hs₀,ht₀⟩
  · intro p
    change activeRule p₀ α β γ p = α ∨ activeRule p₀ α β γ p = β ∨ activeRule p₀ α β γ p = γ
    unfold activeRule
    split_ifs <;> simp
  · intro p
    change activeRule p₀ α β γ p = γ ↔ p = p₀
    by_cases hx : p.1 = p₀.1 <;> by_cases hy : p.2 = p₀.2 <;>
      simp [activeRule,hx,hy,hαγ,hβγ,Prod.ext_iff]

end Assignments

section Deletion

variable [DecidableEq X] [DecidableEq Y] [Nonempty X]

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] in
lemma delete_S_coloring (hS : CriticalData S (m+2)) (hT : CriticalData T (m+1))
    (x y : X) (hxy : S.Adj x y) (α β : C) :
    ∃ f : ModuleVertex X Y → C,
      ProperExcept (moduleGraph S T) f (s x) (s y) ∧ ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  obtain ⟨cs,hcs⟩ := coloring_avoiding (S.deleteEdges {s(x,y)}) (hS.delete_edge x y hxy) {α} (by simp [hcard])
  obtain ⟨ct,hct⟩ := coloring_avoiding T hT.colorable {α} (by simp [hcard])
  refine ⟨Sum.elim cs (Sum.elim ct (fun _ => α)),?_,fun p => Or.inl rfl⟩
  apply exceptOfParts
  · intro z w h he
    rcases except_of_coloring_delete S x y cs z w h he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
  · intro z w h he
    exact False.elim (ct.valid h he)
  · intro p he
    exact False.elim (hcs p.1 (by simpa using he.symm))
  · intro p he
    exact False.elim (hct p.2 (by simpa using he.symm))

omit [DecidableEq Y] in
lemma delete_T_coloring (hS : CriticalData S (m+2)) (hT : CriticalData T (m+1))
    (y z : Y) (hyz : T.Adj y z) (α β : C) (hαβ : α ≠ β) :
    ∃ f : ModuleVertex X Y → C,
      ProperExcept (moduleGraph S T) f (t y) (t z) ∧ ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨cs,hcs₀,hcs⟩ := singleton_coloring S x₀ (hS.delete_vertex x₀) α (by simp [hcard])
  obtain ⟨ct,hct⟩ := coloring_avoiding (T.deleteEdges {s(y,z)}) (hT.delete_edge y z hyz) {α,β}
    (by simp [hαβ, hcard])
  let ca : X × Y → C := fun p => if p.1 = x₀ then β else α
  refine ⟨Sum.elim cs (Sum.elim ct ca),?_,?_⟩
  · apply exceptOfParts
    · intro u v h he
      exact False.elim (cs.valid h he)
    · intro u v h he
      rcases except_of_coloring_delete T y z ct u v h he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
    · intro p he
      by_cases hp : p.1 = x₀
      · have hh : β = α := by simpa [ca,hp,hcs₀] using he
        exact False.elim (hαβ hh.symm)
      · have hh : cs p.1 = α := by simpa [ca,hp] using he.symm
        exact False.elim (hp (hcs p.1 hh))
    · intro p he
      apply False.elim (hct p.2 _)
      by_cases hp : p.1 = x₀ <;> simp_all [ca]
  · intro p
    change ca p = α ∨ ca p = β
    unfold ca
    split_ifs <;> simp

omit [Nonempty X] in
lemma delete_spoke_coloring (hS : CriticalData S (m+2)) (hT : CriticalData T (m+1))
    (p₀ : X × Y) (α β : C) (hαβ : α ≠ β) (side : Bool) :
    ∃ f : ModuleVertex X Y → C,
      ProperExcept (moduleGraph S T) f (a p₀) (if side then t p₀.2 else s p₀.1) ∧
      ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  have hex : ∃ γ : C, γ ∉ ({α,β} : Finset C) := by
    by_contra! h
    have he : ({α,β} : Finset C) = univ := eq_univ_of_forall h
    have hc := congrArg Finset.card he
    simp [hαβ,hcard] at hc
  obtain ⟨γ,hγ⟩ := hex
  have hαγ : α ≠ γ := fun h => hγ (by simp [h])
  have hβγ : β ≠ γ := fun h => hγ (by simp [h])
  obtain ⟨c,hca,hcγ,hcs,hct⟩ := singleton_active_coloring S T hcard hS hT p₀ α β γ hαβ hαγ hβγ
  let δ := if side then β else α
  let f := Function.update c (a p₀) δ
  refine ⟨f,?_,?_⟩
  · apply update_proper_except (moduleGraph S T) c (a p₀) (if side then t p₀.2 else s p₀.1) δ
    rintro (x|y|p) hadj hcol
    · change p₀.1 = x at hadj
      subst x
      cases side
      · rfl
      · exact False.elim (hαβ (hcs.symm.trans hcol))
    · change p₀.2 = y at hadj
      subst y
      cases side
      · exact False.elim (hαβ (hct.symm.trans hcol).symm)
      · rfl
    · contradiction
  · intro p
    by_cases hp : p = p₀
    · subst p
      cases side <;> simp [f,δ]
    · have hne : a p ≠ a p₀ := by simpa [a] using hp
      rw [show f (a p) = c (a p) from Function.update_of_ne hne _ _]
      rcases hca p with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hp ((hcγ p).mp h))

/-- Lemma 3(3): every module edge has an explicit palette deletion certificate. -/
theorem delete_edge_coloring (hS : CriticalData S (m+2)) (hT : CriticalData T (m+1))
    (u v : ModuleVertex X Y) (huv : (moduleGraph S T).Adj u v)
    (α β : C) (hαβ : α ≠ β) :
    ∃ f : ModuleVertex X Y → C, ProperExcept (moduleGraph S T) f u v ∧
      ∀ p,f (a p) = α ∨ f (a p) = β := by
  rcases edge_cases S T u v huv with ⟨x,y,h,rfl,rfl⟩|⟨x,y,h,rfl,rfl⟩|⟨p,h⟩|⟨p,h⟩
  · exact delete_S_coloring S T hcard hS hT x y h α β
  · exact delete_T_coloring S T hcard hS hT x y h α β hαβ
  · obtain ⟨f,hf,hfa⟩ := delete_spoke_coloring S T hcard hS hT p α β hαβ false
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨f,hf,hfa⟩
    · exact ⟨f,fun a b h he => (hf a b h he).symm,hfa⟩
  · obtain ⟨f,hf,hfa⟩ := delete_spoke_coloring S T hcard hS hT p α β hαβ true
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨f,hf,hfa⟩
    · exact ⟨f,fun a b h he => (hf a b h he).symm,hfa⟩

end Deletion

end Module
end Erdos917.General
