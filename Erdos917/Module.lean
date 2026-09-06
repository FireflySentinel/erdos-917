import Erdos917.Basic

namespace Erdos917

open Finset SimpleGraph

abbrev ModuleVertex (X Y : Type*) := X ⊕ (Y ⊕ (X × Y))

namespace ModuleVertex
variable {X Y : Type*}
def s (x : X) : ModuleVertex X Y := Sum.inl x
def t (y : Y) : ModuleVertex X Y := Sum.inr (Sum.inl y)
def a (p : X × Y) : ModuleVertex X Y := Sum.inr (Sum.inr p)
end ModuleVertex

def moduleAdj {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y) :
    ModuleVertex X Y → ModuleVertex X Y → Prop
  | Sum.inl x, Sum.inl y => S.Adj x y
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => T.Adj x y
  | Sum.inl x, Sum.inr (Sum.inr p) => x = p.1
  | Sum.inr (Sum.inr p), Sum.inl x => p.1 = x
  | Sum.inr (Sum.inl y), Sum.inr (Sum.inr p) => y = p.2
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inl y) => p.2 = y
  | _,_ => False

def moduleGraph {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y) : SimpleGraph (ModuleVertex X Y) where
  Adj := moduleAdj S T
  symm := ⟨by
    rintro (x|x|x) (y|y|y) h <;> simp_all [moduleAdj,S.adj_comm,T.adj_comm,eq_comm]⟩
  loopless := ⟨by
    rintro (x|x|x) <;> simp [moduleAdj]⟩

namespace Module

open ModuleVertex

variable {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y)

def coloringOfParts {C : Type*} (cs : S.Coloring C) (ct : T.Coloring C) (ca : X × Y → C)
    (has : ∀ p, ca p ≠ cs p.1) (hat : ∀ p, ca p ≠ ct p.2) : (moduleGraph S T).Coloring C :=
  Coloring.mk (Sum.elim cs (Sum.elim ct ca)) (by
    rintro (x|x|x) (y|y|y) h
    · exact cs.valid h
    · exact False.elim h
    · change x = y.1 at h
      subst x
      exact (has y).symm
    · exact False.elim h
    · exact ct.valid h
    · change x = y.2 at h
      subst x
      exact (hat y).symm
    · change x.1 = y at h
      subst y
      exact has x
    · change x.2 = y at h
      subst y
      exact hat x
    · exact False.elim h)

def restrictS {C : Type*} (f : (moduleGraph S T).Coloring C) : S.Coloring C :=
  Coloring.mk (fun x => f (s x)) (fun {_x _y} h => f.valid h)

def restrictT {C : Type*} (f : (moduleGraph S T).Coloring C) : T.Coloring C :=
  Coloring.mk (fun y => f (t y)) (fun {_x _y} h => f.valid h)

/-- Lemma 2(1): the active set cannot be contained in two colors. -/
theorem active_not_two (hS : ¬ S.Colorable 10) (hT : ¬ T.Colorable 9)
    (f : (moduleGraph S T).Coloring Palette) (α β : Palette) (hαβ : α ≠ β) :
    ∃ p : X × Y, f (a p) ≠ α ∧ f (a p) ≠ β := by
  classical
  by_contra! h
  have hall : ∀ p : X × Y, f (a p) = α ∨ f (a p) = β := by
    intro p
    by_cases hp : f (a p) = α
    · exact Or.inl hp
    · exact Or.inr (h p hp)
  obtain ⟨xα,hxα⟩ := color_surjective S (by decide : Fintype.card Palette = 10+1) hS (restrictS S T f) α
  obtain ⟨xβ,hxβ⟩ := color_surjective S (by decide : Fintype.card Palette = 10+1) hS (restrictS S T f) β
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
  simpa [card_sdiff_of_subset (subset_univ _),hαβ] using hc

section Assignments

variable [DecidableEq X] [DecidableEq Y]

def activeRule {C : Type*} (p₀ : X × Y) (α β γ : C) (p : X × Y) : C :=
  if p.1 = p₀.1 then if p.2 = p₀.2 then γ else β else α

lemma activeRule_good {C : Type*} (p₀ : X × Y) (α β γ : C)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (cs : S.Coloring C) (ct : T.Coloring C)
    (hs₀ : cs p₀.1 = α) (hs : ∀ x,cs x = α → x = p₀.1)
    (ht₀ : ct p₀.2 = β) (ht : ∀ y,ct y = β → y = p₀.2)
    (htα : ∀ y,ct y ≠ α) :
    (∀ p,activeRule p₀ α β γ p ≠ cs p.1) ∧
      (∀ p,activeRule p₀ α β γ p ≠ ct p.2) := by
  constructor
  · intro ⟨x,y⟩
    by_cases hx : x = p₀.1
    · subst x
      by_cases hy : y = p₀.2
      · simpa [activeRule,hy,hs₀] using hαγ.symm
      · simpa [activeRule,hy,hs₀] using hαβ.symm
    · simp only [activeRule,if_neg hx]
      exact fun he => hx (hs x he.symm)
  · intro ⟨x,y⟩
    by_cases hx : x = p₀.1
    · by_cases hy : y = p₀.2
      · simpa [activeRule,hx,hy,ht₀] using hβγ.symm
      · simp only [activeRule,if_pos hx,if_neg hy]
        exact fun he => hy (ht y he.symm)
    · simpa [activeRule,hx] using (htα y).symm

/-- Lemma 2(2), with the colors of the two structural neighbors also recorded. -/
theorem singleton_active_coloring (hS : CriticalData S 10) (hT : CriticalData T 9)
    (p₀ : X × Y) (α β γ : Palette) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∃ f : (moduleGraph S T).Coloring Palette,
      (∀ p,f (a p) = α ∨ f (a p) = β ∨ f (a p) = γ) ∧
      (∀ p,f (a p) = γ ↔ p = p₀) ∧ f (s p₀.1) = α ∧ f (t p₀.2) = β := by
  classical
  obtain ⟨cs,hs₀,hs⟩ := singleton_coloring S p₀.1 (hS.delete_vertex p₀.1) α (by decide)
  obtain ⟨ct,ht₀,ht,htα⟩ := singleton_coloring_avoiding T p₀.2 (hT.delete_vertex p₀.2)
    {α} β (by simpa using hαβ.symm) (by simp [Palette])
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

omit [DecidableEq X] [DecidableEq Y] in
/-- The complete list of module edge types. -/
lemma edge_cases (u v : ModuleVertex X Y) (h : (moduleGraph S T).Adj u v) :
    (∃ x y,S.Adj x y ∧ u = s x ∧ v = s y) ∨
    (∃ x y,T.Adj x y ∧ u = t x ∧ v = t y) ∨
    (∃ p,(u = a p ∧ v = s p.1) ∨ (u = s p.1 ∧ v = a p)) ∨
    (∃ p,(u = a p ∧ v = t p.2) ∨ (u = t p.2 ∧ v = a p)) := by
  rcases u with u|u|u <;> rcases v with v|v|v
  · exact Or.inl ⟨u,v,h,rfl,rfl⟩
  · contradiction
  · change u = v.1 at h
    subst u; exact Or.inr (Or.inr (Or.inl ⟨v,Or.inr ⟨rfl,rfl⟩⟩))
  · contradiction
  · exact Or.inr (Or.inl ⟨u,v,h,rfl,rfl⟩)
  · change u = v.2 at h
    subst u; exact Or.inr (Or.inr (Or.inr ⟨v,Or.inr ⟨rfl,rfl⟩⟩))
  · change u.1 = v at h
    subst v; exact Or.inr (Or.inr (Or.inl ⟨u,Or.inl ⟨rfl,rfl⟩⟩))
  · change u.2 = v at h
    subst v; exact Or.inr (Or.inr (Or.inr ⟨u,Or.inl ⟨rfl,rfl⟩⟩))
  · contradiction

end Assignments

lemma exceptOfParts {C : Type*} (cs : X → C) (ct : Y → C) (ca : X × Y → C)
    (u v : ModuleVertex X Y)
    (hs : ∀ x y,S.Adj x y → cs x = cs y →
      (s x = u ∧ s y = v) ∨ (s x = v ∧ s y = u))
    (ht : ∀ x y,T.Adj x y → ct x = ct y →
      (t x = u ∧ t y = v) ∨ (t x = v ∧ t y = u))
    (has : ∀ p,ca p = cs p.1 →
      (a p = u ∧ s p.1 = v) ∨ (a p = v ∧ s p.1 = u))
    (hat : ∀ p,ca p = ct p.2 →
      (a p = u ∧ t p.2 = v) ∨ (a p = v ∧ t p.2 = u)) :
    ProperExcept (moduleGraph S T) (Sum.elim cs (Sum.elim ct ca)) u v := by
  rintro (x|x|x) (y|y|y) h he
  · exact hs x y h he
  · contradiction
  · change x = y.1 at h
    subst x
    rcases has y he.symm with h|h
    · exact Or.inr ⟨h.2,h.1⟩
    · exact Or.inl ⟨h.2,h.1⟩
  · contradiction
  · exact ht x y h he
  · change x = y.2 at h
    subst x
    rcases hat y he.symm with h|h
    · exact Or.inr ⟨h.2,h.1⟩
    · exact Or.inl ⟨h.2,h.1⟩
  · change x.1 = y at h
    subst y
    exact has x he
  · change x.2 = y at h
    subst y
    exact hat x he
  · contradiction

section Deletion

variable [DecidableEq X] [DecidableEq Y] [Nonempty X]

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] in
lemma delete_S_coloring (hS : CriticalData S 10) (hT : CriticalData T 9)
    (x y : X) (hxy : S.Adj x y) (α β : Palette) :
    ∃ f : ModuleVertex X Y → Palette,
      ProperExcept (moduleGraph S T) f (s x) (s y) ∧ ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  obtain ⟨cs,hcs⟩ := coloring_avoiding (S.deleteEdges {s(x,y)}) (hS.delete_edge x y hxy) {α} (by simp [Palette])
  obtain ⟨ct,hct⟩ := coloring_avoiding T hT.colorable {α} (by simp [Palette])
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
lemma delete_T_coloring (hS : CriticalData S 10) (hT : CriticalData T 9)
    (y z : Y) (hyz : T.Adj y z) (α β : Palette) (hαβ : α ≠ β) :
    ∃ f : ModuleVertex X Y → Palette,
      ProperExcept (moduleGraph S T) f (t y) (t z) ∧ ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨cs,hcs₀,hcs⟩ := singleton_coloring S x₀ (hS.delete_vertex x₀) α (by decide)
  obtain ⟨ct,hct⟩ := coloring_avoiding (T.deleteEdges {s(y,z)}) (hT.delete_edge y z hyz) {α,β}
    (by simp [hαβ])
  let ca : X × Y → Palette := fun p => if p.1 = x₀ then β else α
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
lemma delete_spoke_coloring (hS : CriticalData S 10) (hT : CriticalData T 9)
    (p₀ : X × Y) (α β : Palette) (hαβ : α ≠ β) (side : Bool) :
    ∃ f : ModuleVertex X Y → Palette,
      ProperExcept (moduleGraph S T) f (a p₀) (if side then t p₀.2 else s p₀.1) ∧
      ∀ p,f (a p) = α ∨ f (a p) = β := by
  classical
  have hex : ∃ γ : Palette, γ ∉ ({α,β} : Finset Palette) := by
    by_contra! h
    have he : ({α,β} : Finset Palette) = univ := eq_univ_of_forall h
    have hc := congrArg Finset.card he
    simp [hαβ,Palette] at hc
  obtain ⟨γ,hγ⟩ := hex
  have hαγ : α ≠ γ := fun h => hγ (by simp [h])
  have hβγ : β ≠ γ := fun h => hγ (by simp [h])
  obtain ⟨c,hca,hcγ,hcs,hct⟩ := singleton_active_coloring S T hS hT p₀ α β γ hαβ hαγ hβγ
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

/-- Lemma 2(3): every module edge has an explicit eleven-color deletion certificate. -/
theorem delete_edge_coloring (hS : CriticalData S 10) (hT : CriticalData T 9)
    (u v : ModuleVertex X Y) (huv : (moduleGraph S T).Adj u v)
    (α β : Palette) (hαβ : α ≠ β) :
    ∃ f : ModuleVertex X Y → Palette, ProperExcept (moduleGraph S T) f u v ∧
      ∀ p,f (a p) = α ∨ f (a p) = β := by
  rcases edge_cases S T u v huv with ⟨x,y,h,rfl,rfl⟩|⟨x,y,h,rfl,rfl⟩|⟨p,h⟩|⟨p,h⟩
  · exact delete_S_coloring S T hS hT x y h α β
  · exact delete_T_coloring S T hS hT x y h α β hαβ
  · obtain ⟨f,hf,hfa⟩ := delete_spoke_coloring S T hS hT p α β hαβ false
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨f,hf,hfa⟩
    · exact ⟨f,fun a b h he => (hf a b h he).symm,hfa⟩
  · obtain ⟨f,hf,hfa⟩ := delete_spoke_coloring S T hS hT p α β hαβ true
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨f,hf,hfa⟩
    · exact ⟨f,fun a b h he => (hf a b h he).symm,hfa⟩

end Deletion

end Module

end Erdos917
