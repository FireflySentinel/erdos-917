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

def label {X Y V : Type*} (e : Y ≃ V × Bool) (p : X × Y) : V := (e p.2).1

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

end Module
end Erdos917
