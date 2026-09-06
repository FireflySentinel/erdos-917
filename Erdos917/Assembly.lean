import Erdos917.Module

namespace Erdos917
open Finset SimpleGraph ModuleVertex

abbrev Part := Fin 5
abbrev AssemblyVertex (X Y : Type*) := Part × ModuleVertex X Y

/-- `Z` records omitted edges between active vertices. -/
def assemblyAdj {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y)
    (Z : SimpleGraph (Part × (X × Y))) (u v : AssemblyVertex X Y) : Prop :=
  (u.1 = v.1 ∧ (moduleGraph S T).Adj u.2 v.2) ∨
  (u.1 ≠ v.1 ∧ ∃ p q,u.2 = a p ∧ v.2 = a q ∧ ¬ Z.Adj (u.1,p) (v.1,q))

def assemblyGraph {X Y : Type*} (S : SimpleGraph X) (T : SimpleGraph Y)
    (Z : SimpleGraph (Part × (X × Y))) : SimpleGraph (AssemblyVertex X Y) where
  Adj := assemblyAdj S T Z
  symm := ⟨by
    intro u v h
    rcases h with ⟨h,h'⟩|⟨h,p,q,hp,hq,hz⟩
    · exact Or.inl ⟨h.symm,h'.symm⟩
    · exact Or.inr ⟨h.symm,q,p,hq,hp,fun hh => hz hh.symm⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_,h⟩|⟨h,_⟩
    · exact (moduleGraph S T).ne_of_adj h rfl
    · exact h rfl⟩

/-- Finite combinatorial properties of the omitted-edge graph used by Proposition 3. -/
structure Scaffold {X Y : Type*} [Fintype X] [Fintype Y]
    (Z : SimpleGraph (Part × (X × Y))) (D : ℕ) : Prop where
  degree : ∀ i j : Part,i ≠ j → ∀ q : X × Y,
    Nat.card {p : X × Y // Z.Adj (i,p) (j,q)} ≤ D
  no_five : ∀ p : Part → X × Y, ¬ (∀ i j,i ≠ j → Z.Adj (i,p i) (j,p j))
  fill : ∀ i j : Part,i ≠ j → ∀ p q : X × Y,¬ Z.Adj (i,p) (j,q) →
    ∃ r : Part → X × Y,r i = p ∧ r j = q ∧
      ∀ k l,k ≠ l → ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) → Z.Adj (k,r k) (l,r l)
  four : ∀ i : Part,∃ r : Part → X × Y,
    ∀ k l,k ≠ i → l ≠ i → k ≠ l → Z.Adj (k,r k) (l,r l)

namespace Assembly
variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (S : SimpleGraph X) (T : SimpleGraph Y) (Z : SimpleGraph (Part × (X × Y)))

 def restrictModule (f : (assemblyGraph S T Z).Coloring Palette) (i : Part) :
    (moduleGraph S T).Coloring Palette :=
  Coloring.mk (fun v => f (i,v)) (fun h => f.valid (Or.inl ⟨rfl,h⟩))

noncomputable def colorClass (f : (assemblyGraph S T Z).Coloring Palette)
    (i : Part) (α : Palette) : Finset (X × Y) := by
  classical
  exact univ.filter (fun p => f (i,a p) = α)

def Large (f : (assemblyGraph S T Z).Coloring Palette) (D : ℕ) (i : Part) (α : Palette) : Prop :=
  D < (colorClass S T Z f i α).card

lemma large_occurs (f : (assemblyGraph S T Z).Coloring Palette) {D i α}
    (h : Large S T Z f D i α) : ∃ p,f (i,a p) = α := by
  classical
  obtain ⟨p,hp⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le D) h)
  exact ⟨p,(mem_filter.mp hp).2⟩

lemma exists_large_other (hS : ¬ S.Colorable 10) (D : ℕ) (hY : 10*D < Fintype.card Y)
    (f : (assemblyGraph S T Z).Coloring Palette) (i : Part) (α : Palette) :
    ∃ β,β ≠ α ∧ Large S T Z f D i β := by
  classical
  obtain ⟨x,hx⟩ := color_surjective S (by decide : Fintype.card Palette = 10+1)
    hS (Module.restrictS S T (restrictModule S T Z f i)) α
  have hrow (y : Y) : f (i,a (x,y)) ≠ α := by
    have hadj : (assemblyGraph S T Z).Adj (i,s x) (i,a (x,y)) := Or.inl ⟨rfl,rfl⟩
    change f (i,s x) = α at hx
    exact fun he => f.valid hadj (hx.trans he.symm)
  obtain ⟨β,hβ,hcard⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (univ : Finset Y)) (t := univ.erase α) (f := fun y => f (i,a (x,y)))
    (fun y _ => by simp [hrow y]) (by simpa using hY)
  refine ⟨β,(mem_erase.mp hβ).1,lt_of_lt_of_le hcard ?_⟩
  exact card_le_card_of_injOn (fun y => (x,y))
    (by intro y hy; simpa [colorClass] using (mem_filter.mp hy).2)
    (by intro y _ z _ h; exact congrArg Prod.snd h)

lemma large_private {D : ℕ} (hz : Scaffold Z D) (f : (assemblyGraph S T Z).Coloring Palette)
    {i j : Part} (hij : i ≠ j) {α : Palette} (hα : Large S T Z f D i α) (q : X × Y) :
    f (j,a q) ≠ α := by
  classical
  intro he
  have hsub : colorClass S T Z f i α ⊆ univ.filter (fun p => Z.Adj (i,p) (j,q)) := by
    intro p hp
    have hcol : f (i,a p) = α := (mem_filter.mp hp).2
    simp only [mem_filter,mem_univ,true_and]
    by_contra hn
    exact f.valid (Or.inr ⟨hij,p,q,rfl,rfl,hn⟩) (hcol.trans he.symm)
  have hb := hz.degree i j hij q
  have heq : Nat.card {p : X × Y // Z.Adj (i,p) (j,q)} =
      (univ.filter (fun p => Z.Adj (i,p) (j,q))).card := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [heq] at hb
  exact (not_lt_of_ge ((card_le_card hsub).trans hb)) hα

/-- The eleven-color obstruction: ten private colors force a transversal K5 in Z. -/
theorem not_eleven_colorable (hS : ¬ S.Colorable 10) (hT : ¬ T.Colorable 9)
    {D : ℕ} (hz : Scaffold Z D) (hY : 10*D < Fintype.card Y) :
    ¬ (assemblyGraph S T Z).Colorable 11 := by
  classical
  intro hc
  let f : (assemblyGraph S T Z).Coloring Palette := hc.toColoring (by decide)
  have hex (i : Part) : ∃ α β : Palette,α ≠ β ∧ Large S T Z f D i α ∧ Large S T Z f D i β := by
    obtain ⟨α,_,hα⟩ := exists_large_other S T Z hS D hY f i none
    obtain ⟨β,hβα,hβ⟩ := exists_large_other S T Z hS D hY f i α
    exact ⟨α,β,hβα.symm,hα,hβ⟩
  choose α β hab ha hb using hex
  let c : Part × Bool → Palette := fun ib => if ib.2 then β ib.1 else α ib.1
  have hcLarge (ib : Part × Bool) : Large S T Z f D ib.1 (c ib) := by
    rcases ib with ⟨i,b⟩; cases b <;> simp only [c,Bool.false_eq_true,if_false,if_true]
    · exact ha i
    · exact hb i
  have hinj : Function.Injective c := by
    intro ⟨i,b⟩ ⟨j,d⟩ he
    have hij : i = j := by
      by_contra hij
      obtain ⟨q,hq⟩ := large_occurs S T Z f (hcLarge (j,d))
      exact large_private S T Z hz f hij (hcLarge (i,b)) q (hq.trans he.symm)
    subst j
    have hbd : b = d := by
      cases b <;> cases d
      · rfl
      · exact False.elim (hab i he)
      · exact False.elim (hab i he.symm)
      · rfl
    subst d
    rfl
  let P : Finset Palette := univ.image c
  have hP : P.card = 10 := by simp [P,card_image_of_injective _ hinj,Part]
  have hQ : (univ \ P).card = 1 := by rw [card_sdiff_of_subset (subset_univ P)]; simp [hP]
  obtain ⟨γ,hγ⟩ := card_eq_one.mp hQ
  have hextra (i : Part) : ∃ p : X × Y,f (i,a p) = γ := by
    obtain ⟨p,hpα,hpβ⟩ := Module.active_not_two S T hS hT (restrictModule S T Z f i) (α i) (β i) (hab i)
    have hp : f (i,a p) ∈ univ \ P := by
      simp only [mem_sdiff,mem_univ,true_and]
      intro hh
      obtain ⟨⟨j,b⟩,_,he⟩ := mem_image.mp hh
      by_cases hij : j = i
      · subst j
        cases b
        · exact hpα he.symm
        · exact hpβ he.symm
      · exact large_private S T Z hz f hij (hcLarge (j,b)) p he.symm
    rw [hγ] at hp
    exact ⟨p,mem_singleton.mp hp⟩
  choose p hp using hextra
  apply hz.no_five p
  intro i j hij
  by_contra hn
  exact f.valid (Or.inr ⟨hij,p i,p j,rfl,rfl,hn⟩) ((hp i).trans (hp j).symm)

end Assembly
end Erdos917
