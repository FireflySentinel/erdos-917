import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace Erdos917

open Finset SimpleGraph

abbrev Palette := Option (Fin 5 × Bool)

@[simp] lemma card_palette : Fintype.card Palette = 11 := by decide

/-- A coloring certificate with at most one specified monochromatic edge. -/
def ProperExcept {V C : Type*} (G : SimpleGraph V) (f : V → C) (u v : V) : Prop :=
  ∀ a b, G.Adj a b → f a = f b → (a = u ∧ b = v) ∨ (a = v ∧ b = u)

lemma properExcept_iff {V C : Type*} (G : SimpleGraph V) (f : V → C) (u v : V) :
    ProperExcept G f u v ↔ ∀ a b, (G.deleteEdges {s(u,v)}).Adj a b → f a ≠ f b := by
  simp only [deleteEdges_adj,Set.mem_singleton_iff]
  constructor
  · intro hf a b hab heq
    exact hab.2 (Sym2.eq_iff.mpr (hf a b hab.1 heq))
  · intro hf a b hab heq
    by_contra h
    exact hf a b ⟨hab,fun he => h (Sym2.eq_iff.mp he)⟩ heq

lemma coloring_delete_of_except {V C : Type*} (G : SimpleGraph V) (f : V → C) (u v : V)
    (hf : ProperExcept G f u v) : Nonempty ((G.deleteEdges {s(u,v)}).Coloring C) :=
  ⟨Coloring.mk f (fun {a b} h => (properExcept_iff G f u v).mp hf a b h)⟩

lemma except_of_coloring_delete {V C : Type*} (G : SimpleGraph V) (u v : V)
    (f : (G.deleteEdges {s(u,v)}).Coloring C) : ProperExcept G f u v :=
  (properExcept_iff G f u v).mpr (fun _a _b h => f.valid h)

/-- Ordinary vertex and edge criticality, with chromatic number `k+1`. -/
structure CriticalData {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop where
  colorable : G.Colorable (k+1)
  not_colorable : ¬ G.Colorable k
  delete_edge : ∀ u v, G.Adj u v → (G.deleteEdges {s(u,v)}).Colorable k
  delete_vertex : ∀ u, (G.induce {v | v ≠ u}).Colorable k

lemma colorable_of_palette {V C : Type*} [DecidableEq C] (G : SimpleGraph V)
    (f : G.Coloring C) (P : Finset C) (hf : ∀ v, f v ∈ P) : G.Colorable P.card := by
  let c : G.Coloring P := Coloring.mk (fun v => ⟨f v,hf v⟩) (fun {v w} h he =>
    f.valid h (congrArg Subtype.val he))
  simpa using c.colorable

lemma color_surjective {V C : Type*} [Fintype C] [DecidableEq C] {k : ℕ}
    (G : SimpleGraph V) (hk : Fintype.card C = k+1) (hG : ¬ G.Colorable k)
    (f : G.Coloring C) : Function.Surjective f := by
  intro α
  by_contra h
  have havoid : ∀ v,f v ∈ (univ.erase α) := by
    intro v
    simp only [mem_erase,mem_univ,and_true]
    exact fun hv => h ⟨v,hv⟩
  have hc := colorable_of_palette G f (univ.erase α) havoid
  apply hG
  simpa [hk] using hc

lemma coloring_avoiding {V C : Type*} [Fintype C] [DecidableEq C] {k : ℕ}
    (G : SimpleGraph V) (hc : G.Colorable k) (P : Finset C)
    (hcard : k ≤ Fintype.card C - P.card) :
    ∃ f : G.Coloring C, ∀ v, f v ∉ P := by
  classical
  let Q := univ \ P
  have hQ : k ≤ Fintype.card Q := by
    simpa [Q,card_sdiff_of_subset (subset_univ P)] using hcard
  let f := hc.toColoring hQ
  refine ⟨Coloring.mk (fun v => (f v).val) (fun {v w} h he => f.valid h (Subtype.ext he)),?_⟩
  intro v
  exact (mem_sdiff.mp (f v).property).2

lemma singleton_coloring {V C : Type*} [DecidableEq V] [Fintype C] [DecidableEq C] {k : ℕ}
    (G : SimpleGraph V) (u : V) (hc : (G.induce {v | v ≠ u}).Colorable k)
    (α : C) (hcard : k+1 ≤ Fintype.card C) :
    ∃ f : G.Coloring C, f u = α ∧ ∀ v, f v = α → v = u := by
  classical
  obtain ⟨c,hcα⟩ := coloring_avoiding (G.induce {v | v ≠ u}) hc {α} (by simpa using Nat.le_sub_one_of_lt hcard)
  let f : V → C := fun v => if h : v = u then α else c ⟨v,h⟩
  have hf : ∀ {v w},G.Adj v w → f v ≠ f w := by
    intro v w hvw
    by_cases hv : v = u <;> by_cases hw : w = u
    · subst v; subst w; exact False.elim (G.ne_of_adj hvw rfl)
    · simp only [f,dif_pos hv,dif_neg hw]
      have hne : c ⟨w,hw⟩ ≠ α := by simpa using hcα ⟨w,hw⟩
      exact hne.symm
    · simp only [f,dif_neg hv,dif_pos hw]
      simpa using hcα ⟨v,hv⟩
    · simp only [f,dif_neg hv,dif_neg hw]
      exact c.valid hvw
  refine ⟨Coloring.mk f hf,by change f u = α; simp [f],?_⟩
  intro v hv
  by_contra h
  have hh := hcα ⟨v,h⟩
  apply hh
  have heq : c ⟨v,h⟩ = α := by change f v = α at hv; simpa [f,h] using hv
  simp [heq]

/-- An edge-deletion certificate gives an extra-color coloring of the whole graph. -/
lemma colorable_succ_of_delete {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (k : ℕ) (hc : (G.deleteEdges {s(u,v)}).Colorable k) : G.Colorable (k+1) := by
  classical
  obtain ⟨c⟩ := hc
  let f : V → Fin (k+1) := fun w => if w = u then Fin.last k else (c w).castSucc
  refine ⟨Coloring.mk f ?_⟩
  intro a b hab
  by_cases ha : a = u <;> by_cases hb : b = u
  · subst a; subst b; exact False.elim (G.ne_of_adj hab rfl)
  · simp only [f,if_pos ha,if_neg hb]
    exact (Fin.castSucc_ne_last (c b)).symm
  · simp only [f,if_neg ha,if_pos hb]
    exact Fin.castSucc_ne_last (c a)
  · simp only [f,if_neg ha,if_neg hb,ne_eq,Fin.castSucc_inj]
    apply c.valid
    simp only [deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    exact ⟨hab,by aesop⟩

lemma singleton_coloring_avoiding {V C : Type*} [DecidableEq V] [Fintype C] [DecidableEq C] {k : ℕ}
    (G : SimpleGraph V) (u : V) (hc : (G.induce {v | v ≠ u}).Colorable k)
    (P : Finset C) (α : C) (hα : α ∉ P) (hcard : k+1 ≤ Fintype.card C-P.card) :
    ∃ f : G.Coloring C, f u = α ∧ (∀ v,f v = α → v = u) ∧ ∀ v,f v ∉ P := by
  classical
  let Q := univ \ P
  let α' : Q := ⟨α,by simp [Q,hα]⟩
  have hQ : k+1 ≤ Fintype.card Q := by
    simpa [Q,card_sdiff_of_subset (subset_univ P)] using hcard
  obtain ⟨f,hfu,hfα⟩ := singleton_coloring G u hc α' hQ
  refine ⟨Coloring.mk (fun v => (f v).val) (fun {v w} h he => f.valid h (Subtype.ext he)),?_,?_,?_⟩
  · exact congrArg Subtype.val hfu
  · intro v he
    exact hfα v (Subtype.ext he)
  · intro v
    exact (mem_sdiff.mp (f v).property).2

lemma update_proper_except {V C : Type*} [DecidableEq V] (G : SimpleGraph V)
    (f : G.Coloring C) (u v : V) (α : C)
    (hu : ∀ w,G.Adj u w → f w = α → w = v) :
    ProperExcept G (Function.update f u α) u v := by
  intro a b hab heq
  by_cases ha : a = u <;> by_cases hb : b = u
  · subst a; subst b; exact False.elim (G.ne_of_adj hab rfl)
  · subst a
    have hfb : f b = α := by simpa [Function.update_of_ne hb] using heq.symm
    exact Or.inl ⟨rfl,hu b hab hfb⟩
  · subst b
    have hfa : f a = α := by simpa [Function.update_of_ne ha] using heq
    exact Or.inr ⟨hu a hab.symm hfa,rfl⟩
  · have h := f.valid hab
    exact False.elim (h (by simpa [Function.update_of_ne ha,Function.update_of_ne hb] using heq))

end Erdos917
