import Erdos917.Basic

namespace Erdos917
open SimpleGraph Finset

/-- Join with a single new universal vertex. -/
def coneAdj {V : Type*} (G : SimpleGraph V) : Option V → Option V → Prop
  | none,none => False
  | some u,some v => G.Adj u v
  | _,_ => True

def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj := coneAdj G
  symm := ⟨by rintro (u|u) (v|v) h <;> simp_all [coneAdj,G.adj_comm]⟩
  loopless := ⟨by rintro (u|u) <;> simp [coneAdj]⟩

def cone_coloring {V C : Type*} (G : SimpleGraph V) (c : G.Coloring C) :
    (cone G).Coloring (Option C) :=
  Coloring.mk (Option.map c) (by
    rintro (u|u) (v|v) h
    · exact False.elim h
    · simp
    · simp
    · exact fun he => c.valid h (Option.some.inj he))

lemma cone_internal_except {V C : Type*} (G : SimpleGraph V) (u v : V) (c : V → C)
    (hc : ProperExcept G c u v) : ProperExcept (cone G) (Option.map c) (some u) (some v) := by
  rintro (x|x) (y|y) h he
  · exact False.elim h
  · simp at he
  · simp at he
  · rcases hc x y h (Option.some.inj he) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

lemma cone_spoke_delete {V : Type*} [DecidableEq V] (G : SimpleGraph V) {k : ℕ}
    (hG : CriticalData G k) (u : V) :
    ((cone G).deleteEdges {s(none,some u)}).Colorable (k+1) := by
  obtain ⟨c,hcu,hc⟩ := singleton_coloring G u (hG.delete_vertex u) (0 : Fin (k+1)) (by simp)
  apply coloring_delete_of_except (f := fun v => Option.elim v 0 c)
  rintro (x|x) (y|y) h he
  · exact False.elim h
  · exact Or.inl ⟨rfl,congrArg some (hc y he.symm)⟩
  · exact Or.inr ⟨congrArg some (hc x he),rfl⟩
  · exact False.elim (c.valid h he)

/-- Adding a universal vertex increases the critical chromatic number by one. -/
theorem cone_critical {V : Type*} [DecidableEq V] (G : SimpleGraph V) {k : ℕ}
    (hG : CriticalData G k) : CriticalData (cone G) (k+1) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨c⟩ := hG.colorable
    simpa using (cone_coloring G c).colorable
  · rintro ⟨c⟩
    let f : G.Coloring (Fin (k+1)) := Coloring.mk (fun v => c (some v)) (fun h => c.valid h)
    have hf (v : V) : f v ∈ univ.erase (c none) := by
      have h : (cone G).Adj (some v) none := trivial
      simp only [mem_erase,mem_univ,and_true]
      exact c.valid h
    have hc := colorable_of_palette G f (univ.erase (c none)) hf
    exact hG.not_colorable (by simpa using hc)
  · rintro (u|u) (v|v) huv
    · exact False.elim huv
    · exact cone_spoke_delete G hG v
    · simpa only [Sym2.eq_swap] using cone_spoke_delete G hG u
    · obtain ⟨c⟩ := hG.delete_edge u v huv
      obtain ⟨d⟩ := coloring_delete_of_except (cone G) (Option.map c) (some u) (some v)
        (cone_internal_except G u v c (except_of_coloring_delete G u v c))
      simpa using d.colorable
  · rintro (u|u)
    · obtain ⟨c⟩ := hG.colorable
      let f : {v : Option V // v ≠ none} → Fin (k+1) :=
        fun v => c (v.val.get (Option.isSome_iff_ne_none.mpr v.property))
      refine ⟨Coloring.mk f ?_⟩
      rintro ⟨x,hx⟩ ⟨y,hy⟩ h
      cases x with
      | none => exact False.elim (hx rfl)
      | some x => cases y with
        | none => exact False.elim (hy rfl)
        | some y => exact c.valid h
    · obtain ⟨c⟩ := hG.delete_vertex u
      let f : {v : Option V // v ≠ some u} → Option (Fin k) := fun v =>
        match v with
        | ⟨none,_⟩ => none
        | ⟨some x,hx⟩ => some (c ⟨x,fun he => hx (congrArg some he)⟩)
      have hf : ∀ {x y : {v : Option V // v ≠ some u}},
          ((cone G).induce {v | v ≠ some u}).Adj x y → f x ≠ f y := by
        rintro ⟨x,hx⟩ ⟨y,hy⟩ h
        cases x with
        | none => cases y with
          | none => exact False.elim h
          | some y => simp [f]
        | some x => cases y with
          | none => simp [f]
          | some y =>
            intro he
            have hxy : c ⟨x,fun h => hx (congrArg some h)⟩ ≠
                c ⟨y,fun h => hy (congrArg some h)⟩ := c.valid h
            exact hxy (Option.some.inj he)
      simpa using (Coloring.mk f hf).colorable

/-- Vertex type for K_r joined to G, implemented by r successive universal vertices. -/
def JoinVertex (V : Type*) : ℕ → Type _
  | 0 => V
  | r+1 => Option (JoinVertex V r)

instance {V : Type*} [Fintype V] (r : ℕ) : Fintype (JoinVertex V r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype V)
  | succ r ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Option (JoinVertex V r)))

instance {V : Type*} [Nonempty V] (r : ℕ) : Nonempty (JoinVertex V r) := by
  cases r with
  | zero => exact inferInstanceAs (Nonempty V)
  | succ r => exact ⟨none⟩

@[simp] lemma card_joinVertex {V : Type*} [Fintype V] (r : ℕ) :
    Fintype.card (JoinVertex V r) = Fintype.card V+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Fintype.card (Option (JoinVertex V r)) = _
    rw [Fintype.card_option,ih]
    omega

def cliqueJoin {V : Type*} (G : SimpleGraph V) : (r : ℕ) → SimpleGraph (JoinVertex V r)
  | 0 => G
  | r+1 => cone (cliqueJoin G r)

lemma cliqueJoin_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hG : CriticalData G k) (r : ℕ) :
    CriticalData (cliqueJoin G r) (k+r) := by
  classical
  induction r with
  | zero => exact hG
  | succ r ih => exact cone_critical (cliqueJoin G r) ih

end Erdos917
