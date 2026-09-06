import Erdos917.Assembly

namespace Erdos917
open Finset SimpleGraph ModuleVertex
namespace Assembly

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable (S : SimpleGraph X) (T : SimpleGraph Y) (Z : SimpleGraph (Part × (X × Y)))

lemma common_color {i j : Part} (hij : i ≠ j) {α β : Palette}
    (hα : α = some (i,false) ∨ α = some (i,true) ∨ α = none)
    (hβ : β = some (j,false) ∨ β = some (j,true) ∨ β = none) (he : α = β) :
    α = none ∧ β = none := by
  rcases hα with rfl|rfl|rfl <;> rcases hβ with rfl|rfl|rfl <;> simp_all

omit [Fintype X] [Fintype Y] in
lemma assemble_except (c : Part → ModuleVertex X Y → Palette) (u v : AssemblyVertex X Y)
    (hlocal : ∀ i x y,(moduleGraph S T).Adj x y → c i x = c i y →
      ((i,x) = u ∧ (i,y) = v) ∨ ((i,x) = v ∧ (i,y) = u))
    (hrange : ∀ i p,c i (a p) = some (i,false) ∨ c i (a p) = some (i,true) ∨ c i (a p) = none)
    (hshared : ∀ i j,i ≠ j → ∀ p q,c i (a p) = none → c j (a q) = none →
      Z.Adj (i,p) (j,q) ∨ (((i,a p) = u ∧ (j,a q) = v) ∨ ((i,a p) = v ∧ (j,a q) = u))) :
    ProperExcept (assemblyGraph S T Z) (fun w => c w.1 w.2) u v := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hadj he
  rcases hadj with ⟨hij,hxy⟩|⟨hij,p,q,hp,hq,hz⟩
  · change i = j at hij
    subst j
    exact hlocal i x y hxy he
  · change x = a p at hp
    change y = a q at hq
    subst x; subst y
    obtain ⟨hi,hj⟩ := common_color hij (hrange i p) (hrange j q) he
    exact (hshared i j hij p q hi hj).resolve_left hz

/-- Every cross-module edge can be the sole monochromatic edge in an eleven-color assignment. -/
theorem delete_cross_coloring [DecidableEq X] [DecidableEq Y]
    (hS : CriticalData S 10) (hT : CriticalData T 9) {D : ℕ} (hz : Scaffold Z D)
    (i j : Part) (hij : i ≠ j) (p q : X × Y) (hpq : ¬ Z.Adj (i,p) (j,q)) :
    ∃ f : AssemblyVertex X Y → Palette,
      ProperExcept (assemblyGraph S T Z) f (i,a p) (j,a q) := by
  classical
  obtain ⟨r,hri,hrj,hr⟩ := hz.fill i j hij p q hpq
  have hex (k : Part) := Module.singleton_active_coloring S T hS hT (r k)
    (some (k,false)) (some (k,true)) none (by simp) (by simp) (by simp)
  choose c hc hcγ hcs hct using hex
  refine ⟨fun w => c w.1 w.2,assemble_except S T Z (fun k => c k) (i,a p) (j,a q) ?_ hc ?_⟩
  · intro k x y h he
    exact False.elim ((c k).valid h he)
  · intro k l hkl x y hx hy
    have hx' : x = r k := (hcγ k x).mp hx
    have hy' : y = r l := (hcγ l y).mp hy
    subst x; subst y
    by_cases he : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · right
      rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact Or.inl ⟨by rw [hri],by rw [hrj]⟩
      · exact Or.inr ⟨by rw [hrj],by rw [hri]⟩
    · exact Or.inl (hr k l hkl he)

/-- Every internal edge admits an eleven-color deletion assignment of the whole graph. -/
theorem delete_internal_coloring [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (hS : CriticalData S 10) (hT : CriticalData T 9) {D : ℕ} (hz : Scaffold Z D)
    (i : Part) (u v : ModuleVertex X Y) (huv : (moduleGraph S T).Adj u v) :
    ∃ f : AssemblyVertex X Y → Palette,
      ProperExcept (assemblyGraph S T Z) f (i,u) (i,v) := by
  classical
  obtain ⟨r,hr⟩ := hz.four i
  obtain ⟨d,hd,hda⟩ := Module.delete_edge_coloring S T hS hT u v huv
    (some (i,false)) (some (i,true)) (by simp)
  have hex (k : Part) := Module.singleton_active_coloring S T hS hT (r k)
    (some (k,false)) (some (k,true)) none (by simp) (by simp) (by simp)
  choose c hc hcγ hcs hct using hex
  let f : Part → ModuleVertex X Y → Palette := fun k => if k = i then d else c k
  refine ⟨fun w => f w.1 w.2,assemble_except S T Z f (i,u) (i,v) ?_ ?_ ?_⟩
  · intro k x y h he
    by_cases hk : k = i
    · subst k
      have hh : d x = d y := by simpa [f] using he
      rcases hd x y h hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
    · exact False.elim ((c k).valid h (by simpa [f,hk] using he))
  · intro k p
    by_cases hk : k = i
    · subst k
      simpa [f] using (hda p).imp_right Or.inl
    · simpa [f,hk] using hc k p
  · intro k l hkl p q hp hq
    have hk : k ≠ i := by
      intro hh; subst k
      have hp' : d (a p) = none := by simpa [f] using hp
      rcases hda p with h|h <;> simp_all
    have hl : l ≠ i := by
      intro hh; subst l
      have hq' : d (a q) = none := by simpa [f] using hq
      rcases hda q with h|h <;> simp_all
    have hp' : p = r k := (hcγ k p).mp (by simpa [f,hk] using hp)
    have hq' : q = r l := (hcγ l q).mp (by simpa [f,hl] using hq)
    subst p; subst q
    exact Or.inl (hr k l hk hl hkl)

/-- All edges, including structural edges and both types of active spokes, are covered. -/
theorem delete_edge_eleven_colorable [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (hS : CriticalData S 10) (hT : CriticalData T 9) {D : ℕ} (hz : Scaffold Z D)
    (u v : AssemblyVertex X Y) (huv : (assemblyGraph S T Z).Adj u v) :
    ((assemblyGraph S T Z).deleteEdges {s(u,v)}).Colorable 11 := by
  have hex : ∃ f : AssemblyVertex X Y → Palette,ProperExcept (assemblyGraph S T Z) f u v := by
    rcases u with ⟨i,u⟩; rcases v with ⟨j,v⟩
    rcases huv with ⟨hij,h⟩|⟨hij,p,q,hp,hq,hz'⟩
    · change i = j at hij
      subst j
      exact delete_internal_coloring S T Z hS hT hz i u v h
    · change u = a p at hp
      change v = a q at hq
      subst u; subst v
      exact delete_cross_coloring S T Z hS hT hz i j hij p q hz'
  obtain ⟨f,hf⟩ := hex
  obtain ⟨c⟩ := coloring_delete_of_except (assemblyGraph S T Z) f u v hf
  simpa using c.colorable

end Assembly
end Erdos917
