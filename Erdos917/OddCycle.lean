import Erdos917.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

namespace Erdos917
open SimpleGraph

/-- Parity colors a cycle except for its closing edge. -/
lemma cycle_parity_except (n : ℕ) :
    ProperExcept (cycleGraph (n+3)) (fun x : Fin (n+3) => (⟨x.val % 2,by omega⟩ : Fin 2))
      0 (Fin.last (n+2)) := by
  intro a b hab he
  have hp : a.val % 2 = b.val % 2 := congrArg Fin.val he
  have h := cycleGraph_adj.mp hab
  simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last]
  rcases h with h|h
  · have hv := congrArg Fin.val h
    simp only [Fin.val_one] at hv
    by_cases hba : b ≤ a
    · rw [Fin.sub_val_of_le hba] at hv
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hba)] at hv
      omega
  · have hv := congrArg Fin.val h
    simp only [Fin.val_one] at hv
    by_cases hab : a ≤ b
    · rw [Fin.sub_val_of_le hab] at hv
      omega
    · rw [Fin.coe_sub_iff_lt.mpr (lt_of_not_ge hab)] at hv
      omega

/-- Translating the parity assignment moves its sole possible bad edge to any cycle edge. -/
lemma cycle_delete_colorable (n : ℕ) (u v : Fin (n+3)) (huv : (cycleGraph (n+3)).Adj u v) :
    ((cycleGraph (n+3)).deleteEdges {s(u,v)}).Colorable 2 := by
  have h := cycleGraph_adj.mp huv
  suffices hs : ∀ a b : Fin (n+3),a-b=1 →
      ((cycleGraph (n+3)).deleteEdges {s(a,b)}).Colorable 2 by
    rcases h with h|h
    · exact hs u v h
    · simpa only [Sym2.eq_swap] using hs v u h
  intro u v huv
  let f : Fin (n+3) → Fin 2 := fun x => ⟨(x-u).val%2,by omega⟩
  apply coloring_delete_of_except
  intro a b hab he
  have hadj : (cycleGraph (n+3)).Adj (a-u) (b-u) := by
    simpa only [cycleGraph_adj,sub_sub_sub_cancel_right] using hab
  have hex := cycle_parity_except n (a-u) (b-u) hadj he
  have hv : v-u = Fin.last (n+2) := by
    have hv' : v-u = -(1 : Fin (n+3)) := by rw [← huv]; abel
    rw [hv']
    apply Fin.ext
    simp [Fin.val_neg]
  rcases hex with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact Or.inl ⟨sub_eq_zero.mp ha,sub_left_injective (hb.trans hv.symm)⟩
  · exact Or.inr ⟨sub_left_injective (ha.trans hv.symm),sub_eq_zero.mp hb⟩

/-- Every odd cycle of length at least three is vertex and edge critical. -/
theorem odd_cycle_critical (n : ℕ) (hn : Odd (n+3)) : CriticalData (cycleGraph (n+3)) 2 := by
  classical
  have hc := chromaticNumber_cycleGraph_of_odd (n+3) (by omega) hn
  have hcol := (chromaticNumber_eq_iff_colorable_not_colorable (n := 2)).mp hc
  refine ⟨hcol.1,hcol.2,cycle_delete_colorable n,?_⟩
  intro u
  let v : Fin (n+3) := u-1
  have huv : (cycleGraph (n+3)).Adj u v := by
    apply cycleGraph_adj.mpr
    left
    dsimp [v]
    abel
  obtain ⟨c⟩ := cycle_delete_colorable n u v huv
  refine ⟨Coloring.mk (fun x => c x.val) ?_⟩
  intro a b hab
  apply c.valid
  simp only [deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
  exact ⟨hab,by have ha := a.property; have hb := b.property; aesop⟩

end Erdos917
