import Erdos917.Critical
import Erdos917.SaturationDefinition
import Erdos917.Cone
import Erdos917.OddCycle

namespace Erdos917
open SimpleGraph

/-- K8 joined to the odd cycle of length h-8 (for h ≥ 11). -/
abbrev SVertex (h : ℕ) := JoinVertex (Fin ((h-11)+3)) 8
abbrev SGraph (h : ℕ) := cliqueJoin (cycleGraph ((h-11)+3)) 8

/-- K7 joined to the odd cycle of length 2v-7 (for v ≥ 5). -/
abbrev TVertex (v : ℕ) := JoinVertex (Fin ((2*v-10)+3)) 7
abbrev TGraph (v : ℕ) := cliqueJoin (cycleGraph ((2*v-10)+3)) 7

lemma card_SVertex {h : ℕ} (hh : 11 ≤ h) : Fintype.card (SVertex h) = h := by
  simp only [SVertex,card_joinVertex,Fintype.card_fin]
  omega

lemma card_TVertex {v : ℕ} (hv : 5 ≤ v) : Fintype.card (TVertex v) = 2*v := by
  simp only [TVertex,card_joinVertex,Fintype.card_fin]
  omega

lemma SGraph_critical {h : ℕ} (hh : 11 ≤ h) (ho : Odd h) : CriticalData (SGraph h) 10 := by
  have hn : Odd ((h-11)+3) := by simp only [Nat.odd_iff] at *; omega
  exact cliqueJoin_critical _ (odd_cycle_critical (h-11) hn) 8

lemma TGraph_critical {v : ℕ} (hv : 5 ≤ v) : CriticalData (TGraph v) 9 := by
  have hn : Odd ((2*v-10)+3) := by simp only [Nat.odd_iff]; omega
  exact cliqueJoin_critical _ (odd_cycle_critical (2*v-10) hn) 7

noncomputable def labelEquiv (V : Type*) [Fintype V] (hv : 5 ≤ Fintype.card V) :
    TVertex (Fintype.card V) ≃ V × Bool :=
  Fintype.equivOfCardEq (by rw [card_TVertex hv]; simp [mul_comm])

/-- Exactly the five-module graph in Proposition 3, with a chosen labeling bijection. -/
noncomputable def conversionGraph {V : Type*} [Fintype V] (H : SimpleGraph V)
    (h : ℕ) (hv : 5 ≤ Fintype.card V) :
    SimpleGraph (AssemblyVertex (SVertex h) (TVertex (Fintype.card V))) :=
  assemblyGraph (SGraph h) (TGraph (Fintype.card V)) (blowupGraph H (labelEquiv V hv))

/-- Proposition 3, criticality component, with standard K5-saturation hypotheses.
No module coloring, odd-cycle criticality, or omitted-edge property is assumed here. -/
theorem conversion_twelve_critical {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : 5 ≤ Fintype.card V) (hh : 11 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree 5)
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree 5)
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (hsize : 40*h*d < Fintype.card V) :
    IsCritical (conversionGraph H h hv) 12 := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hs := SaturatedK5.of_add_edges H hfree hsat
  have hz := Saturation.scaffold (X := SVertex h) H (labelEquiv V hv) hs hdegree hsmall
  apply Assembly.twelve_critical _ _ _ (SGraph_critical hh hodd) (TGraph_critical hv) hz
  rw [card_TVertex hv,card_SVertex hh]
  nlinarith

/-- The standard chromatic-number conclusion extracted from the full criticality theorem. -/
theorem conversion_chromaticNumber {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : 5 ≤ Fintype.card V) (hh : 11 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree 5)
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree 5)
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (hsize : 40*h*d < Fintype.card V) :
    (conversionGraph H h hv).chromaticNumber = 12 :=
  (conversion_twelve_critical H h d hv hh hodd hfree hsat hdegree hsmall hsize).1

/-- Every edge of the concrete construction, with no restriction on its type. -/
theorem conversion_delete_edge_colorable {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : 5 ≤ Fintype.card V)
    (hh : 11 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree 5)
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree 5)
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (u v : AssemblyVertex (SVertex h) (TVertex (Fintype.card V)))
    (huv : (conversionGraph H h hv).Adj u v) :
    ((conversionGraph H h hv).deleteEdges {s(u,v)}).Colorable 11 := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hs := SaturatedK5.of_add_edges H hfree hsat
  have hz := Saturation.scaffold (X := SVertex h) H (labelEquiv V hv) hs hdegree hsmall
  exact Assembly.delete_edge_eleven_colorable _ _ _ (SGraph_critical hh hodd) (TGraph_critical hv) hz u v huv

/-- Cardinality check identifying the formal vertex type with the manuscript construction. -/
lemma conversion_order {V : Type*} [Fintype V] {h : ℕ}
    (hv : 5 ≤ Fintype.card V) (hh : 11 ≤ h) :
    Fintype.card (AssemblyVertex (SVertex h) (TVertex (Fintype.card V))) =
      5 * (2*h*Fintype.card V+h+2*Fintype.card V) := by
  simp only [AssemblyVertex,ModuleVertex,Fintype.card_prod,Fintype.card_sum,
    Part,Fintype.card_fin,card_SVertex hh,card_TVertex hv]
  ring

end Erdos917
