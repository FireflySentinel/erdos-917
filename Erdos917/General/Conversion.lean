import Erdos917.General.Critical
import Erdos917.General.SaturationDefinition
import Erdos917.Cone
import Erdos917.OddCycle

/-! Proposition 4: construction of critical graphs from saturated graphs of arbitrary clique order. -/

namespace Erdos917.General
open SimpleGraph
variable {n : ℕ}

/-- A clique joined to an odd cycle, with chromatic number `2 n + 7`. -/
abbrev SVertex (n h : ℕ) := JoinVertex (Fin ((h-(2*n+7))+3)) (2*n+4)
abbrev SGraph (n h : ℕ) := cliqueJoin (cycleGraph ((h-(2*n+7))+3)) (2*n+4)

/-- A clique joined to an odd cycle, with chromatic number `2 n + 6`. -/
abbrev TVertex (n v : ℕ) := JoinVertex (Fin ((2*v-(2*n+6))+3)) (2*n+3)
abbrev TGraph (n v : ℕ) := cliqueJoin (cycleGraph ((2*v-(2*n+6))+3)) (2*n+3)

lemma card_SVertex {h : ℕ} (hh : 2*n+7 ≤ h) : Fintype.card (SVertex n h) = h := by
  simp only [SVertex,card_joinVertex,Fintype.card_fin]
  omega

lemma card_TVertex {v : ℕ} (hv : n+3 ≤ v) : Fintype.card (TVertex n v) = 2*v := by
  simp only [TVertex,card_joinVertex,Fintype.card_fin]
  omega

lemma SGraph_critical {h : ℕ} (hh : 2*n+7 ≤ h) (ho : Odd h) : CriticalData (SGraph n h) (2*n+6) := by
  have hn : Odd ((h-(2*n+7))+3) := by simp only [Nat.odd_iff] at *; omega
  convert cliqueJoin_critical _ (odd_cycle_critical (h-(2*n+7)) hn) (2*n+4) using 1; omega

lemma TGraph_critical {v : ℕ} (hv : n+3 ≤ v) : CriticalData (TGraph n v) (2*n+5) := by
  have hn : Odd ((2*v-(2*n+6))+3) := by simp only [Nat.odd_iff]; omega
  convert cliqueJoin_critical _ (odd_cycle_critical (2*v-(2*n+6)) hn) (2*n+3) using 1; omega

noncomputable def labelEquiv (n : ℕ) (V : Type*) [Fintype V] (hv : n+3 ≤ Fintype.card V) :
    TVertex n (Fintype.card V) ≃ V × Bool :=
  Fintype.equivOfCardEq (by rw [card_TVertex hv]; simp [mul_comm])

/-- The module graph in Proposition 4, with a chosen labeling bijection. -/
noncomputable def conversionGraph (n : ℕ) {V : Type*} [Fintype V] (H : SimpleGraph V)
    (h : ℕ) (hv : n+3 ≤ Fintype.card V) :
    SimpleGraph (AssemblyVertex n (SVertex n h) (TVertex n (Fintype.card V))) :=
  assemblyGraph (SGraph n h) (TGraph n (Fintype.card V)) (blowupGraph H (labelEquiv n V hv))

/-- Proposition 4: the conversion graph is critical. -/
theorem conversion_critical {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : n+3 ≤ Fintype.card V) (hh : 2*n+7 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree (n+3))
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree (n+3))
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (hsize : 2*(n+3)*(n+2)*h*d < Fintype.card V) :
    IsCritical (conversionGraph n H h hv) (2*n+8) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hs := Saturated.of_add_edges H hfree hsat
  have hz := Saturation.scaffold (X := SVertex n h) H (labelEquiv n V hv) hs hdegree hsmall
  apply Assembly.critical _ _ _ (SGraph_critical hh hodd) (TGraph_critical hv) hz
  rw [card_TVertex hv,card_SVertex hh]
  nlinarith

/-- The standard chromatic-number conclusion extracted from the full criticality theorem. -/
theorem conversion_chromaticNumber {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : n+3 ≤ Fintype.card V) (hh : 2*n+7 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree (n+3))
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree (n+3))
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (hsize : 2*(n+3)*(n+2)*h*d < Fintype.card V) :
    (conversionGraph n H h hv).chromaticNumber= 2*n+8 :=
  (conversion_critical H h d hv hh hodd hfree hsat hdegree hsmall hsize).1

/-- Deleting any edge of the conversion graph leaves a `(2 n + 7)`-colorable graph. -/
theorem conversion_delete_edge_colorable {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h d : ℕ)
    (hv : n+3 ≤ Fintype.card V)
    (hh : 2*n+7 ≤ h) (hodd : Odd h)
    (hfree : H.CliqueFree (n+3))
    (hsat : ∀ z w,z ≠ w → ¬ H.Adj z w → ¬ (H ⊔ edge z w).CliqueFree (n+3))
    (hdegree : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1)
    (u v : AssemblyVertex n (SVertex n h) (TVertex n (Fintype.card V)))
    (huv : (conversionGraph n H h hv).Adj u v) :
    ((conversionGraph n H h hv).deleteEdges {s(u,v)}).Colorable (2*n+7) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hs := Saturated.of_add_edges H hfree hsat
  have hz := Saturation.scaffold (X := SVertex n h) H (labelEquiv n V hv) hs hdegree hsmall
  exact Assembly.delete_edge_colorable _ _ _ (SGraph_critical hh hodd) (TGraph_critical hv) hz u v huv

/-- The order of the module conversion graph. -/
lemma conversion_order {V : Type*} [Fintype V] {h : ℕ}
    (hv : n+3 ≤ Fintype.card V) (hh : 2*n+7 ≤ h) :
    Fintype.card (AssemblyVertex n (SVertex n h) (TVertex n (Fintype.card V))) =
      (n+3) * (2*h*Fintype.card V+h+2*Fintype.card V) := by
  simp only [AssemblyVertex,ModuleVertex,Fintype.card_prod,Fintype.card_sum,
    Part,Fintype.card_fin,card_SVertex hh,card_TVertex hv]
  ring

end Erdos917.General
