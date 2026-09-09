import Erdos917.EdgeCount
import Erdos917.General.Conversion

/-! Exact edge count for the parameterized module construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Erdos917.General
open SimpleGraph Finset
variable {n : ℕ}

lemma structural_edgeCount {h v : ℕ} (hh : 2*n+7 ≤ h) (hv : n+3 ≤ v) :
    (edgeCount (SGraph n h) : ℝ) = (2*n+5) * h - (n+2)*(2*n+7) ∧
      (edgeCount (TGraph n v) : ℝ) = 4*(n+2)*v-(n+3)*(2*n+3) := by
  have hs : h-(2*n+7)+(2*n+7) = h := Nat.sub_add_cancel hh
  have ht : 2*v-(2*n+6)+(2*n+6) = 2*v := Nat.sub_add_cancel (by omega)
  have hs' : ((h-(2*n+7) : ℕ) : ℝ)+(2*n+7) = h := by exact_mod_cast hs
  have ht' : ((2*v-(2*n+6) : ℕ) : ℝ)+(2*n+6) = 2*v := by exact_mod_cast ht
  constructor <;> rw [cliqueJoin_edgeCount, cycle_edgeCount] <;>
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul] <;>
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) n)]

private lemma assembly_pair_sum {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (S : SimpleGraph X) (T : SimpleGraph Y) (H : SimpleGraph V) (e : Y ≃ V × Bool)
    (i j : (Part n)) :
    (∑ u : ModuleVertex X Y, ∑ v : ModuleVertex X Y,
      adjIndicator (assemblyGraph (n := n) S T (blowupGraph (n := n) H e)) (i, u) (j, v)) =
    if i = j then 2 * (edgeCount (moduleGraph S T) : ℝ) else
      ((Fintype.card X : ℝ) * Fintype.card Y) ^ 2 -
        8 * (Fintype.card X : ℝ) ^ 2 * edgeCount H := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, twice_edgeCount]
    simp [adjIndicator, assemblyGraph, assemblyAdj]
  · rw [if_neg hij, ← cross_pair_count H e]
    simp +instances only [ModuleVertex, Fintype.sum_sum_type]
    simp +instances [adjIndicator, assemblyGraph, assemblyAdj, hij, ModuleVertex.a,
      blowupGraph, -sum_boole, -sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases hpq : H.Adj (label e p) (label e q) <;> simp_all [label, Erdos917.label]

private lemma part_sum (i : (Part n)) (a b : ℝ) :
    (∑ j : (Part n), if i = j then a else b) = a + (n+2) * b := by
  classical
  calc
    _ = ∑ j : (Part n), ((if i = j then a - b else 0) + b) := by
      apply sum_congr rfl
      intro j _
      by_cases hij : i = j <;> simp [hij]
    _ = a + (n+2) * b := by simp [sum_add_distrib, Part]; ring

/-- All module edges and all retained cross edges of the actual assembly. -/
theorem assembly_edgeCount {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (n : ℕ) (S : SimpleGraph X) (T : SimpleGraph Y) (H : SimpleGraph V) (e : Y ≃ V × Bool) :
    (edgeCount (assemblyGraph (n := n) S T (blowupGraph (n := n) H e)) : ℝ) =
      (n+3) * (edgeCount (moduleGraph S T) : ℝ) +
        ((n+3)*(n+2)/2 : ℝ) * (((Fintype.card X : ℝ) * Fintype.card Y) ^ 2 -
          8 * (Fintype.card X : ℝ) ^ 2 * edgeCount H) := by
  classical
  have h := twice_edgeCount (assemblyGraph (n := n) S T (blowupGraph (n := n) H e))
  simp only [AssemblyVertex, Fintype.sum_prod_type] at h
  have hs := fun i => sum_comm (s := univ) (t := univ) (f := fun u : ModuleVertex X Y =>
    fun j : (Part n) => ∑ v : ModuleVertex X Y,
      adjIndicator (assemblyGraph (n := n) S T (blowupGraph (n := n) H e)) (i, u) (j, v))
  simp_rw [hs, assembly_pair_sum, part_sum] at h
  simp only [sum_const, card_univ, Fintype.card_fin, Part, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add] at h
  nlinarith only [h]


theorem conversion_edgeCount {V : Type*} [Fintype V]
    (H : SimpleGraph V) {h : ℕ} (hv : n+3 ≤ Fintype.card V) (hh : 2*n+7 ≤ h) :
    (edgeCount (conversionGraph n H h hv) : ℝ) =
      ((n+3)*(n+2)/2 : ℝ) * ((2*h*(Fintype.card V : ℝ))^2-8*(h : ℝ)^2*edgeCount H) +
        (n+3)*(4*h*(Fintype.card V : ℝ)+(2*n+5)*h+4*(n+2)*Fintype.card V-
          (4*(n : ℝ)^2+20*n+23)) := by
  change (edgeCount (assemblyGraph _ _ _) : ℝ) = _
  rw [assembly_edgeCount, module_edgeCount, card_SVertex hh, card_TVertex hv,
    (structural_edgeCount hh hv).1, (structural_edgeCount hh hv).2]
  push_cast
  ring

/-- The lower bound in Proposition 4. -/
theorem conversion_edgeCount_lower {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {h d : ℕ}
    (hv : n+3 ≤ Fintype.card V) (hh : 2*n+7 ≤ h) (hd : ∀ z, H.degree z ≤ d) :
    ((n+3)*(n+2)/2 : ℝ)*(2*h*(Fintype.card V : ℝ))^2*(1-d/(Fintype.card V : ℝ)) ≤
      edgeCount (conversionGraph n H h hv) := by
  have hvpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hb := degree_sum_bound H hd
  have he : (edgeCount (conversionGraph n H h hv) : ℝ) =
      (n+3)*(edgeCount (moduleGraph (SGraph n h) (TGraph n (Fintype.card V))) : ℝ) +
        ((n+3)*(n+2)/2 : ℝ)*((2*h*(Fintype.card V : ℝ))^2-8*(h : ℝ)^2*edgeCount H) := by
    change (edgeCount (assemblyGraph _ _ _) : ℝ) = _
    rw [assembly_edgeCount,card_SVertex hh,card_TVertex hv]
    push_cast
    ring
  have hid : (2*h*(Fintype.card V : ℝ))^2*(1-d/(Fintype.card V : ℝ)) =
      (2*h*(Fintype.card V : ℝ))^2-4*(h : ℝ)^2*Fintype.card V*d := by
    field_simp
    ring
  rw [mul_assoc, hid, he]
  apply le_trans (mul_le_mul_of_nonneg_left (show
    (2*h*(Fintype.card V : ℝ))^2-4*(h : ℝ)^2*Fintype.card V*d ≤
      (2*h*(Fintype.card V : ℝ))^2-8*(h : ℝ)^2*edgeCount H from ?_) (by positivity))
  · exact le_add_of_nonneg_left (by positivity)
  · nlinarith only [mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 4*(h : ℝ)^2 by positivity)]

end Erdos917.General
