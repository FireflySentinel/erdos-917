import Erdos917.Main
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option backward.isDefEq.respectTransparency false

namespace Erdos917
open SimpleGraph Finset

/-- The number of unordered edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

lemma edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : edgeCount G = G.edgeFinset.card := by
  classical
  simp [edgeCount, Nat.card_eq_fintype_card, G.card_edgeSet]

noncomputable def adjIndicator {V : Type*} (G : SimpleGraph V) (u v : V) : ℝ := by
  classical
  exact if G.Adj u v then 1 else 0

lemma twice_edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) :
    2 * (edgeCount G : ℝ) = ∑ u, ∑ v, adjIndicator G u v := by
  classical
  rw [edgeCount_eq_card_edgeFinset]
  have he := G.two_mul_card_edgeFinset
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) he
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type, adjIndicator] using hcast

lemma degree_sum_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : ∀ v, G.degree v ≤ d) :
    2 * (edgeCount G : ℝ) ≤ (Fintype.card V : ℝ) * d := by
  classical
  have he := G.sum_degrees_eq_twice_card_edges
  have hb := sum_le_sum (s := (univ : Finset V)) (fun v _ => hd v)
  rw [he] at hb
  rw [edgeCount_eq_card_edgeFinset]
  exact_mod_cast (by simpa using hb : 2 * G.edgeFinset.card ≤ Fintype.card V * d)

lemma cone_edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (edgeCount (cone G) : ℝ) = edgeCount G + Fintype.card V := by
  have h : 2 * (edgeCount (cone G) : ℝ) =
      2 * Fintype.card V + 2 * (edgeCount G : ℝ) := by
    rw [twice_edgeCount, twice_edgeCount]
    simp +instances only [Fintype.sum_option, adjIndicator, cone, coneAdj, sum_add_distrib,
      if_true, if_false, sum_const, card_univ, nsmul_eq_mul, mul_one, zero_add]
    ring
  linarith

lemma cycle_edgeCount (n : ℕ) : (edgeCount (cycleGraph (n + 3)) : ℝ) = n + 3 := by
  classical
  have h := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
  simp only [cycleGraph_degree_three_le, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  rw [← edgeCount_eq_card_edgeFinset] at h
  exact_mod_cast (by omega : edgeCount (cycleGraph (n + 3)) = n + 3)

lemma cliqueJoin_edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) :
    (edgeCount (cliqueJoin G r) : ℝ) = edgeCount G + r * (Fintype.card V : ℝ) +
      (r : ℝ) * (r - 1) / 2 := by
  induction r with
  | zero => change (edgeCount G : ℝ) = _; simp
  | succ r ih =>
    change (edgeCount (cone (cliqueJoin G r)) : ℝ) = _
    rw [cone_edgeCount, ih, card_joinVertex]
    push_cast
    ring

lemma structural_edgeCount {h v : ℕ} (hh : 11 ≤ h) (hv : 5 ≤ v) :
    (edgeCount (SGraph h) : ℝ) = 9 * h - 44 ∧
      (edgeCount (TGraph v) : ℝ) = 16 * v - 35 := by
  have hs : h - 11 + 11 = h := Nat.sub_add_cancel hh
  have ht : 2 * v - 10 + 10 = 2 * v := Nat.sub_add_cancel (by omega)
  have hs' : ((h - 11 : ℕ) : ℝ) + 11 = h := by exact_mod_cast hs
  have ht' : ((2 * v - 10 : ℕ) : ℝ) + 10 = 2 * v := by exact_mod_cast ht
  constructor <;> rw [cliqueJoin_edgeCount, cycle_edgeCount] <;>
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] <;> linarith

lemma module_edgeCount {X Y : Type*} [Fintype X] [Fintype Y]
    (S : SimpleGraph X) (T : SimpleGraph Y) :
    (edgeCount (moduleGraph S T) : ℝ) = edgeCount S + edgeCount T +
      2 * (Fintype.card X : ℝ) * Fintype.card Y := by
  classical
  have h : 2 * (edgeCount (moduleGraph S T) : ℝ) =
      2 * edgeCount S + 2 * edgeCount T +
        4 * (Fintype.card X : ℝ) * Fintype.card Y := by
    rw [twice_edgeCount, twice_edgeCount, twice_edgeCount]
    simp +instances only [ModuleVertex, Fintype.sum_sum_type, Fintype.sum_prod_type,
      adjIndicator, moduleGraph, moduleAdj, sum_add_distrib, if_false, sum_const_zero,
      zero_add, add_zero, sum_ite_eq, mem_univ, if_true,
      sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_prod, Nat.cast_mul]
    simp [apply_ite, eq_comm]
    ring
  linarith

lemma sum_labels {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (e : Y ≃ V × Bool) (f : V → ℝ) :
    ∑ p : X × Y, f (label e p) = 2 * (Fintype.card X : ℝ) * ∑ z, f z := by
  rw [Fintype.sum_prod_type]
  simp only [label]
  simp_rw [e.sum_comp (fun z : V × Bool => f z.1)]
  simp only [Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_ofNat, ← mul_sum]
  ring

/-- Ordered active pairs retained between two distinct modules. -/
lemma cross_pair_count {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (H : SimpleGraph V) (e : Y ≃ V × Bool) :
    (∑ p : X × Y, ∑ q : X × Y, (1 - adjIndicator H (label e p) (label e q) : ℝ)) =
      ((Fintype.card X : ℝ) * Fintype.card Y) ^ 2 -
        8 * (Fintype.card X : ℝ) ^ 2 * edgeCount H := by
  have hlabels : (∑ p : X × Y, ∑ q : X × Y,
      adjIndicator H (label e p) (label e q)) =
      8 * (Fintype.card X : ℝ) ^ 2 * edgeCount H := by
    simp_rw [sum_labels (X := X) e]
    rw [← mul_sum, sum_comm]
    have hl (y : V) := sum_labels (X := X) e (fun z => adjIndicator H z y)
    simp_rw [hl, ← mul_sum]
    rw [sum_comm, ← twice_edgeCount]
    ring
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_prod,
    nsmul_eq_mul, mul_one, Nat.cast_mul]
  rw [hlabels]
  ring

private lemma assembly_pair_sum {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (S : SimpleGraph X) (T : SimpleGraph Y) (H : SimpleGraph V) (e : Y ≃ V × Bool)
    (i j : Part) :
    (∑ u : ModuleVertex X Y, ∑ v : ModuleVertex X Y,
      adjIndicator (assemblyGraph S T (blowupGraph H e)) (i, u) (j, v)) =
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
    by_cases hpq : H.Adj (label e p) (label e q) <;> simp [hpq]

private lemma part_sum (i : Part) (a b : ℝ) :
    (∑ j : Part, if i = j then a else b) = a + 4 * b := by
  classical
  calc
    _ = ∑ j : Part, ((if i = j then a - b else 0) + b) := by
      apply sum_congr rfl
      intro j _
      by_cases hij : i = j <;> simp [hij]
    _ = a + 4 * b := by simp [sum_add_distrib, Part]; ring

/-- All module edges and all retained cross edges of the actual assembly. -/
theorem assembly_edgeCount {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    (S : SimpleGraph X) (T : SimpleGraph Y) (H : SimpleGraph V) (e : Y ≃ V × Bool) :
    (edgeCount (assemblyGraph S T (blowupGraph H e)) : ℝ) =
      5 * (edgeCount (moduleGraph S T) : ℝ) +
        10 * (((Fintype.card X : ℝ) * Fintype.card Y) ^ 2 -
          8 * (Fintype.card X : ℝ) ^ 2 * edgeCount H) := by
  classical
  have h := twice_edgeCount (assemblyGraph S T (blowupGraph H e))
  simp only [AssemblyVertex, Fintype.sum_prod_type] at h
  have hs := fun i => sum_comm (s := univ) (t := univ) (f := fun u : ModuleVertex X Y =>
    fun j : Part => ∑ v : ModuleVertex X Y,
      adjIndicator (assemblyGraph S T (blowupGraph H e)) (i, u) (j, v))
  simp_rw [hs, assembly_pair_sum, part_sum] at h
  simp only [sum_const, card_univ, show Fintype.card Part = 5 from rfl, nsmul_eq_mul, Nat.cast_ofNat] at h
  linarith

/-- Proposition 3, equation (3.4), with real subtraction rather than truncated subtraction. -/
theorem conversion_edgeCount {V : Type*} [Fintype V]
    (H : SimpleGraph V) {h : ℕ} (hv : 5 ≤ Fintype.card V) (hh : 11 ≤ h) :
    (edgeCount (conversionGraph H h hv) : ℝ) =
      10 * ((2 * h * (Fintype.card V : ℝ)) ^ 2 - 8 * (h : ℝ) ^ 2 * edgeCount H) +
        5 * (4 * h * (Fintype.card V : ℝ) + 9 * h + 16 * Fintype.card V - 79) := by
  change (edgeCount (assemblyGraph _ _ _) : ℝ) = _
  rw [assembly_edgeCount, module_edgeCount, card_SVertex hh, card_TVertex hv,
    (structural_edgeCount hh hv).1, (structural_edgeCount hh hv).2]
  push_cast
  ring

/-- Proposition 3, equation (3.3). Only a degree bound is needed for this estimate. -/
theorem conversion_edgeCount_lower {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {h d : ℕ}
    (hv : 5 ≤ Fintype.card V) (hh : 11 ≤ h) (hd : ∀ z, H.degree z ≤ d) :
    10 * (2 * h * (Fintype.card V : ℝ)) ^ 2 * (1 - d / (Fintype.card V : ℝ)) ≤
      edgeCount (conversionGraph H h hv) := by
  have hvpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hb := degree_sum_bound H hd
  have he : (edgeCount (conversionGraph H h hv) : ℝ) =
      5 * (edgeCount (moduleGraph (SGraph h) (TGraph (Fintype.card V))) : ℝ) +
        10 * ((2 * h * (Fintype.card V : ℝ)) ^ 2 - 8 * (h : ℝ) ^ 2 * edgeCount H) := by
    change (edgeCount (assemblyGraph _ _ _) : ℝ) = _
    rw [assembly_edgeCount, card_SVertex hh, card_TVertex hv]
    push_cast
    ring
  have hmodule : (0 : ℝ) ≤ edgeCount (moduleGraph (SGraph h) (TGraph (Fintype.card V))) :=
    Nat.cast_nonneg _
  have hid : (2 * h * (Fintype.card V : ℝ)) ^ 2 * (1 - d / (Fintype.card V : ℝ)) =
      (2 * h * (Fintype.card V : ℝ)) ^ 2 -
        4 * (h : ℝ) ^ 2 * Fintype.card V * d := by
    field_simp
    ring
  rw [mul_assoc 10, hid, he]
  nlinarith [mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 4 * (h : ℝ) ^ 2 by positivity)]

end Erdos917
