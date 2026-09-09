import Erdos917.Cone
import Erdos917.OddCycle
import Erdos917.ModuleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Edge counts for graphs, joins, and coloring modules. -/
set_option backward.isDefEq.respectTransparency false
namespace Erdos917
open SimpleGraph Finset

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

end Erdos917
