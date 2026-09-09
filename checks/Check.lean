import Erdos917

/-! Axiom checks and the statement of the general construction. -/

/-- info: 'Erdos917.not_density_three_eighths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.not_density_three_eighths

/-- info: 'Erdos917.f12_not_density_below_two_fifths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.f12_not_density_below_two_fifths

/-- info: 'Erdos917.dense_critical_graphs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.dense_critical_graphs

/-- info: 'Erdos917.General.exists_prime_power_exact_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.General.exists_prime_power_exact_model

open Filter Topology Erdos917 in
example (k : ℕ) (hk : 8 ≤ k) :
    ∃ (N : ℕ → ℕ) (G : ∀ s, SimpleGraph (Fin (N s))),
      Tendsto N atTop atTop ∧ (∀ s, IsCritical (G s) k) ∧
      Tendsto (fun s => (edgeCount (G s) : ℝ)/(N s : ℝ)^2) atTop
        (𝓝 (if Even k then ((k : ℝ)-4)/(2*((k : ℝ)-2))
          else ((k : ℝ)-5)/(2*((k : ℝ)-3)))) := dense_critical_graphs k hk

/-- info: 'Erdos917.f12_limsup_ge_two_fifths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.f12_limsup_ge_two_fifths

/-- info: 'Erdos917.corollary_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.corollary_two

open Filter Topology Erdos917 in
example (k : ℕ) (hk : 8 ≤ k) (h9 : k ≠ 9) :
    ¬ Asymptotics.IsEquivalent atTop (fun n : ℕ => (fk k n : ℝ))
      (fun n : ℕ => (1/2*(1-1/((k/3 : ℕ) : ℝ)))*(n : ℝ)^2) :=
  (corollary_two k hk h9).2.2.2

open Erdos917 in
example : constructionDensity 9 = 1/3 ∧ erdosCoefficient 9 = 1/3 ∧
    toftCoefficient 9 = 1/3 := coefficients_nine
