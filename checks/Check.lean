import Erdos917

/-! Axiom checks for the twelve-critical family, its density, and the extremal-function consequences. -/

/-- info: 'Erdos917.AEHK.canonical_counterexample_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.AEHK.canonical_counterexample_critical

/-- info: 'Erdos917.AEHK.canonical_counterexample_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.AEHK.canonical_counterexample_density

/-- info: 'Erdos917.not_density_three_eighths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.not_density_three_eighths

/-- info: 'Erdos917.f12_not_density_below_two_fifths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos917.f12_not_density_below_two_fifths
