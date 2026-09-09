import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Graph-theoretic definitions used in the main statements. -/
namespace Erdos917
open SimpleGraph

/-- Full criticality: chromatic number k, and every proper subgraph
(including subgraphs missing vertices) is (k-1)-colorable. -/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ Q : G.Subgraph,Q ≠ ⊤ → Q.coe.Colorable (k-1)

/-- The manuscript's edge-deletion convention for criticality. -/
def IsEdgeCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ u v, G.Adj u v → (G.deleteEdges {s(u, v)}).Colorable (k - 1)

/-- The number of unordered edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The edge-deletion version of the extremal function, with empty value zero. -/
noncomputable def fk (k n : ℕ) : ℕ :=
  sSup (edgeCount '' {G : SimpleGraph (Fin n) | IsEdgeCritical G k})

/-- The twelve-critical instance of the extremal function. -/
noncomputable abbrev f12 (n : ℕ) : ℕ := fk 12 n

end Erdos917
