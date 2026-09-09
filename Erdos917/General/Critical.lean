import Erdos917.Basic
import Erdos917.General.Deletion

namespace Erdos917.General
open SimpleGraph ModuleVertex

namespace Assembly
variable {n : ℕ} {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable (S : SimpleGraph X) (T : SimpleGraph Y) (Z : SimpleGraph ((Part n) × (X × Y)))

omit [Fintype X] [Fintype Y] in
lemma no_isolated (u : AssemblyVertex n X Y) : ∃ v,(assemblyGraph S T Z).Adj u v := by
  rcases u with ⟨i,x|y|p⟩
  · exact ⟨(i,a (x,Classical.arbitrary Y)),Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(i,a (Classical.arbitrary X,y)),Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(i,s p.1),Or.inl ⟨rfl,rfl⟩⟩

/-- The complete criticality conclusion, quantified over all proper subgraphs. -/
theorem critical (hS : CriticalData S (2*n+6)) (hT : CriticalData T (2*n+5))
    {D : ℕ} (hz : Scaffold Z D) (hY : (2*n+6)*D < Fintype.card Y) :
    IsCritical (assemblyGraph S T Z) (2*n+8) := by
  classical
  have he := delete_edge_colorable S T Z hS hT hz
  have hn := no_isolated S T Z
  let u : AssemblyVertex n X Y := (0,s (Classical.arbitrary X))
  obtain ⟨v,huv⟩ := hn u
  have hc := colorable_succ_of_delete (assemblyGraph S T Z) u v (2*n+7) (he u v huv)
  constructor
  · exact (chromaticNumber_eq_iff_colorable_not_colorable (n := (2*n+7))).mpr
      ⟨hc,not_colorable S T Z hS.not_colorable hT.not_colorable hz hY⟩
  · exact proper_subgraph_colorable_of_edge_deletions (assemblyGraph S T Z) (2*n+7) hn he

end Assembly
end Erdos917.General
