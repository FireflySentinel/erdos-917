import Erdos917.Deletion
import Mathlib.Combinatorics.SimpleGraph.Subgraph

namespace Erdos917
open SimpleGraph ModuleVertex

/-- The manuscript's convention: chromatic number k, and every proper subgraph
(including subgraphs missing vertices) is (k-1)-colorable. -/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ Q : G.Subgraph,Q ≠ ⊤ → Q.coe.Colorable (k-1)

lemma proper_subgraph_colorable_of_edge_deletions {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hn : ∀ u,∃ v,G.Adj u v)
    (he : ∀ u v,G.Adj u v → (G.deleteEdges {s(u,v)}).Colorable k)
    (Q : G.Subgraph) (hQ : Q ≠ ⊤) : Q.coe.Colorable k := by
  classical
  have hex : ∃ u v,G.Adj u v ∧ ¬ Q.Adj u v := by
    by_contra! h
    apply hQ
    have hv : Q.verts = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro u
      obtain ⟨v,huv⟩ := hn u
      exact Q.edge_vert (h u v huv)
    apply Subgraph.ext hv
    funext u v
    exact propext ⟨Q.adj_sub,h u v⟩
  obtain ⟨u,v,huv,hq⟩ := hex
  obtain ⟨c⟩ := he u v huv
  refine ⟨Coloring.mk (fun x => c x.val) ?_⟩
  intro x y hxy
  apply c.valid
  simp only [deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
  refine ⟨Q.adj_sub hxy,?_⟩
  rintro (⟨hx,hy⟩|⟨hx,hy⟩)
  · apply hq
    simpa only [Subgraph.coe_adj,← hx,← hy] using hxy
  · apply hq
    simpa only [Subgraph.coe_adj,← hx,← hy] using hxy.symm

namespace Assembly
variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable (S : SimpleGraph X) (T : SimpleGraph Y) (Z : SimpleGraph (Part × (X × Y)))

omit [Fintype X] [Fintype Y] in
lemma no_isolated (u : AssemblyVertex X Y) : ∃ v,(assemblyGraph S T Z).Adj u v := by
  rcases u with ⟨i,x|y|p⟩
  · exact ⟨(i,a (x,Classical.arbitrary Y)),Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(i,a (Classical.arbitrary X,y)),Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨(i,s p.1),Or.inl ⟨rfl,rfl⟩⟩

/-- The complete criticality conclusion, quantified over all proper subgraphs. -/
theorem twelve_critical (hS : CriticalData S 10) (hT : CriticalData T 9)
    {D : ℕ} (hz : Scaffold Z D) (hY : 10*D < Fintype.card Y) :
    IsCritical (assemblyGraph S T Z) 12 := by
  classical
  have he := delete_edge_eleven_colorable S T Z hS hT hz
  have hn := no_isolated S T Z
  let u : AssemblyVertex X Y := (0,s (Classical.arbitrary X))
  obtain ⟨v,huv⟩ := hn u
  have hc := colorable_succ_of_delete (assemblyGraph S T Z) u v 11 (he u v huv)
  constructor
  · exact (chromaticNumber_eq_iff_colorable_not_colorable (n := 11)).mpr
      ⟨hc,not_eleven_colorable S T Z hS.not_colorable hT.not_colorable hz hY⟩
  · exact proper_subgraph_colorable_of_edge_deletions (assemblyGraph S T Z) 11 hn he

end Assembly
end Erdos917
