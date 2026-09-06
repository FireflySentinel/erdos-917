import Erdos917.EdgeCount

namespace Erdos917
open SimpleGraph

/-- The manuscript's edge-deletion convention for criticality. -/
def IsEdgeCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ u v, G.Adj u v → (G.deleteEdges {s(u, v)}).Colorable (k - 1)

/-- Full proper-subgraph criticality is preserved by relabeling vertices. -/
lemma IsCritical.iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {k : ℕ} (hG : IsCritical G k) (e : G ≃g H) : IsCritical H k := by
  refine ⟨(chromaticNumber_congr e).symm.trans hG.1, ?_⟩
  intro Q hQ
  have hpre : Q.comap e.toHom ≠ ⊤ := by
    intro h
    have ht : (⊤ : G.Subgraph).map e.toHom ≤ Q :=
      (Subgraph.map_le_iff_le_comap e.toHom ⊤ Q).mpr (by rw [h])
    exact hQ (top_le_iff.mp (by simpa using ht))
  obtain ⟨c⟩ := hG.2 _ hpre
  refine ⟨Coloring.mk (fun x => c ⟨e.symm x, by simp⟩) ?_⟩
  intro x y hxy
  apply c.valid
  exact ⟨e.symm.map_adj_iff.mpr (Q.adj_sub hxy), by simpa using hxy⟩

lemma IsCritical.edgeCritical {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : IsCritical G k) : IsEdgeCritical G k := by
  refine ⟨hG.1, ?_⟩
  intro u v huv
  let Q := G.toSubgraph (G.deleteEdges {s(u, v)}) (G.deleteEdges_le _)
  have hQ : Q ≠ ⊤ := by
    intro h
    have ha : Q.Adj u v := by rw [h]; exact huv
    simp [Q] at ha
  obtain ⟨c⟩ := hG.2 Q hQ
  exact ⟨Coloring.mk (fun x => c ⟨x, Set.mem_univ x⟩) (fun hxy => c.valid hxy)⟩

/-- Maximum edge count of a twelve-critical graph on `n` vertices, using the
manuscript's edge-deletion definition. The supremum of the empty set is zero. -/
noncomputable def f12 (n : ℕ) : ℕ :=
  sSup (edgeCount '' {G : SimpleGraph (Fin n) | IsEdgeCritical G 12})

lemma edgeCount_le_f12_of_edgeCritical {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : IsEdgeCritical G 12) : edgeCount G ≤ f12 n := by
  apply le_csSup ((Set.toFinite _).image edgeCount).bddAbove
  exact ⟨G, hG, rfl⟩

/-- The finite supremum is attained whenever a twelve-critical graph exists. -/
lemma f12_attained {n : ℕ} (hex : ∃ G : SimpleGraph (Fin n), IsEdgeCritical G 12) :
    ∃ G : SimpleGraph (Fin n), IsEdgeCritical G 12 ∧ edgeCount G = f12 n := by
  have hne : (edgeCount '' {G : SimpleGraph (Fin n) | IsEdgeCritical G 12}).Nonempty := by
    obtain ⟨G, hG⟩ := hex
    exact ⟨edgeCount G, G, hG, rfl⟩
  exact Nat.sSup_mem hne ((Set.toFinite _).image edgeCount).bddAbove

/-- Relabel any finite critical graph onto `Fin n` without changing its edge count. -/
theorem edgeCount_le_f12 {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : IsCritical G 12) : edgeCount G ≤ f12 (Fintype.card V) := by
  let e := Fintype.equivFin V
  let H := G.comap e.symm
  let i : G ≃g H := { e with map_rel_iff' := by simp [H] }
  have hH := edgeCount_le_f12_of_edgeCritical (hG.iso i).edgeCritical
  have he : edgeCount G = edgeCount H := Nat.card_congr i.mapEdgeSet
  exact he.symm ▸ hH

end Erdos917
