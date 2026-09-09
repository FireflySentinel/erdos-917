import Erdos917.General.Family

namespace Erdos917.General
open SimpleGraph ModuleVertex Filter Topology

lemma criticalData_of_deletions {V : Type*} [Nonempty V] (G : SimpleGraph V) (k : ℕ)
    (hn : ∀ u, ∃ v, G.Adj u v) (hnot : ¬ G.Colorable k)
    (he : ∀ u v, G.Adj u v → (G.deleteEdges {s(u,v)}).Colorable k) : CriticalData G k := by
  classical
  let u := Classical.arbitrary V
  obtain ⟨v,huv⟩ := hn u
  refine ⟨colorable_succ_of_delete G u v k (he u v huv),hnot,he,?_⟩
  intro x
  obtain ⟨y,hxy⟩ := hn x
  obtain ⟨c⟩ := he x y hxy
  refine ⟨Coloring.mk (fun z => c z.val) ?_⟩
  intro a b hab
  apply c.valid
  rw [deleteEdges_adj]
  refine ⟨hab,?_⟩
  intro heq
  rcases Sym2.eq_iff.mp heq with ⟨ha,_⟩|⟨_,hb⟩
  · exact a.2 ha
  · exact b.2 hb

lemma graph_criticalData (n s : ℕ) : CriticalData (graph n s) (2*n+7) := by
  classical
  have hs := baseGraph_saturated n s
  have hcrit := graph_critical n s
  apply criticalData_of_deletions _ _
  · exact Assembly.no_isolated _ _ _
  · exact ((chromaticNumber_eq_iff_colorable_not_colorable (n := 2*n+7)).mp hcrit.1).2
  · exact conversion_delete_edge_colorable (baseGraph n s) (h n s) (d n s)
      (by simpa using v_lower n s) (h_large n s) (h_odd n s)
      hs.free hs.add_edges (baseGraph_degree n s) (by simpa using degree_small n s)

lemma cone_isCritical {V : Type*} [Nonempty V] (G : SimpleGraph V) {k : ℕ}
    (hG : CriticalData G k) : IsCritical (cone G) (k+2) := by
  classical
  have hc := cone_critical G hG
  have hn : ∀ u, ∃ v, (cone G).Adj u v := by
    rintro (u|u)
    · exact ⟨some (Classical.arbitrary V),trivial⟩
    · exact ⟨none,trivial⟩
  refine ⟨(chromaticNumber_eq_iff_colorable_not_colorable (n := k+1)).mpr
    ⟨hc.colorable,hc.not_colorable⟩,?_⟩
  exact proper_subgraph_colorable_of_edge_deletions _ _ hn hc.delete_edge

lemma cone_graph_critical (n s : ℕ) : IsCritical (cone (graph n s)) (2*n+9) :=
  cone_isCritical _ (graph_criticalData n s)

lemma cone_density {V : ℕ → Type} [∀ s, Fintype (V s)] (G : ∀ s, SimpleGraph (V s))
    {c : ℝ} (hN : Tendsto (fun s => Fintype.card (V s)) atTop atTop)
    (hG : Tendsto (fun s => (edgeCount (G s) : ℝ)/(Fintype.card (V s) : ℝ)^2) atTop (𝓝 c)) :
    Tendsto (fun s => (edgeCount (cone (G s)) : ℝ)/(Fintype.card (Option (V s)) : ℝ)^2)
      atTop (𝓝 c) := by
  have hinv : Tendsto (fun s => ((Fintype.card (V s) : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hlim := (hG.add hinv).div (((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow 2) (by norm_num)
  simp only [add_zero,one_pow,div_one] at hlim
  apply hlim.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0)] with s hs
  dsimp only [Pi.div_apply,Pi.add_apply]
  rw [cone_edgeCount,Fintype.card_option]
  push_cast
  have hn : (Fintype.card (V s) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  field_simp

lemma cone_graph_density (n : ℕ) :
    Tendsto (fun s => (edgeCount (cone (graph n s)) : ℝ)/(Fintype.card (Option (Vertex n s)) : ℝ)^2)
      atTop (𝓝 ((n+2)/(2*(n+3)) : ℝ)) :=
  cone_density (graph n) (graph_order_tendsto n) (graph_density n)

end Erdos917.General
