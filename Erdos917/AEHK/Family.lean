import Erdos917.AEHK.Saturated
import Erdos917.AEHK.Degrees
import Erdos917.Counterexample

/-! Construction of the infinite AEHK family and unconditional consequences for Problem 917. -/

namespace Erdos917.AEHK
open SimpleGraph Filter Topology

variable {q : ℕ} [NeZero q]

/-- Relabel the geometric construction by the required finite vertex set. -/
theorem exists_finite_model (P : Plane q) (hq : 4 ≤ q) :
    ∃ G : SimpleGraph (Fin (13 * q ^ 2 + 12 * q)), G.CliqueFree 5 ∧
      (∀ x y, x ≠ y → ¬ G.Adj x y → ¬ (G ⊔ edge x y).CliqueFree 5) ∧
      (∀ z, Nat.card (G.neighborSet z) ≤ 22 * q - 3) ∧
      ∃ z, Nat.card (G.neighborSet z) = 22 * q - 3 := by
  classical
  let e : Fin (13 * q ^ 2 + 12 * q) ≃ PlaneVertex P :=
    (Fintype.equivFinOfCardEq (planeVertex_card P)).symm
  let G := planeGraph P
  let H := G.comap e
  let f : H ≃g G := Iso.comap e G
  refine ⟨H, CliqueFree.comap f.isContained (planeGraph_cliqueFree P hq), ?_, ?_, ?_⟩
  · intro x y hxy hn hfree
    have h := planeGraph_saturated P hq (e x) (e y) (e.injective.ne hxy) hn
    apply h
    let f' : (H ⊔ edge x y) ≃g (G ⊔ edge (e x) (e y)) := {
      __ := e
      map_rel_iff' := by
        intro a b
        simp [H, edge_adj, e.injective.eq_iff] }
    exact CliqueFree.comap f'.symm.isContained hfree
  · intro z
    calc
      Nat.card (H.neighborSet z) = Nat.card (G.neighborSet (e z)) := Nat.card_congr (f.mapNeighborSet z)
      _ = G.degree (e z) := by rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
      _ ≤ 22 * q - 3 := planeGraph_degree_le P hq (e z)

  · let x : CoreVertex q := ⟨0,0,0,0⟩
    refine ⟨e.symm (.inl x), ?_⟩
    rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree, ← f.degree_eq]
    change G.degree (e (e.symm (.inl x))) = _
    rw [e.apply_symm_apply]
    exact core_degree P hq x

/-- Lemma 5 for every prime power at least four; the degree bound is attained. -/
theorem exists_prime_power_model (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (hq : 4 ≤ p ^ n) :
    ∃ G : SimpleGraph (Fin (13 * (p ^ n) ^ 2 + 12 * p ^ n)), G.CliqueFree 5 ∧
      (∀ x y, x ≠ y → ¬ G.Adj x y → ¬ (G ⊔ edge x y).CliqueFree 5) ∧
      (∀ z, Nat.card (G.neighborSet z) ≤ 22 * p ^ n - 3) ∧
      ∃ z, Nat.card (G.neighborSet z) = 22 * p ^ n - 3 := by
  classical
  let : NeZero (p ^ n) := ⟨by omega⟩
  let F := GaloisField p n
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p ^ n := by rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn]
  exact exists_finite_model (Plane.ofField F hc) hq

/-- The family used in the manuscript, constructed over fields of order `3^(2(s+4))`. -/
noncomputable def canonicalFamily : Family := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hs (s : ℕ) : ∃ G : SimpleGraph (Fin (v s)), G.CliqueFree 5 ∧
      (∀ x y, x ≠ y → ¬ G.Adj x y → ¬ (G ⊔ edge x y).CliqueFree 5) ∧
      ∀ z, Nat.card (G.neighborSet z) ≤ d s := by
    let q := h s ^ 2
    have hq : 4 ≤ q := by have hh := h_lower s; dsimp [q]; nlinarith
    have he : 3 ^ (2 * (s + 4)) = q := by
      dsimp [q, h]
      rw [Nat.mul_comm 2 (s + 4), pow_mul]
    have hmodel := exists_prime_power_model 3 (2 * (s + 4)) (by omega) (by simpa [he] using hq)
    rw [he] at hmodel
    have hv : 13 * q ^ 2 + 12 * q = v s := by dsimp [q, v]; ring
    rw [← hv]
    obtain ⟨G,hfree,hsat,hdeg,_⟩ := hmodel
    exact ⟨G,hfree,hsat,hdeg⟩
  choose G hfree hsat hdeg using hs
  exact ⟨G, hfree, hsat, hdeg⟩

theorem canonical_counterexample_critical (s : ℕ) :
    IsCritical (counterexample canonicalFamily s) 12 := counterexample_critical canonicalFamily s

theorem canonical_counterexample_density :
    Tendsto (fun s => (edgeCount (counterexample canonicalFamily s) : ℝ) /
      (Fintype.card (Vertex s) : ℝ) ^ 2) atTop (𝓝 (2 / 5 : ℝ)) := counterexample_density canonicalFamily

end Erdos917.AEHK

namespace Erdos917
open Filter Topology

/-- The asymptotic formula proposed in Problem 917 is false at `k = 12`. -/
theorem not_density_three_eighths :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (3 / 8 : ℝ)) :=
  AEHK.not_density_three_eighths AEHK.canonicalFamily

theorem f12_not_density_below_two_fifths {c : ℝ} (hc : c < 2 / 5) :
    ¬ Tendsto (fun n : ℕ => (f12 n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 c) :=
  AEHK.f12_not_density_below_two_fifths AEHK.canonicalFamily hc

end Erdos917
