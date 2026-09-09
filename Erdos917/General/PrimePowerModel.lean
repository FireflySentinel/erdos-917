import Erdos917.General.FiniteModel
import Erdos917.General.TriangleModel

namespace Erdos917.General
open SimpleGraph Erdos917.Geometry

def baseOrder (n q : ℕ) : ℕ := (n+1)*(n+2)*(q^2+q)+q^2
def baseBound (n q : ℕ) : ℕ := 2*(n+3)^2*q

def baseDegree (n q : ℕ) : ℕ :=
  if n = 0 then 2*(q+1) else q*((n+1)*(2*n+3)+1)-(n+1)

/-- The saturated-graph construction for clique order `n + 3`, with exact maximum degree. -/
theorem exists_prime_power_exact_model (n p e : ℕ) [Fact p.Prime] (he : e ≠ 0)
    (hq : 2*(n+3) ≤ p^e) :
    ∃ G : SimpleGraph (Fin (baseOrder n (p^e))), Saturated n G ∧
      (∀ z, Nat.card (G.neighborSet z) ≤ baseDegree n (p^e)) ∧
      ∃ z, Nat.card (G.neighborSet z) = baseDegree n (p^e) := by
  classical
  let q := p^e
  let : NeZero q := ⟨by dsimp [q]; omega⟩
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = q := by rw [← Nat.card_eq_fintype_card,GaloisField.card p e he]
  let P := Plane.ofField F hc
  cases n with
  | zero =>
    have ho : baseOrder 0 q = 3*q^2+2*q := by dsimp [baseOrder]; ring
    change ∃ G : SimpleGraph (Fin (baseOrder 0 q)), _
    rw [ho]
    exact exists_triangle_model P (ofField_hasTwoPoints F hc) (by dsimp [q]; omega)
  | succ r =>
    have ho : baseOrder (r+1) q = (r+2)*(r+3)*(q^2+q)+q^2 := rfl
    change ∃ G : SimpleGraph (Fin (baseOrder (r+1) q)), _
    rw [ho]
    have hb : baseDegree (r+1) (p^e) = q*((r+2)*(2*r+5)+1)-(r+2) := by
      simp only [baseDegree,show r+1 ≠ 0 by omega,if_false]
      dsimp [q]
      congr 1
    rw [hb]
    exact exists_finite_model r P (by dsimp [q]; omega)


/-- A uniform linear degree bound convenient for the parameter limits. -/
theorem exists_prime_power_model (n p e : ℕ) [Fact p.Prime] (he : e ≠ 0)
    (hq : 2*(n+3) ≤ p^e) :
    ∃ G : SimpleGraph (Fin (baseOrder n (p^e))), Saturated n G ∧
      ∀ z, Nat.card (G.neighborSet z) ≤ baseBound n (p^e) := by
  obtain ⟨G,hs,hd,_⟩ := exists_prime_power_exact_model n p e he hq
  refine ⟨G,hs,fun z => (hd z).trans ?_⟩
  cases n with
  | zero => simp [baseDegree,baseBound]; omega
  | succ r =>
    simp only [baseDegree,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    calc
      _ ≤ p^e*((r+1+1)*(2*(r+1)+3)+1) := Nat.sub_le _ _
      _ ≤ p^e*(2*(r+4)^2) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = baseBound (r+1) (p^e) := by dsimp [baseBound]; ring

end Erdos917.General
