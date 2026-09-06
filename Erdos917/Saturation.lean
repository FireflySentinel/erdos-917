import Erdos917.Deletion
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos917
open Finset SimpleGraph

/-- Common-neighborhood characterization of K5 saturation. This is derived in `SaturationDefinition.lean` from adding
any missing edge and obtaining a K5. -/
structure SaturatedK5 {V : Type*} (H : SimpleGraph V) : Prop where
  free : H.CliqueFree 5
  triangle : ∀ z w,z ≠ w → ¬ H.Adj z w → ∃ t : Fin 3 → V,
    (∀ i j,i ≠ j → H.Adj (t i) (t j)) ∧ ∀ i,H.Adj z (t i) ∧ H.Adj w (t i)

def label {X Y V : Type*} (e : Y ≃ V × Bool) (p : X × Y) : V := (e p.2).1

def blowupGraph {X Y V : Type*} (H : SimpleGraph V) (e : Y ≃ V × Bool) :
    SimpleGraph (Part × (X × Y)) where
  Adj u v := u.1 ≠ v.1 ∧ H.Adj (label e u.2) (label e v.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

namespace Saturation
variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty X]
variable (H : SimpleGraph V) (e : Y ≃ V × Bool)

omit [Fintype X] [Fintype Y] [Fintype V] [Nonempty X] in
lemma no_five (hH : H.CliqueFree 5) (r : Part → X × Y) :
    ¬ (∀ i j,i ≠ j → (blowupGraph H e).Adj (i,r i) (j,r j)) := by
  intro hr
  let c : Copy (completeGraph Part) H := {
    toHom := { toFun := fun i => label e (r i)
               map_rel' := by intro i j hij; exact (hr i j hij).2 }
    injective' := by
      intro i j he
      by_contra hij
      exact H.ne_of_adj (hr i j hij).2 he }
  exact (cliqueFree_iff.mp hH).false c

lemma nonneighbor [DecidableRel H.Adj] {d : ℕ} (hd : ∀ z,H.degree z ≤ d)
    (hsmall : d < Fintype.card V-1) (z : V) : ∃ w,z ≠ w ∧ ¬ H.Adj z w := by
  have hn : ¬ H.IsUniversal z := (H.degree_lt_card_sub_one z).mp (lt_of_le_of_lt (hd z) hsmall)
  by_contra! h
  exact hn (fun w hw => h w hw)

omit [Fintype V] in
lemma triangle_including_equal (hH : SaturatedK5 H) (hn : ∀ z,∃ w,z ≠ w ∧ ¬ H.Adj z w)
    (z w : V) (hzw : ¬ H.Adj z w) : ∃ t : Fin 3 → V,
    (∀ i j,i ≠ j → H.Adj (t i) (t j)) ∧ ∀ i,H.Adj z (t i) ∧ H.Adj w (t i) := by
  by_cases he : z = w
  · subst w
    obtain ⟨w,hne,hnw⟩ := hn z
    obtain ⟨t,ht,hzt⟩ := hH.triangle z w hne hnw
    exact ⟨t,ht,fun i => ⟨(hzt i).1,(hzt i).1⟩⟩
  · exact hH.triangle z w he hzw

omit [Fintype X] [Fintype Y] [Fintype V] in
lemma fill (hH : SaturatedK5 H) (hn : ∀ z,∃ w,z ≠ w ∧ ¬ H.Adj z w)
    (i j : Part) (hij : i ≠ j) (p q : X × Y)
    (hpq : ¬ (blowupGraph H e).Adj (i,p) (j,q)) :
    ∃ r : Part → X × Y,r i = p ∧ r j = q ∧
      ∀ k l,k ≠ l → ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) →
        (blowupGraph H e).Adj (k,r k) (l,r l) := by
  classical
  obtain ⟨t,ht,hpt⟩ := triangle_including_equal H hH hn (label e p) (label e q)
    (fun h => hpq ⟨hij,h⟩)
  let R : Finset Part := univ \ {i,j}
  have hR : R.card = 3 := by simp [R,card_sdiff_of_subset (subset_univ _),hij,Part]
  let idx : R ≃ Fin 3 := R.equivFinOfCardEq hR
  let lift : V → X × Y := fun z => (Classical.arbitrary X,e.symm (z,false))
  have hlift (z : V) : label e (lift z) = z := by simp [lift,label]
  let r : Part → X × Y := fun k => if hk : k = i then p else if hj : k = j then q
    else lift (t (idx ⟨k,by simp [R,hk,hj]⟩))
  have hri : r i = p := by simp [r]
  have hrj : r j = q := by simp [r,hij.symm]
  have hrk (k : Part) (hk : k ≠ i) (hj : k ≠ j) :
      label e (r k) = t (idx ⟨k,by simp [R,hk,hj]⟩) := by simp [r,hk,hj,hlift]
  refine ⟨r,hri,hrj,?_⟩
  intro k l hkl hpair
  refine ⟨hkl,?_⟩
  by_cases hki : k = i
  · subst k
    have hli : l ≠ i := hkl.symm
    have hlj : l ≠ j := fun h => hpair (Or.inl ⟨rfl,h⟩)
    rw [hri,hrk l hli hlj]
    exact (hpt _).1
  by_cases hkj : k = j
  · subst k
    have hlj : l ≠ j := hkl.symm
    have hli : l ≠ i := fun h => hpair (Or.inr ⟨rfl,h⟩)
    rw [hrj,hrk l hli hlj]
    exact (hpt _).2
  by_cases hli : l = i
  · subst l
    rw [hri,hrk k hki hkj]
    exact (hpt _).1.symm
  by_cases hlj : l = j
  · subst l
    rw [hrj,hrk k hki hkj]
    exact (hpt _).2.symm
  rw [hrk k hki hkj,hrk l hli hlj]
  apply ht
  intro he
  exact hkl (congrArg Subtype.val (idx.injective he))

omit [Fintype Y] [Nonempty X] in
lemma degree_bound [DecidableRel H.Adj] {d : ℕ} (hd : ∀ z,H.degree z ≤ d)
    (i j : Part) (_hij : i ≠ j) (q : X × Y) :
    Nat.card {p : X × Y // (blowupGraph H e).Adj (i,p) (j,q)} ≤ 8 * Fintype.card X * d := by
  classical
  let f : {p : X × Y // (blowupGraph H e).Adj (i,p) (j,q)} →
      X × (H.neighborSet (label e q) × Bool) :=
    fun p => (p.val.1,(⟨label e p.val,p.property.2.symm⟩,(e p.val.2).2))
  have hf : Function.Injective f := by
    intro p r he
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.1) he
    · apply e.injective
      apply Prod.ext
      · exact congrArg (fun z => z.2.1.val) he
      · exact congrArg (fun z => z.2.2) he
  have hc := Nat.card_le_card_of_injective f hf
  have heq : Nat.card (X × (H.neighborSet (label e q) × Bool)) =
      Fintype.card X * (H.degree (label e q) * 2) := by
    simp [Nat.card_eq_fintype_card,H.card_neighborSet_eq_degree]
  rw [heq] at hc
  calc
    _ ≤ Fintype.card X * (H.degree (label e q) * 2) := hc
    _ ≤ Fintype.card X * (d * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hd _))
    _ ≤ 8 * Fintype.card X * d := by nlinarith

/-- All scaffold properties follow from the supplied saturated graph, including equal-label edges. -/
theorem scaffold [DecidableRel H.Adj] [Nonempty V] (hH : SaturatedK5 H)
    {d : ℕ} (hd : ∀ z,H.degree z ≤ d) (hsmall : d < Fintype.card V-1) :
    Scaffold (blowupGraph (X := X) H e) (8 * Fintype.card X * d) := by
  classical
  have hn := nonneighbor H hd hsmall
  refine ⟨degree_bound H e hd,no_five H e hH.free,fill H e hH hn,?_⟩
  intro i
  obtain ⟨j,hj⟩ : ∃ j : Part,j ≠ i := exists_ne i
  let p : X × Y := (Classical.arbitrary X,e.symm (Classical.arbitrary V,false))
  obtain ⟨r,_,_,hr⟩ := fill H e hH hn i j hj.symm p p (by
    intro h; exact H.ne_of_adj h.2 rfl)
  refine ⟨r,?_⟩
  intro k l hki hli hkl
  exact hr k l hkl (by aesop)

end Saturation
end Erdos917
