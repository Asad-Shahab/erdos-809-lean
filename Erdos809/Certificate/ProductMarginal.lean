import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Convert

/-! Marginalization of a finite normalized product law to any injectively
indexed set of coordinates. Local kernel validation checks the supplied proof.
-/

namespace Erdos809.Certificate

theorem product_law_marginal {I J V R : Type*}
    [Fintype I] [Fintype J] [Fintype V] [DecidableEq I] [DecidableEq J]
    [CommSemiring R] (w : I → V → R) (hnorm : ∀ i, ∑ v, w i v = 1)
    (e : J ↪ I) (f : (J → V) → R) :
    (∑ x : I → V, (∏ i, w i (x i)) * f (fun j => x (e j))) =
      ∑ y : J → V, (∏ j, w (e j) (y j)) * f y := by
  classical
  let p : I → Prop := fun i => i ∈ Set.range e
  let g : J ≃ {i // p i} := Equiv.ofInjective e e.injective
  have key : ∀ x : I → V, (∏ i, w i (x i)) =
      (∏ j, w (e j) (x (e j))) * ∏ i : {i // ¬ p i}, w i (x i) := by
    intro x
    rw [← Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))]
    congr 1
    convert (Fintype.prod_equiv g (fun j => w (e j) (x (e j))) (fun i => w i (x i))
      (fun j => rfl)).symm
  simp_rw [key]
  rw [← (Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm.sum_comp, Fintype.sum_prod_type]
  rw [← (Equiv.piCongrLeft' (fun _ => V) g).sum_comp]
  refine Fintype.sum_congr _ _ (fun y => ?_)
  have hz : ∑ z : ({i // ¬ p i} → V), ∏ i : {i // ¬ p i}, w i (z i) = 1 := by
    rw [← Fintype.prod_sum]; simp [hnorm]
  have hs : ∀ (j : J) (z : {i // ¬ p i} → V),
      (Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm
        ((Equiv.piCongrLeft' (fun _ => V) g) y, z) (e j) = y j := by
    intro j z
    have : p (e j) := ⟨j, rfl⟩
    have hg : g.symm ⟨e j, this⟩ = j := g.symm_apply_eq.mpr rfl
    simp [Equiv.piEquivPiSubtypeProd, this, hg]
  have hs' : ∀ (i : {i // ¬ p i}) (z : {i // ¬ p i} → V),
      (Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm
        ((Equiv.piCongrLeft' (fun _ => V) g) y, z) i = z i := by
    intro i z
    simp [Equiv.piEquivPiSubtypeProd, i.2]
  simp_rw [hs, hs', mul_right_comm _ _ (f _), ← Finset.mul_sum, hz, mul_one]

end Erdos809.Certificate
