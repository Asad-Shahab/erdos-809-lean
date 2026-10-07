module
public import Erdos809.Certificate.ProductMarginal
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Independence of observables on disjoint coordinate families.
The returned ordinary proof was compared against its exact input statement. -/

namespace Erdos809.Certificate

theorem product_law_disjoint {I J K V R : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype V]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [CommSemiring R] (w : I → V → R) (hnorm : ∀ i, ∑ v, w i v = 1)
    (e : J ↪ I) (d : K ↪ I) (hdisjoint : ∀ j k, e j ≠ d k)
    (f : (J → V) → R) (g : (K → V) → R) :
    (∑ x : I → V, (∏ i, w i (x i)) * f (fun j => x (e j)) *
      g (fun k => x (d k))) =
      (∑ y : J → V, (∏ j, w (e j) (y j)) * f y) *
      (∑ z : K → V, (∏ k, w (d k) (z k)) * g z) := by
  classical
  let s : J ⊕ K ↪ I := ⟨Sum.elim e d, by
    rintro (a | a) (b | b) h
    · simp [e.injective h]
    · exact absurd h (hdisjoint a b)
    · exact absurd h.symm (hdisjoint b a)
    · simp [d.injective h]⟩
  have hs_inl : ∀ j, s (Sum.inl j) = e j := fun _ => rfl
  have hs_inr : ∀ k, s (Sum.inr k) = d k := fun _ => rfl
  have h := product_law_marginal w hnorm s
    (fun y => f (fun j => y (Sum.inl j)) * g (fun k => y (Sum.inr k)))
  have hclean :
      (∑ x : I → V, (∏ i, w i (x i)) *
        (f (fun j => x (e j)) * g (fun k => x (d k)))) =
        ∑ y : J ⊕ K → V, (∏ i, w (s i) (y i)) *
          (f (fun j => y (Sum.inl j)) * g (fun k => y (Sum.inr k))) := h
  simp_rw [mul_assoc]
  rw [hclean, ← (Equiv.sumArrowEquivProdArrow J K V).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Fintype.sum_congr _ _ (fun y => Fintype.sum_congr _ _ (fun z => ?_))
  simp [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow, hs_inl, hs_inr]
  ring

end Erdos809.Certificate
