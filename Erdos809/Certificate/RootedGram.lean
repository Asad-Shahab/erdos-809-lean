import Erdos809.Certificate.ProductDisjoint
import Erdos809.Certificate.GramForms
import Erdos809.Certificate.Sampling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Actual one-root flag Gram positivity under the hierarchical vertex-and-mark
sampling law. The target statement and supplied dependencies were compared
against the isolated Aristotle input before this proof was transplanted. -/

namespace Erdos809.Certificate

theorem rooted_flag_gram_nonnegative {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (κ : V → V → Fin 4 → ℝ) (hκ : ∀ u v c, 0 ≤ κ u v c)
    (hκtotal : ∀ u v, ∑ c, κ u v c = 1)
    (Q : Matrix I I ℝ) (hQ : Q.PosSemidef)
    (flag : Fin 4 → Fin 4 → Fin 4 → I) :
    0 ≤ ∑ v : Fin 5 → V, (∏ i, w (v i)) *
      ∑ c : PairPosition 5 → Fin 4,
        (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (c e)) *
        Q (flag (c ⟨(0, 1), by decide⟩) (c ⟨(0, 2), by decide⟩)
            (c ⟨(1, 2), by decide⟩))
          (flag (c ⟨(0, 3), by decide⟩) (c ⟨(0, 4), by decide⟩)
            (c ⟨(3, 4), by decide⟩)) := by
  classical
  let A : V → V → V → I → ℝ := fun a b c i =>
    ∑ y : Fin 3 → Fin 4, κ a b (y 0) * κ a c (y 1) * κ b c (y 2) *
      (if flag (y 0) (y 1) (y 2) = i then 1 else 0)
  let e1 : Fin 3 ↪ PairPosition 5 :=
    ⟨![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩], by decide⟩
  let e2 : Fin 3 ↪ PairPosition 5 :=
    ⟨![⟨(0, 3), by decide⟩, ⟨(0, 4), by decide⟩, ⟨(3, 4), by decide⟩], by decide⟩
  have hinner : ∀ v : Fin 5 → V, (∑ c : PairPosition 5 → Fin 4,
        (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (c e)) *
        Q (flag (c ⟨(0, 1), by decide⟩) (c ⟨(0, 2), by decide⟩)
            (c ⟨(1, 2), by decide⟩))
          (flag (c ⟨(0, 3), by decide⟩) (c ⟨(0, 4), by decide⟩)
            (c ⟨(3, 4), by decide⟩))) =
      ∑ i, ∑ j, Q i j * (A (v 0) (v 1) (v 2) i * A (v 0) (v 3) (v 4) j) := by
    intro v
    have hQ' : ∀ a b : I, Q a b = ∑ i, ∑ j,
        Q i j * ((if a = i then 1 else 0) * (if b = j then 1 else 0)) := by
      intro a b; simp
    simp_rw [hQ' (flag _ _ _), Finset.mul_sum]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
    have := product_law_disjoint (fun e c => κ (v e.1.1) (v e.1.2) c) (fun e => hκtotal _ _)
      e1 e2 (by decide) (fun y => if flag (y 0) (y 1) (y 2) = i then (1:ℝ) else 0)
      (fun y => if flag (y 0) (y 1) (y 2) = j then (1:ℝ) else 0)
    have h3 : (∑ x : PairPosition 5 → Fin 4, (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (x e)) *
        (if flag (x ⟨(0, 1), by decide⟩) (x ⟨(0, 2), by decide⟩) (x ⟨(1, 2), by decide⟩) = i
          then (1:ℝ) else 0) *
        (if flag (x ⟨(0, 3), by decide⟩) (x ⟨(0, 4), by decide⟩) (x ⟨(3, 4), by decide⟩) = j
          then (1:ℝ) else 0)) = A (v 0) (v 1) (v 2) i * A (v 0) (v 3) (v 4) j := by
      refine this.trans ?_; simp only [A, Fin.prod_univ_three]; rfl
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl fun v _ => by rw [hinner v]]
  let x : V → I → ℝ := fun a i => ∑ b, ∑ c, w b * w c * A a b c i
  have key : ∀ a, (∑ b, ∑ c, ∑ d, ∑ e, (w a * w b * w c * w d * w e) *
      ∑ i, ∑ j, Q i j * (A a b c i * A a d e j)) =
      w a * dotProduct (star (x a)) (Q.mulVec (x a)) := by
    intro a
    simp only [x, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, Finset.sum_mul,
      ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv
      { toFun := fun x => (x.2.2.2.2.1, (x.2.2.2.2.2, x.2.2.1, x.2.2.2.1), x.1, x.2.1)
        invFun := fun y => (y.2.2.1, y.2.2.2, y.2.1.2.1, y.2.1.2.2, y.1, y.2.1.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ (fun _ => by simp only [Equiv.coe_fn_mk]; ring)
  let E : V × V × V × V × V ≃ (Fin 5 → V) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
      invFun := fun v => (v 0, v 1, v 2, v 3, v 4)
      left_inv := fun _ => rfl
      right_inv := fun v => by funext k; fin_cases k <;> rfl }
  rw [← E.sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun a _ => ?_
  refine le_of_le_of_eq (mul_nonneg (hw a) (hQ.dotProduct_mulVec_nonneg (x a))) ?_
  rw [← key a]
  simp only [Fin.prod_univ_five]
  rfl

end Erdos809.Certificate
