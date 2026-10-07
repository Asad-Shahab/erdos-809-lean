module
public import Erdos809.Certificate.ProductDisjoint
public import Erdos809.Certificate.GramForms
public import Erdos809.Certificate.Sampling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Conditional Gram forms with three fixed sampled roots and one fresh
vertex per flag. The pair coordinates are independent even for repeated types.
-/

namespace Erdos809.Certificate

private abbrev TripleMarks := Fin 3 ⊕ (Fin 3 ⊕ Fin 3)

private def typedMarkPair : TripleMarks → PairPosition 5 :=
  Sum.elim ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]
    (Sum.elim ![⟨(0, 3), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(2, 3), by decide⟩]
      ![⟨(0, 4), by decide⟩, ⟨(1, 4), by decide⟩, ⟨(2, 4), by decide⟩])

private def typedMarkEmbedding : TripleMarks ↪ PairPosition 5 :=
  ⟨typedMarkPair, by decide +kernel⟩

private theorem sum_triple_marks (f : (TripleMarks → Fin 4) → ℝ) :
    (∑ z, f z) = ∑ r : Fin 3 → Fin 4, ∑ l : Fin 3 → Fin 4,
      ∑ s : Fin 3 → Fin 4, f (Sum.elim r (Sum.elim l s)) := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin 3 ⊕ Fin 3) (Fin 4)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin 3) (Fin 4)).symm.sum_comp,
    Fintype.sum_prod_type]
  rfl

private theorem triple_event_iff (r : Fin 3 → Fin 4) (a b d : Fin 4) :
    (r 0 = a ∧ r 1 = b ∧ r 2 = d) ↔ r = ![a, b, d] := by
  constructor
  · intro h
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  · rintro rfl
    simp

private def extensionWeight {V : Type*} (κ : V → V → Fin 4 → ℝ)
    (u v w z : V) (c : Fin 3 → Fin 4) : ℝ :=
  κ u z (c 0) * κ v z (c 1) * κ w z (c 2)

private theorem typed_mark_expectation {V I : Type*}
    (κ : V → V → Fin 4 → ℝ) (hκtotal : ∀ u v, ∑ c, κ u v c = 1)
    (Q : Matrix I I ℝ) (flag : Fin 4 → Fin 4 → Fin 4 → I)
    (v : Fin 5 → V) (a b d : Fin 4) :
    (∑ c : PairPosition 5 → Fin 4,
      (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (c e)) *
      (if c ⟨(0, 1), by decide⟩ = a ∧ c ⟨(0, 2), by decide⟩ = b ∧
          c ⟨(1, 2), by decide⟩ = d then
        Q (flag (c ⟨(0, 3), by decide⟩) (c ⟨(1, 3), by decide⟩) (c ⟨(2, 3), by decide⟩))
          (flag (c ⟨(0, 4), by decide⟩) (c ⟨(1, 4), by decide⟩) (c ⟨(2, 4), by decide⟩))
        else 0)) =
      (κ (v 0) (v 1) a * κ (v 0) (v 2) b * κ (v 1) (v 2) d) *
        ∑ l : Fin 3 → Fin 4, ∑ r : Fin 3 → Fin 4,
          extensionWeight κ (v 0) (v 1) (v 2) (v 3) l *
          Q (flag (l 0) (l 1) (l 2)) (flag (r 0) (r 1) (r 2)) *
          extensionWeight κ (v 0) (v 1) (v 2) (v 4) r := by
  classical
  let obs : (TripleMarks → Fin 4) → ℝ := fun z =>
    if z (.inl 0) = a ∧ z (.inl 1) = b ∧ z (.inl 2) = d then
      Q (flag (z (.inr (.inl 0))) (z (.inr (.inl 1))) (z (.inr (.inl 2))))
        (flag (z (.inr (.inr 0))) (z (.inr (.inr 1))) (z (.inr (.inr 2)))) else 0
  have hm := product_law_marginal
    (fun (e : PairPosition 5) c => κ (v e.1.1) (v e.1.2) c)
    (fun e => hκtotal _ _) typedMarkEmbedding obs
  change _ = _ at hm
  rw [show (∑ c : PairPosition 5 → Fin 4,
      (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (c e)) *
      (if c ⟨(0, 1), by decide⟩ = a ∧ c ⟨(0, 2), by decide⟩ = b ∧
          c ⟨(1, 2), by decide⟩ = d then
        Q (flag (c ⟨(0, 3), by decide⟩) (c ⟨(1, 3), by decide⟩) (c ⟨(2, 3), by decide⟩))
          (flag (c ⟨(0, 4), by decide⟩) (c ⟨(1, 4), by decide⟩) (c ⟨(2, 4), by decide⟩))
        else 0)) = ∑ z : TripleMarks → Fin 4,
        (∏ i, κ (v (typedMarkEmbedding i).1.1) (v (typedMarkEmbedding i).1.2) (z i)) *
          obs z from hm]
  rw [sum_triple_marks]
  simp only [obs, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    typedMarkEmbedding, Function.Embedding.coeFn_mk, typedMarkPair]
  simp_rw [triple_event_iff]
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [extensionWeight, Fin.prod_univ_three, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [Matrix.cons_val]
  ring

private theorem sum_vertex_product_succ {V : Type*} [Fintype V]
    (w : V → ℝ) {n : ℕ} (f : (Fin (n + 1) → V) → ℝ) :
    (∑ v, (∏ i, w (v i)) * f v) =
      ∑ a, w a * ∑ v : Fin n → V, (∏ i, w (v i)) * f (Fin.cons a v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => V)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mul_assoc, ← Finset.mul_sum]
  rfl

private theorem sum_vertex_product_zero {V : Type*} [Fintype V]
    (w : V → ℝ) (f : (Fin 0 → V) → ℝ) :
    (∑ v, (∏ i, w (v i)) * f v) = f Fin.elim0 := by
  simp [Finset.univ_unique, Subsingleton.elim (default : Fin 0 → V) Fin.elim0]

theorem typed_flag_gram_nonnegative {V I : Type*} [Fintype V] [Fintype I]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (κ : V → V → Fin 4 → ℝ) (hκ : ∀ u v c, 0 ≤ κ u v c)
    (hκtotal : ∀ u v, ∑ c, κ u v c = 1)
    (Q : Matrix I I ℝ) (hQ : Q.PosSemidef)
    (flag : Fin 4 → Fin 4 → Fin 4 → I) (a b d : Fin 4) :
    0 ≤ ∑ v : Fin 5 → V, (∏ i, w (v i)) *
      ∑ c : PairPosition 5 → Fin 4,
        (∏ e : PairPosition 5, κ (v e.1.1) (v e.1.2) (c e)) *
        (if c ⟨(0, 1), by decide⟩ = a ∧ c ⟨(0, 2), by decide⟩ = b ∧
            c ⟨(1, 2), by decide⟩ = d then
          Q (flag (c ⟨(0, 3), by decide⟩) (c ⟨(1, 3), by decide⟩)
              (c ⟨(2, 3), by decide⟩))
            (flag (c ⟨(0, 4), by decide⟩) (c ⟨(1, 4), by decide⟩)
              (c ⟨(2, 4), by decide⟩)) else 0) := by
  classical
  simp_rw [typed_mark_expectation κ hκtotal Q flag]
  simp only [sum_vertex_product_succ, sum_vertex_product_zero, Fin.cons_zero, Fin.cons_one]
  apply Finset.sum_nonneg
  intro u _
  apply mul_nonneg (hw u)
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (hw z)
  change 0 ≤ ∑ s, w s * ∑ t, w t *
    ((κ u v a * κ u z b * κ v z d) *
      ∑ l : Fin 3 → Fin 4, ∑ r : Fin 3 → Fin 4,
        extensionWeight κ u v z s l * Q (flag (l 0) (l 1) (l 2))
          (flag (r 0) (r 1) (r 2)) * extensionWeight κ u v z t r)
  let μ : V × (Fin 3 → Fin 4) → ℝ := fun s => w s.1 * extensionWeight κ u v z s.1 s.2
  let f : V × (Fin 3 → Fin 4) → I := fun s => flag (s.2 0) (s.2 1) (s.2 2)
  have hgram := flag_gram_nonnegative Q hQ f μ
  have hid : (∑ s, w s * ∑ t, w t *
      ((κ u v a * κ u z b * κ v z d) *
        ∑ l : Fin 3 → Fin 4, ∑ r : Fin 3 → Fin 4,
          extensionWeight κ u v z s l * Q (flag (l 0) (l 1) (l 2))
            (flag (r 0) (r 1) (r 2)) * extensionWeight κ u v z t r)) =
      (κ u v a * κ u z b * κ v z d) *
        ∑ s, ∑ t, μ s * μ t * Q (f s) (f t) := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum, μ, f]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hid]
  exact mul_nonneg (mul_nonneg (mul_nonneg (hκ _ _ _) (hκ _ _ _)) (hκ _ _ _)) hgram

end Erdos809.Certificate
