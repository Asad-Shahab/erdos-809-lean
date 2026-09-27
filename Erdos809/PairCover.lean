import Erdos809.Patterns
import Erdos809.PairCounting

/-! Extract the actual pair amounts of an exact cover by singleton and pair
patterns. Empty patterns are permitted and only increase the cover cost. -/

namespace Erdos809.ExactPatternCover

open Finset
open scoped BigOperators

variable {E P : Type*} [Fintype E] [Fintype P] [DecidableEq E]
variable {capacity : E → ℝ} {edges : P → Finset E}
variable (cover : ExactPatternCover capacity edges)

noncomputable def pairAmount (e f : E) : ℝ :=
  ∑ p, if e ∈ edges p ∧ f ∈ edges p ∧ e ≠ f then cover.amount p else 0

theorem pairAmount_nonneg (e f : E) : 0 ≤ cover.pairAmount e f := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact cover.nonneg p
  · exact le_refl _

theorem pairAmount_symmetric (e f : E) : cover.pairAmount e f = cover.pairAmount f e := by
  unfold pairAmount
  apply sum_congr rfl
  intro p _
  have h : (e ∈ edges p ∧ f ∈ edges p ∧ e ≠ f) ↔
      (f ∈ edges p ∧ e ∈ edges p ∧ f ≠ e) := by
    simp only [ne_comm, and_left_comm]
  simp only [h]

@[simp] theorem pairAmount_diagonal (e : E) : cover.pairAmount e e = 0 := by
  simp [pairAmount]

theorem pairAmount_support {e f : E} (hpos : 0 < cover.pairAmount e f) :
    ∃ p, e ∈ edges p ∧ f ∈ edges p ∧ e ≠ f := by
  classical
  by_contra h
  simp only [not_exists] at h
  have hz : cover.pairAmount e f = 0 := by
    unfold pairAmount
    exact sum_eq_zero fun p _ => if_neg (h p)
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

private theorem pair_row_count (s : Finset E) (a : ℝ) (e : E) :
    (∑ f : E, if e ∈ s ∧ f ∈ s ∧ e ≠ f then a else 0) =
      if e ∈ s then ((s.card - 1 : ℕ) : ℝ) * a else 0 := by
  by_cases he : e ∈ s
  · have h : ∀ f : E, (e ∈ s ∧ f ∈ s ∧ e ≠ f) ↔ f ∈ s.erase e := by
      intro f
      simp [he, mem_erase, and_comm, eq_comm]
    simp_rw [h]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const,
      card_erase_of_mem he, nsmul_eq_mul]
    simp only [he, if_true]
  · simp [he]

theorem pairAmount_row (e : E) :
    (∑ f, cover.pairAmount e f) =
      ∑ p, if e ∈ edges p then (((edges p).card - 1 : ℕ) : ℝ) * cover.amount p else 0 := by
  simp only [pairAmount]
  rw [sum_comm]
  exact sum_congr rfl fun p _ => pair_row_count (edges p) (cover.amount p) e

theorem pairAmount_capacity (hcard : ∀ p, (edges p).card ≤ 2) (e : E) :
    (∑ f, cover.pairAmount e f) ≤ capacity e := by
  rw [cover.pairAmount_row, ← cover.covers e]
  apply sum_le_sum
  intro p _
  by_cases he : e ∈ edges p
  · simp only [he, if_true]
    have hn : (edges p).card - 1 ≤ 1 := by have := hcard p; omega
    have hr : ((((edges p).card - 1 : ℕ) : ℝ)) ≤ 1 := by exact_mod_cast hn
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (cover.nonneg p)
  · simp only [he, if_false, le_refl]

theorem total_capacity : (∑ e, capacity e) =
    ∑ p, ((edges p).card : ℝ) * cover.amount p := by
  calc
    _ = ∑ e, ∑ p, if e ∈ edges p then cover.amount p else 0 := by
      exact sum_congr rfl fun e _ => (cover.covers e).symm
    _ = ∑ p, ∑ e, if e ∈ edges p then cover.amount p else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p _
      rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]

theorem pairAmount_total : (∑ e, ∑ f, cover.pairAmount e f) =
    ∑ p, ((edges p).card : ℝ) * (((edges p).card - 1 : ℕ) : ℝ) * cover.amount p := by
  unfold pairAmount
  calc
    _ = ∑ e, ∑ p, ∑ f, if e ∈ edges p ∧ f ∈ edges p ∧ e ≠ f then cover.amount p else 0 :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ p, ∑ e, ∑ f, if e ∈ edges p ∧ f ∈ edges p ∧ e ≠ f then cover.amount p else 0 :=
      sum_comm
    _ = _ := sum_congr rfl fun p _ => pairPattern_double_sum (edges p) (cover.amount p)

/-- Cover cost pays the total capacity minus the value of this one extracted
matching. There is no optimizer or external LP oracle in this statement. -/
theorem pairAmount_cost_bound (hcard : ∀ p, (edges p).card ≤ 2) :
    (∑ e, capacity e) - (∑ e, ∑ f, cover.pairAmount e f) / 2 ≤ cover.cost := by
  have hp (p : P) :
      2 * (((edges p).card : ℝ) * cover.amount p) ≤ 2 * cover.amount p +
        ((edges p).card : ℝ) * (((edges p).card - 1 : ℕ) : ℝ) * cover.amount p := by
    have hn := hcard p
    have hc : (edges p).card = 0 ∨ (edges p).card = 1 ∨ (edges p).card = 2 := by omega
    rcases hc with hc | hc | hc <;> simp [hc] <;> linarith [cover.nonneg p]
  have hsum := sum_le_sum fun p (_ : p ∈ univ) => hp p
  rw [← mul_sum, sum_add_distrib, ← mul_sum, ← cover.total_capacity,
    ← cover.pairAmount_total] at hsum
  change 2 * (∑ e, capacity e) ≤ 2 * cover.cost + _ at hsum
  linarith

end Erdos809.ExactPatternCover
