module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Erdos809
open Finset
open scoped BigOperators

/-- Count ordered distinct members of one pattern. This identity is used to
extract a fractional matching from triangular patterns of size at most two. -/
theorem pairPattern_double_sum {E : Type*} [Fintype E] [DecidableEq E]
    (s : Finset E) (a : ℝ) :
    (∑ e : E, ∑ f : E, if e ∈ s ∧ f ∈ s ∧ e ≠ f then a else 0) =
      (s.card : ℝ) * ((s.card - 1 : ℕ) : ℝ) * a := by
  have h : ∀ e : E, (∑ f : E, if e ∈ s ∧ f ∈ s ∧ e ≠ f then a else 0) =
      if e ∈ s then ((s.card - 1 : ℕ) : ℝ) * a else 0 := by
    intro e
    split_ifs with he
    · have : ∀ f : E, (e ∈ s ∧ f ∈ s ∧ e ≠ f) ↔ f ∈ s.erase e := by
        intro f; simp [he, Finset.mem_erase, and_comm, eq_comm]
      simp_rw [this]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        Finset.card_erase_of_mem he, nsmul_eq_mul]
    · simp [he]
  simp_rw [h]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, mul_assoc]

end Erdos809
