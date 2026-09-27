/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Resources
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Finite weighted double-counting and the weighted Mantel inequality. -/

namespace Erdos809.VertexWeights

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] (x : VertexWeights V)

theorem weighted_square_bound (f : V → ℝ) :
    (∑ v, x.weight v * f v) ^ 2 ≤ ∑ v, x.weight v * f v ^ 2 := by
  let μ := ∑ v, x.weight v * f v
  have hvar : 0 ≤ ∑ v, x.weight v * (f v - μ)^2 :=
    sum_nonneg fun v _ => mul_nonneg (x.nonneg v) (sq_nonneg _)
  have hid : (∑ v, x.weight v * (f v - μ)^2) =
      (∑ v, x.weight v * f v^2) - μ^2 := by
    calc
      _ = ∑ v, (x.weight v * f v^2 - 2*μ*(x.weight v*f v) + μ^2*x.weight v) := by
        apply sum_congr rfl
        intro v _
        ring
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, x.total]
        change (∑ v, x.weight v * f v^2) - 2*μ*μ + μ^2*1 = _
        ring
  rw [hid] at hvar
  exact sub_nonneg.mp hvar

variable (G : SimpleGraph V)

open Classical in
theorem degree_eq_sum (u : V) :
    x.degree G u = ∑ v, if G.Adj u v then x.weight v else 0 := by
  classical
  simp [degree, mass, neighbors, sum_filter]

/-- An oriented edge sum. Symmetric edge functions are counted twice. -/
noncomputable def edgeSum (f : V → V → ℝ) : ℝ := by
  classical
  exact ∑ u, ∑ v, if G.Adj u v then x.weight u * x.weight v * f u v else 0

theorem edgeSum_add (f g : V → V → ℝ) :
    x.edgeSum G (fun u v => f u v + g u v) = x.edgeSum G f + x.edgeSum G g := by
  classical
  unfold edgeSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v <;> simp [h, mul_add]

theorem edgeSum_swap (f : V → V → ℝ) :
    x.edgeSum G (fun u v => f v u) = x.edgeSum G f := by
  classical
  unfold edgeSum
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  rw [G.adj_comm v u, mul_comm (x.weight v) (x.weight u)]

theorem edgeSum_left (f : V → ℝ) :
    x.edgeSum G (fun u _ => f u) = ∑ u, x.weight u * x.degree G u * f u := by
  classical
  unfold edgeSum
  apply sum_congr rfl
  intro u _
  rw [x.degree_eq_sum, mul_sum, sum_mul]
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v <;> simp [h]

theorem edgeSum_one : x.edgeSum G (fun _ _ => 1) = 2 * x.edgeMass G := by
  rw [x.edgeSum_left]
  simp only [mul_one, edgeMass]
  ring

theorem edgeSum_mono {f g : V → V → ℝ}
    (h : ∀ u v, G.Adj u v → f u v ≤ g u v) : x.edgeSum G f ≤ x.edgeSum G g := by
  classical
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro v _
  by_cases huv : G.Adj u v
  · simp only [huv, if_true]
    exact mul_le_mul_of_nonneg_left (h u v huv) (mul_nonneg (x.nonneg u) (x.nonneg v))
  · simp [huv]

theorem degree_square_lower :
    4 * x.edgeMass G ^ 2 ≤ ∑ v, x.weight v * x.degree G v ^ 2 := by
  have := x.weighted_square_bound (x.degree G)
  dsimp [edgeMass]
  nlinarith

/-- Weighted Mantel, derived directly by degree double-counting and variance.
No graph blow-up, rational approximation, or external extremal theorem is used. -/
theorem mantel (hfree : ∀ u v, G.Adj u v → ¬ Walk2 G u v) : x.edgeMass G ≤ 1 / 4 := by
  have hdeg : ∀ u v, G.Adj u v → x.degree G u + x.degree G v ≤ 1 := by
    intro u v huv
    exact x.mass_add_le_one ((disjoint_neighbors_iff G).mpr (hfree u v huv))
  have hupper := x.edgeSum_mono G hdeg
  rw [x.edgeSum_add, x.edgeSum_one, x.edgeSum_swap G (fun u _ => x.degree G u),
    x.edgeSum_left] at hupper
  have hsq : (∑ u, x.weight u * x.degree G u * x.degree G u) =
      ∑ u, x.weight u * x.degree G u ^ 2 := by
    apply sum_congr rfl
    intro u _
    ring
  rw [hsq] at hupper
  have hnonneg := x.edgeMass_nonneg G
  have hlower := x.degree_square_lower G
  nlinarith

end Erdos809.VertexWeights
