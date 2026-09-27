/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Triangular
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! One actual capacitated fractional matching, with a symmetric ordered-pair
matrix. Each unordered pair is counted twice by this representation. -/

namespace Erdos809

open Finset VertexWeights
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

/-- Endpoint incidences count positions, so shared endpoints retain multiplicity. -/
noncomputable def rootIncidence (w u v : V) : ℝ := by
  classical
  exact (if G.Adj w u then 1 else 0) + (if G.Adj w v then 1 else 0)

theorem compatible_root_incidence_le_two {u v a b w : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : G.Adj a b) :
    rootIncidence G w u v + rootIncidence G w a b ≤ 2 := by
  classical
  have h₁ : ¬ (G.Adj w u ∧ G.Adj w a ∧ G.Adj w b) := by
    rintro ⟨hu, ha, hb⟩
    exact h.partial_row G huv ⟨⟨w, hu.symm, ha⟩, ⟨w, hu.symm, hb⟩⟩
  have h₂ : ¬ (G.Adj w v ∧ G.Adj w a ∧ G.Adj w b) := by
    rintro ⟨hv, ha, hb⟩
    exact (h.flip_left G).partial_row G huv.symm ⟨⟨w, hv.symm, ha⟩, ⟨w, hv.symm, hb⟩⟩
  have h₃ : ¬ (G.Adj w a ∧ G.Adj w u ∧ G.Adj w v) := by
    rintro ⟨ha, hu, hv⟩
    exact (h.symm G).partial_row G hab ⟨⟨w, ha.symm, hu⟩, ⟨w, ha.symm, hv⟩⟩
  have h₄ : ¬ (G.Adj w b ∧ G.Adj w u ∧ G.Adj w v) := by
    rintro ⟨hb, hu, hv⟩
    exact ((h.symm G).flip_left G).partial_row G hab.symm
      ⟨⟨w, hb.symm, hu⟩, ⟨w, hb.symm, hv⟩⟩
  by_cases hu : G.Adj w u <;> by_cases hv : G.Adj w v <;>
    by_cases ha : G.Adj w a <;> by_cases hb : G.Adj w b <;>
    norm_num [rootIncidence, hu, hv, ha, hb] at *

variable [Fintype V] (x : VertexWeights V)

/-- A matching on a chosen finite family of actual triangular host edges.
The capacity and support conditions are explicit; no optimality is assumed.
Consequently every theorem applies to the same optimal matching when chosen. -/
structure TriangularMatching (E : Type*) [Fintype E] where
  left : E → V
  right : E → V
  triangular : ∀ e, Triangular G (left e) (right e)
  amount : E → E → ℝ
  nonneg : ∀ e f, 0 ≤ amount e f
  symmetric : ∀ e f, amount e f = amount f e
  diagonal : ∀ e, amount e e = 0
  compatible : ∀ e f, 0 < amount e f → Compatible G (left e) (right e) (left f) (right f)
  capacity : ∀ e, (∑ f, amount e f) ≤ x.capacity (left e) (right e)

namespace TriangularMatching

variable {G x} {E : Type*} [Fintype E] (y : TriangularMatching G x E)

def usage (e : E) : ℝ := ∑ f, y.amount e f

def mass : ℝ := ∑ e, y.usage e

noncomputable def value : ℝ := y.mass / 2

theorem mass_eq_twice_value : y.mass = 2 * y.value := by unfold value; ring

theorem usage_nonneg (e : E) : 0 ≤ y.usage e := sum_nonneg fun f _ => y.nonneg e f

theorem usage_le_capacity (e : E) : y.usage e ≤ x.capacity (y.left e) (y.right e) := y.capacity e

theorem exists_mate_of_usage_pos {e : E} (he : 0 < y.usage e) :
    ∃ f, 0 < y.amount e f := by
  by_contra h
  push Not at h
  have hsum : y.usage e ≤ 0 := sum_nonpos fun f _ => h f
  exact (not_le_of_gt he) hsum

/-- Every positively used triangular edge has the geometric union bound. -/
theorem used_union_bound [DecidableEq V] {δ : ℝ}
    (hmin : x.MinDegreeAtLeast G δ) {e : E} (he : 0 < y.usage e) :
    x.mass (neighbors G (y.left e) ∪ neighbors G (y.right e)) ≤ 1 - δ := by
  obtain ⟨f, hf⟩ := y.exists_mate_of_usage_pos he
  exact x.compatible_triangular_union_bound G hmin (y.compatible e f hf)
    (y.triangular e).1 (y.triangular f)

noncomputable def rootLoad (w : V) : ℝ :=
  ∑ e, y.usage e * rootIncidence G w (y.left e) (y.right e)

/-- The root budget for one fixed matching, before rewriting into vertex k(v).
This is the sum of the actual selected endpoint incidences. -/
theorem rootLoad_le_mass (w : V) : y.rootLoad w ≤ y.mass := by
  let inc (e : E) := rootIncidence G w (y.left e) (y.right e)
  have hpair (e f : E) : y.amount e f * (inc e + inc f) ≤ 2 * y.amount e f := by
    by_cases hpos : 0 < y.amount e f
    · have h := compatible_root_incidence_le_two G (y.compatible e f hpos)
        (y.triangular e).1 (y.triangular f).1 (w := w)
      nlinarith [mul_nonneg (y.nonneg e f) (sub_nonneg.mpr h)]
    · have hz : y.amount e f = 0 := le_antisymm (le_of_not_gt hpos) (y.nonneg e f)
      simp [hz]
  have hsum := sum_le_sum (fun e (_ : e ∈ univ) =>
    sum_le_sum (fun f (_ : f ∈ univ) => hpair e f))
  have hleft : (∑ e, ∑ f, y.amount e f * inc e) = y.rootLoad w := by
    simp only [← sum_mul, rootLoad, usage, inc]
  have hright : (∑ e, ∑ f, y.amount e f * inc f) = y.rootLoad w := by
    rw [sum_comm]
    simpa only [y.symmetric] using hleft
  have hmass : (∑ e, ∑ f, 2 * y.amount e f) = 2 * y.mass := by
    simp only [← mul_sum, mass, usage]
  simp_rw [mul_add, sum_add_distrib] at hsum
  rw [hleft, hright, hmass] at hsum
  linarith

end TriangularMatching
end Erdos809
