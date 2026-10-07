module
/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
public import Erdos809.Resources
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Exact fractional covers and prices valid on entire compatible patterns. -/

namespace Erdos809

open Finset VertexWeights
open scoped BigOperators

variable {E P : Type*} [Fintype E] [Fintype P] [DecidableEq E]

/-- An exact cover by the specified entire edge sets. Pattern amounts, rather
than colors nominally available, determine its objective. -/
structure ExactPatternCover (capacity : E → ℝ) (edges : P → Finset E) where
  amount : P → ℝ
  nonneg : ∀ p, 0 ≤ amount p
  covers : ∀ e, (∑ p, if e ∈ edges p then amount p else 0) = capacity e

namespace ExactPatternCover

variable {capacity : E → ℝ} {edges : P → Finset E}
    (cover : ExactPatternCover capacity edges)

def cost : ℝ := ∑ p, cover.amount p

/-- Direct weak duality, proved by finite summation; no LP oracle is used. -/
theorem price_bound (price : E → ℝ) (hprice : ∀ p, (∑ e ∈ edges p, price e) ≤ 1) :
    (∑ e, capacity e * price e) ≤ cover.cost := by
  calc
    _ = ∑ e, (∑ p, if e ∈ edges p then cover.amount p else 0) * price e := by
      simp only [cover.covers]
    _ = ∑ p, cover.amount p * ∑ e ∈ edges p, price e := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [mul_sum]
      simp only [ite_mul, zero_mul, sum_ite_mem_eq]
    _ ≤ ∑ p, cover.amount p * 1 :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hprice p) (cover.nonneg p)
    _ = cover.cost := by simp [cost]

end ExactPatternCover

variable {V : Type*} [Fintype V] (x : VertexWeights V) (G : SimpleGraph V)

open Classical in
/-- Resource prices sum to at most one on a whole finite F pattern. -/
theorem resource_price_on_pattern {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u v : E → V) (s : Finset E)
    (hedge : ∀ e ∈ s, G.Adj (u e) (v e))
    (hF : ∀ e ∈ s, ¬ Walk2 G (u e) (v e))
    (hpattern : (s : Set E).Pairwise (fun e f => Compatible G (u e) (v e) (u f) (v f)))
    (w : V) : (∑ e ∈ s, if Resource G (u e) (v e) w then (1 : ℝ) else 0) ≤ 1 := by
  classical
  have hc : (s.filter (fun e => Resource G (u e) (v e) w)).card ≤ 1 := by
    apply card_le_one.mpr
    intro e he f hf
    obtain ⟨hes, hew⟩ := mem_filter.mp he
    obtain ⟨hfs, hfw⟩ := mem_filter.mp hf
    by_contra hne
    exact compatible_resources_disjoint x G hδ hmin (hpattern hes hfs hne)
      (hedge e hes) (hedge f hfs) (hF f hfs) hew hfw
  have hr : ((s.filter (fun e => Resource G (u e) (v e) w)).card : ℝ) ≤ 1 := by
    exact_mod_cast hc
  simpa [sum_filter] using hr

open Classical in
/-- Every exact nontriangular pattern cover pays each full resource-root price.
The later graph interface identifies this objective with q(w). -/
theorem resource_price_bound {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u v : E → V)
    (hedge : ∀ e, G.Adj (u e) (v e)) (hF : ∀ e, ¬ Walk2 G (u e) (v e))
    (capacity : E → ℝ) (edges : P → Finset E)
    (hpattern : ∀ p, (edges p : Set E).Pairwise
      (fun e f => Compatible G (u e) (v e) (u f) (v f)))
    (cover : ExactPatternCover capacity edges) (w : V) :
    (∑ e, capacity e * if Resource G (u e) (v e) w then (1 : ℝ) else 0) ≤ cover.cost := by
  classical
  apply cover.price_bound
  intro p
  exact resource_price_on_pattern x G hδ hmin u v (edges p)
    (fun e _ => hedge e) (fun e _ => hF e) (hpattern p) w

/-- A vertex lying in no triangle has no triangular neighbor. -/
def TriangleFreeVertex (v : V) : Prop := ∀ w, ¬ Triangular G v w

omit [Fintype V] in
theorem free_edge_resource_empty {u v : V}
    (hu : TriangleFreeVertex G u) (hv : TriangleFreeVertex G v) (w : V) :
    ¬ Resource G u v w := by
  rintro (h | h)
  · exact hu w h
  · exact hv w h

end Erdos809
