/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.WeightedIdentities
import Mathlib.Data.Finset.Max

/-! Weighted maximum cuts and the averaged neighborhood-cut inequality. -/

namespace Erdos809.VertexWeights

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] (x : VertexWeights V) (G : SimpleGraph V)

noncomputable def cutWeight (s : Finset V) : ℝ := by
  classical
  exact x.edgeSum G (fun u v => if u ∈ s ∧ v ∉ s then 1 else 0)

noncomputable def maxCut : ℝ := by
  classical
  exact (univ.image (x.cutWeight G)).max' (by simp)

theorem cutWeight_le_maxCut (s : Finset V) : x.cutWeight G s ≤ x.maxCut G := by
  classical
  exact le_max' _ _ (mem_image.mpr ⟨s, mem_univ _, rfl⟩)

theorem cutWeight_nonneg (s : Finset V) : 0 ≤ x.cutWeight G s := by
  classical
  unfold cutWeight edgeSum
  apply sum_nonneg
  intro u _
  apply sum_nonneg
  intro v _
  have hu := x.nonneg u
  have hv := x.nonneg v
  split_ifs <;> positivity

theorem cutWeight_le_edgeMass (s : Finset V) : x.cutWeight G s ≤ x.edgeMass G := by
  classical
  let f (u v : V) : ℝ := if u ∈ s ∧ v ∉ s then 1 else 0
  have h : x.edgeSum G (fun u v => f u v + f v u) ≤ x.edgeSum G (fun _ _ => 1) := by
    apply x.edgeSum_mono
    intro u v _
    dsimp [f]
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s <;> norm_num [hu, hv]
  rw [x.edgeSum_add, x.edgeSum_swap G f, x.edgeSum_one] at h
  change x.cutWeight G s + x.cutWeight G s ≤ 2 * x.edgeMass G at h
  linarith

theorem maxCut_le_edgeMass : x.maxCut G ≤ x.edgeMass G := by
  classical
  apply max'_le
  intro m hm
  obtain ⟨s, _, rfl⟩ := mem_image.mp hm
  exact x.cutWeight_le_edgeMass G s

/-- Edge mass inside the neighborhood of one root, counting unordered edges. -/
noncomputable def triangleRootMass (w : V) : ℝ := by
  classical
  exact x.edgeSum G (fun u v => if G.Adj w u ∧ G.Adj w v then 1 else 0) / 2

/-- Three times the unordered weighted triangle mass. -/
noncomputable def triangleMass : ℝ := ∑ w, x.weight w * x.triangleRootMass G w

theorem triangleRootMass_nonneg (w : V) : 0 ≤ x.triangleRootMass G w := by
  classical
  unfold triangleRootMass edgeSum
  apply div_nonneg _ (by norm_num)
  apply sum_nonneg
  intro u _
  apply sum_nonneg
  intro v _
  have hu := x.nonneg u
  have hv := x.nonneg v
  split_ifs <;> positivity

theorem triangleMass_nonneg : 0 ≤ x.triangleMass G :=
  sum_nonneg fun w _ => mul_nonneg (x.nonneg w) (x.triangleRootMass_nonneg G w)

noncomputable def neighborhoodVolume (w : V) : ℝ := by
  classical
  exact x.edgeSum G (fun u _ => if G.Adj w u then 1 else 0)

theorem neighborhood_cut_identity (w : V) :
    x.cutWeight G (neighbors G w) = x.neighborhoodVolume G w - 2 * x.triangleRootMass G w := by
  classical
  have h := x.edgeSum_add G
    (fun u v => if G.Adj w u ∧ ¬ G.Adj w v then 1 else 0)
    (fun u v => if G.Adj w u ∧ G.Adj w v then 1 else 0)
  have hf : (fun u v => (if G.Adj w u ∧ ¬ G.Adj w v then (1 : ℝ) else 0) +
      (if G.Adj w u ∧ G.Adj w v then 1 else 0)) =
      (fun u _ => if G.Adj w u then 1 else 0) := by
    funext u v
    by_cases hu : G.Adj w u <;> by_cases hv : G.Adj w v <;> norm_num [hu, hv]
  rw [hf] at h
  dsimp [cutWeight, neighborhoodVolume, triangleRootMass]
  simp only [mem_neighbors]
  linarith

theorem average_neighborhood_volume :
    (∑ w, x.weight w * x.neighborhoodVolume G w) =
      ∑ u, x.weight u * x.degree G u ^ 2 := by
  classical
  simp_rw [neighborhoodVolume, x.edgeSum_left, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  calc
    _ = x.weight u * x.degree G u * ∑ w, if G.Adj u w then x.weight w else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w _
      rw [G.adj_comm w u]
      by_cases h : G.Adj u w <;> simp [h] <;> ring
    _ = _ := by rw [← x.degree_eq_sum]; ring

/-- This is the exact averaged neighborhood-cut identity before Cauchy. -/
theorem average_neighborhood_cut :
    (∑ u, x.weight u * x.degree G u ^ 2) - 2 * x.triangleMass G ≤ x.maxCut G := by
  have hid : (∑ w, x.weight w * x.cutWeight G (neighbors G w)) =
      (∑ u, x.weight u * x.degree G u ^ 2) - 2 * x.triangleMass G := by
    calc
      _ = ∑ w, (x.weight w * x.neighborhoodVolume G w -
          2 * (x.weight w * x.triangleRootMass G w)) := by
        apply sum_congr rfl
        intro w _
        rw [x.neighborhood_cut_identity]
        ring
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, x.average_neighborhood_volume]; rfl
  rw [← hid]
  calc
    _ ≤ ∑ w, x.weight w * x.maxCut G :=
      sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (x.cutWeight_le_maxCut G _) (x.nonneg w)
    _ = x.maxCut G := by rw [← sum_mul, x.total, one_mul]

theorem maxCut_lower : 4 * x.edgeMass G ^ 2 - 2 * x.triangleMass G ≤ x.maxCut G := by
  have h := x.average_neighborhood_cut G
  have hs := x.degree_square_lower G
  linarith

/-- Strict superquarter density forces positive weighted triangle mass, even
when some vertex weights vanish. -/
theorem triangleMass_pos_of_superquarter (hm : 1 / 4 < x.edgeMass G) :
    0 < x.triangleMass G := by
  have hcut := x.maxCut_lower G
  have hle := x.maxCut_le_edgeMass G
  have hpos : 0 < x.edgeMass G := by linarith
  have hproduct := mul_pos hpos (show 0 < x.edgeMass G - 1 / 4 by linarith)
  nlinarith

end Erdos809.VertexWeights
