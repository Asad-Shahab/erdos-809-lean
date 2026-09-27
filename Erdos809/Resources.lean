/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.WeightedGraph
import Mathlib.Tactic.Push

/-!
# Nontriangular sectors and whole-pattern resources

All neighborhoods refer to the unchanged full host. The resource arguments do
not assume that a source coloring is proper or that a pattern is a matching.
-/

namespace Erdos809

open Finset
open VertexWeights

variable {V : Type*} [Fintype V] (x : VertexWeights V) (G : SimpleGraph V)

theorem disjoint_neighbors_iff {u v : V} :
    Disjoint (neighbors G u) (neighbors G v) ↔ ¬ Walk2 G u v := by
  classical
  simp only [disjoint_left, mem_neighbors, Walk2, not_exists, not_and]
  constructor
  · intro h z huz hzv
    exact h huz hzv.symm
  · intro h z huz hvz
    exact h z huz hvz.symm

/-- A compatible pair cannot mix triangular and nontriangular edges above 1/3. -/
theorem compatible_no_mixed_sectors {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b : V}
    (h : Compatible G u v a b) (huv : Triangular G u v)
    (hab : G.Adj a b) (habF : ¬ Walk2 G a b) : False := by
  obtain ⟨z, hz⟩ := (h.symm G).exists_outside_neighborhood G hab huv
  have hza : ¬ Walk2 G z a := by
    rintro ⟨t, hzt, hta⟩
    exact (hz t hzt).1 hta.symm
  have hzb : ¬ Walk2 G z b := by
    rintro ⟨t, hzt, htb⟩
    exact (hz t hzt).2 htb.symm
  exact x.no_three_disjoint_neighborhoods G hδ hmin z a b
    ((disjoint_neighbors_iff G).mpr hza) ((disjoint_neighbors_iff G).mpr hzb)
    ((disjoint_neighbors_iff G).mpr habF)

/-- When the mate is nontriangular, each endpoint must meet a mate neighborhood. -/
theorem compatible_cross_total {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u a b : V}
    (habF : ¬ Walk2 G a b) : Walk2 G u a ∨ Walk2 G u b := by
  by_contra hn
  push Not at hn
  exact x.no_three_disjoint_neighborhoods G hδ hmin u a b
    ((disjoint_neighbors_iff G).mpr hn.1) ((disjoint_neighbors_iff G).mpr hn.2)
    ((disjoint_neighbors_iff G).mpr habF)

/-- A triangular neighbor of either endpoint belongs to the edge's resource. -/
def Resource (u v w : V) : Prop := Triangular G u w ∨ Triangular G v w

omit [Fintype V] in
/-- If a triangular neighbor were in an aligned mate neighborhood, its triangle
would give a forbidden complementary three-walk. -/
theorem resource_avoids_aligned {u v a b w : V}
    (h : Compatible G u v a b) (hvb : Walk2 G v b)
    (huw : Triangular G u w) : ¬ G.Adj a w := by
  intro haw
  obtain ⟨t, hut, htw⟩ := huw.2
  exact h.2.2.2 ⟨hvb, t, w, hut, htw, haw.symm⟩

/-- Compatible nontriangular edges have resources outside the entire endpoint
neighborhood union of their mate. -/
theorem resource_avoids_mate {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b w : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : G.Adj a b)
    (habF : ¬ Walk2 G a b) (hw : Resource G u v w) :
    ¬ G.Adj a w ∧ ¬ G.Adj b w := by
  have endpoint {s t a b : V} (hst : G.Adj s t) (hab : G.Adj a b)
      (habF : ¬ Walk2 G a b) (h : Compatible G s t a b)
      (hsw : Triangular G s w) : ¬ G.Adj a w ∧ ¬ G.Adj b w := by
    rcases compatible_cross_total x G hδ hmin habF (u := s) with hsa | hsb
    · have hsb : ¬ Walk2 G s b := fun hsb => h.partial_row G hst ⟨hsa, hsb⟩
      have hta : ¬ Walk2 G t a := fun hta => h.partial_column G hab ⟨hsa, hta⟩
      have htb : Walk2 G t b :=
        (compatible_cross_total x G hδ hmin habF (u := t)).resolve_left hta
      exact ⟨resource_avoids_aligned G h htb hsw,
        fun hbw => hsb ⟨w, hsw.1, hbw.symm⟩⟩
    · have hsa : ¬ Walk2 G s a := fun hsa => h.partial_row G hst ⟨hsa, hsb⟩
      have htb : ¬ Walk2 G t b :=
        fun htb => (h.flip_right G).partial_column G hab.symm ⟨hsb, htb⟩
      have hta : Walk2 G t a :=
        (compatible_cross_total x G hδ hmin habF (u := t)).resolve_right htb
      exact ⟨fun haw => hsa ⟨w, hsw.1, haw.symm⟩,
        resource_avoids_aligned G (h.flip_right G) hta hsw⟩
  rcases hw with huw | hvw
  · exact endpoint huv hab habF h huw
  · exact endpoint huv.symm hab habF (h.flip_left G) hvw

theorem compatible_resources_disjoint {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b w : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : G.Adj a b)
    (habF : ¬ Walk2 G a b) (hw : Resource G u v w) : ¬ Resource G a b w := by
  obtain ⟨ha, hb⟩ := resource_avoids_mate x G hδ hmin h huv hab habF hw
  rintro (haw | hbw)
  · exact ha haw.1
  · exact hb hbw.1

/-- The whole-pattern conclusion: pairwise resource exclusion makes the map
from root incidences to edge indices injective, so each root pays at most once. -/
theorem whole_pattern_resource_unique {I : Type*} {δ : ℝ}
    (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast G δ)
    (u v : I → V) (hedge : ∀ i, G.Adj (u i) (v i))
    (hF : ∀ i, ¬ Walk2 G (u i) (v i))
    (hpattern : ∀ i j, i ≠ j → Compatible G (u i) (v i) (u j) (v j))
    (w : V) {i j : I} (hi : Resource G (u i) (v i) w)
    (hj : Resource G (u j) (v j) w) : i = j := by
  by_contra hne
  exact compatible_resources_disjoint x G hδ hmin (hpattern i j hne)
    (hedge i) (hedge j) (hF j) hi hj

end Erdos809
