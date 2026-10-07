module
/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
public import Erdos809.Resources

@[expose] public section

/-! No compatible triple contains a triangular edge. The proof retains the
six endpoint neighborhoods separately, even when actual endpoints coincide. -/

namespace Erdos809

open VertexWeights

variable {V : Type*} [Fintype V] (x : VertexWeights V) (G : SimpleGraph V)

theorem some_neighborhood_intersection {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u a c : V) :
    Walk2 G u a ∨ Walk2 G u c ∨ Walk2 G a c := by
  by_contra hn
  push Not at hn
  exact x.no_three_disjoint_neighborhoods G hδ hmin u a c
    ((disjoint_neighbors_iff G).mpr hn.1)
    ((disjoint_neighbors_iff G).mpr hn.2.1)
    ((disjoint_neighbors_iff G).mpr hn.2.2)

/-- In a compatible triple every cross matching is total. This proves the
nontrivial missing-row case without any enumeration of weighted hosts. -/
theorem compatible_triple_cross_total {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b c d : V}
    (_h₁₂ : Compatible G u v a b) (h₁₃ : Compatible G u v c d)
    (h₂₃ : Compatible G a b c d)
    (huv : G.Adj u v) (hab : G.Adj a b) (hcd : G.Adj c d) :
    Walk2 G u a ∨ Walk2 G u b := by
  by_contra hn
  push Not at hn
  have hu_a_c := some_neighborhood_intersection x G hδ hmin u a c
  have hu_a_d := some_neighborhood_intersection x G hδ hmin u a d
  have hu_b_c := some_neighborhood_intersection x G hδ hmin u b c
  have hu_b_d := some_neighborhood_intersection x G hδ hmin u b d
  have huc_or_hud : Walk2 G u c ∨ Walk2 G u d := by
    by_contra hnone
    push Not at hnone
    have hac := (hu_a_c.resolve_left hn.1).resolve_left hnone.1
    have had := (hu_a_d.resolve_left hn.1).resolve_left hnone.2
    exact h₂₃.partial_row G hab ⟨hac, had⟩
  rcases huc_or_hud with huc | hud
  · have hud : ¬ Walk2 G u d := fun hud => h₁₃.partial_row G huv ⟨huc, hud⟩
    have had := (hu_a_d.resolve_left hn.1).resolve_left hud
    have hbd := (hu_b_d.resolve_left hn.2).resolve_left hud
    exact (h₂₃.flip_right G).partial_column G hcd.symm ⟨had, hbd⟩
  · have huc : ¬ Walk2 G u c := fun huc => h₁₃.partial_row G huv ⟨huc, hud⟩
    have hac := (hu_a_c.resolve_left hn.1).resolve_left huc
    have hbc := (hu_b_c.resolve_left hn.2).resolve_left huc
    exact h₂₃.partial_column G hcd ⟨hac, hbc⟩

/-- After aligning the cross matchings, a triangle at the first edge creates
three pairwise disjoint neighborhoods, contradicting the minimum degree. -/
theorem compatible_aligned_triple_not_triangular {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b c d : V}
    (h₁₂ : Compatible G u v a b) (h₁₃ : Compatible G u v c d)
    (h₂₃ : Compatible G a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hua : Walk2 G u a) (hvb : Walk2 G v b)
    (huc : Walk2 G u c) (_hvd : Walk2 G v d) : ¬ Walk2 G u v := by
  intro huv
  have hva : ¬ Walk2 G v a := fun hva => h₁₂.partial_column G hab ⟨hua, hva⟩
  have hvc : ¬ Walk2 G v c := fun hvc => h₁₃.partial_column G hcd ⟨huc, hvc⟩
  have hac := ((some_neighborhood_intersection x G hδ hmin v a c).resolve_left hva).resolve_left hvc
  have had : ¬ Walk2 G a d := fun had => h₂₃.partial_row G hab ⟨hac, had⟩
  obtain ⟨z, huz, hzv⟩ := huv
  have hza : ¬ Walk2 G z a := by
    rintro ⟨t, hzt, hta⟩
    exact h₁₂.2.2.2 ⟨hvb, z, t, huz, hzt, hta⟩
  have hzd : ¬ Walk2 G z d := by
    rintro ⟨t, hzt, htd⟩
    exact h₁₃.1 ⟨huc, z, t, hzv.symm, hzt, htd⟩
  exact x.no_three_disjoint_neighborhoods G hδ hmin z a d
    ((disjoint_neighbors_iff G).mpr hza)
    ((disjoint_neighbors_iff G).mpr hzd)
    ((disjoint_neighbors_iff G).mpr had)

theorem compatible_triple_not_triangular {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v a b c d : V}
    (h₁₂ : Compatible G u v a b) (h₁₃ : Compatible G u v c d)
    (h₂₃ : Compatible G a b c d)
    (huv : G.Adj u v) (hab : G.Adj a b) (hcd : G.Adj c d) : ¬ Walk2 G u v := by
  have total₁₂ := compatible_triple_cross_total x G hδ hmin h₁₂ h₁₃ h₂₃ huv hab hcd
  have total₁₃ := compatible_triple_cross_total x G hδ hmin h₁₃ h₁₂ (h₂₃.symm G) huv hcd hab
  have total₂₂ := compatible_triple_cross_total x G hδ hmin
    (h₁₂.flip_left G) (h₁₃.flip_left G) h₂₃ huv.symm hab hcd
  have total₂₃ := compatible_triple_cross_total x G hδ hmin
    (h₁₃.flip_left G) (h₁₂.flip_left G) (h₂₃.symm G) huv.symm hcd hab
  have aligned {a b c d : V} (h₁₂ : Compatible G u v a b)
      (h₁₃ : Compatible G u v c d) (h₂₃ : Compatible G a b c d)
      (hab : G.Adj a b) (hcd : G.Adj c d)
      (hua : Walk2 G u a) (huc : Walk2 G u c)
      (tvab : Walk2 G v a ∨ Walk2 G v b)
      (tvcd : Walk2 G v c ∨ Walk2 G v d) : ¬ Walk2 G u v := by
    have hvb := tvab.resolve_left (fun hva => h₁₂.partial_column G hab ⟨hua, hva⟩)
    have hvd := tvcd.resolve_left (fun hvc => h₁₃.partial_column G hcd ⟨huc, hvc⟩)
    exact compatible_aligned_triple_not_triangular x G hδ hmin
      h₁₂ h₁₃ h₂₃ hab hcd hua hvb huc hvd
  rcases total₁₂ with hua | hub <;> rcases total₁₃ with huc | hud
  · exact aligned h₁₂ h₁₃ h₂₃ hab hcd hua huc total₂₂ total₂₃
  · exact aligned h₁₂ (h₁₃.flip_right G) (h₂₃.flip_right G)
      hab hcd.symm hua hud total₂₂ total₂₃.symm
  · exact aligned (h₁₂.flip_right G) h₁₃ (h₂₃.flip_left G)
      hab.symm hcd hub huc total₂₂.symm total₂₃
  · exact aligned (h₁₂.flip_right G) (h₁₃.flip_right G)
      ((h₂₃.flip_left G).flip_right G) hab.symm hcd.symm hub hud total₂₂.symm total₂₃.symm

end Erdos809
