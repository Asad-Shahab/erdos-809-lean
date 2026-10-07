module
/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
public import Erdos809.Source.RobustPaths
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Degree pruning after spanning edge cleanup

Every lost edge, including edges incident with discarded vertices, is charged.
The resulting induced graph embeds into the spanning cleaner; robust paths
remain paths of the original source graph.
-/

noncomputable section
namespace Erdos809.Source

open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- The induced-edge cardinality identity, supplied locally for mathlib 4.28. -/
private lemma card_filter_edgeFinset_toFinset_subset_compat (S : Finset V) :
    (G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ S)).card =
      (G.induce (S : Set V)).edgeFinset.card := by
  classical
  have hmap := congrArg Finset.card (G.map_edgeFinset_induce (s := (S : Set V)))
  have heq : G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ S) = G.edgeFinset ∩ S.sym2 := by
    simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]
  rw [heq]
  simpa only [card_map, Finset.toFinset_coe, edgeFinset_card,
    ← Nat.card_eq_fintype_card] using hmap.symm

/-- The number of source edges omitted by the spanning cleanup, as a real. -/
def cleanupLoss : ℝ := (G.edgeFinset.card : ℝ) - H.edgeFinset.card

/-- Vertices losing more than the absolute per-vertex threshold t. -/
def pruningBad (t : ℝ) : Finset V := by
  classical
  exact univ.filter (fun v ↦ t < (G.degree v : ℝ) - H.degree v)

lemma degree_loss_sum :
    (∑ v, ((G.degree v : ℝ) - H.degree v)) = 2 * cleanupLoss G H := by
  have hg := congrArg (fun x : ℕ ↦ (x : ℝ)) G.sum_degrees_eq_twice_card_edges
  have hh := congrArg (fun x : ℕ ↦ (x : ℝ)) H.sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hg hh
  rw [sum_sub_distrib, hg, hh]
  unfold cleanupLoss
  ring

lemma pruningBad_card_le (hHG : H ≤ G) {t : ℝ} (ht : 0 < t) :
    ((pruningBad G H t).card : ℝ) ≤ 2 * cleanupLoss G H / t := by
  have hnonneg (v : V) : 0 ≤ (G.degree v : ℝ) - H.degree v := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr (H.degree_le_of_le hHG))
  have hlow : ((pruningBad G H t).card : ℝ) * t ≤
      ∑ v ∈ pruningBad G H t, ((G.degree v : ℝ) - H.degree v) := by
    calc
      _ = ∑ _v ∈ pruningBad G H t, t := by simp
      _ ≤ _ := sum_le_sum (fun v hv ↦ (mem_filter.mp hv).2.le)
  have hsum : (∑ v ∈ pruningBad G H t, ((G.degree v : ℝ) - H.degree v)) ≤
      ∑ v, ((G.degree v : ℝ) - H.degree v) := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ ↦ hnonneg v)
  rw [degree_loss_sum] at hsum
  exact (le_div_iff₀ ht).mpr (hlow.trans hsum)

/-- Vertex deletion decreases any surviving degree by at most the deleted order. -/
lemma degree_induce_compl_lower (B : Finset V) (v : (↑(univ \ B) : Set V)) :
    H.degree v.val ≤ (H.induce (↑(univ \ B) : Set V)).degree v + B.card := by
  have hmap := congrArg Finset.card (H.map_neighborFinset_induce v)
  have heq : H.neighborFinset v.val ∩ (univ \ B) = H.neighborFinset v.val \ B := by
    ext w
    simp
  simp only [card_map, card_neighborFinset_eq_degree, Finset.toFinset_coe] at hmap
  rw [heq] at hmap
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] at hmap ⊢
  rw [hmap]
  simpa only [card_neighborFinset_eq_degree, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    using card_le_card_sdiff_add_card (s := H.neighborFinset v.val) (t := B)

/-- All edges lost by deleting B are covered by incidence sets of vertices in B. -/
lemma edge_loss_induce_compl_le (B : Finset V) :
    (H.edgeFinset.card : ℝ) - (H.induce (↑(univ \ B) : Set V)).edgeFinset.card ≤
      (B.card : ℝ) * Fintype.card V := by
  classical
  let S : Finset V := univ \ B
  let D := H.edgeFinset.filter (fun e ↦ ¬ e.toFinset ⊆ S)
  have hsub : D ⊆ B.biUnion (fun v ↦ H.incidenceFinset v) := by
    intro e he
    obtain ⟨hee, hn⟩ := mem_filter.mp he
    obtain ⟨v, hve, hvS⟩ := not_subset.mp hn
    have hvB : v ∈ B := by simpa only [S, mem_sdiff, mem_univ, true_and, not_not] using hvS
    apply mem_biUnion.mpr
    refine ⟨v, hvB, ?_⟩
    exact (H.mem_incidenceFinset).mpr ⟨by simpa using hee, by simpa using hve⟩
  have hD : D.card ≤ B.card * Fintype.card V := by
    calc
      D.card ≤ (B.biUnion (fun v ↦ H.incidenceFinset v)).card := card_le_card hsub
      _ ≤ ∑ v ∈ B, (H.incidenceFinset v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ B, Fintype.card V := sum_le_sum (fun v _ ↦ by
        rw [H.card_incidenceFinset_eq_degree]
        exact (H.degree_lt_card_verts v).le)
      _ = _ := by simp
  have hpartition : (H.induce (S : Set V)).edgeFinset.card + D.card = H.edgeFinset.card := by
    rw [← card_filter_edgeFinset_toFinset_subset_compat H S]
    exact card_filter_add_card_filter_not _
  have hpartitionR : ((H.induce (S : Set V)).edgeFinset.card : ℝ) + D.card = H.edgeFinset.card := by
    exact_mod_cast hpartition
  have hDR : (D.card : ℝ) ≤ (B.card : ℝ) * Fintype.card V := by exact_mod_cast hD
  change (H.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤ _
  linarith

/-- Prune vertices with cleanup degree loss above t. The conclusion records
order, minimum degree and all omitted edges, using the original source order. -/
theorem exists_degree_pruning (hHG : H ≤ G) {t D : ℝ} (ht : 0 < t)
    (hdegree : ∀ v, D ≤ (G.degree v : ℝ)) :
    ∃ S : Finset V,
      (Fintype.card V : ℝ) - 2 * cleanupLoss G H / t ≤ S.card ∧
      S.card ≤ Fintype.card V ∧
      (∀ v : (S : Set V), D - t - 2 * cleanupLoss G H / t ≤
        ((H.induce (S : Set V)).degree v : ℝ)) ∧
      (G.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤
        cleanupLoss G H + (2 * cleanupLoss G H / t) * Fintype.card V ∧
      Nonempty (H.induce (S : Set V) ↪g H) := by
  classical
  let B := pruningBad G H t
  let S : Finset V := univ \ B
  have hB : (B.card : ℝ) ≤ 2 * cleanupLoss G H / t := pruningBad_card_le G H hHG ht
  have hcards : (S.card : ℝ) + B.card = Fintype.card V := by
    exact_mod_cast card_sdiff_add_card_eq_card (subset_univ B)
  refine ⟨S, ?_, card_le_card (subset_univ S), ?_, ?_, ⟨Embedding.induce _⟩⟩
  · linarith
  · intro v
    have hvB : v.val ∉ B := (mem_sdiff.mp v.property).2
    have hvLoss : (G.degree v.val : ℝ) - H.degree v.val ≤ t := by
      apply le_of_not_gt
      intro hloss
      exact hvB (mem_filter.mpr ⟨mem_univ _, hloss⟩)
    have hInd : (H.degree v.val : ℝ) ≤
        (H.induce (S : Set V)).degree v + (B.card : ℝ) := by
      exact_mod_cast degree_induce_compl_lower H B v
    have hv := hdegree v.val
    linarith
  · have hInd := edge_loss_induce_compl_le H B
    have hmul := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
    change (G.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤ _
    change (H.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤ _ at hInd
    unfold cleanupLoss at hmul ⊢
    linarith

/-- Standard normalized degree-pruning parameters. Every loss, including edges
at deleted vertices, appears in the final coefficient eta + 2*eta/beta. -/
theorem exists_degree_pruning_margin (hHG : H ≤ G) {γ β η : ℝ}
    (hγ : 0 < γ) (hβ : 0 < β) (hn : 0 < Fintype.card V)
    (hloss : cleanupLoss G H ≤ η * (Fintype.card V : ℝ) ^ 2)
    (hmargin : β + 2 * η / β < γ / 2)
    (hdegree : ∀ v, (1 / 3 + γ) * (Fintype.card V : ℝ) ≤ G.degree v) :
    ∃ S : Finset V,
      (1 - 2 * η / β) * (Fintype.card V : ℝ) ≤ S.card ∧
      S.card ≤ Fintype.card V ∧
      (∀ v : (S : Set V), (1 / 3 + γ / 2) * (S.card : ℝ) <
        ((H.induce (S : Set V)).degree v : ℝ)) ∧
      (G.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤
        (η + 2 * η / β) * (Fintype.card V : ℝ) ^ 2 ∧
      Nonempty (H.induce (S : Set V) ↪g H) := by
  have hnR : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hn
  have ht : 0 < β * (Fintype.card V : ℝ) := mul_pos hβ hnR
  have hratio : 2 * cleanupLoss G H / (β * (Fintype.card V : ℝ)) ≤
      (2 * η / β) * Fintype.card V := by
    apply (div_le_iff₀ ht).mpr
    have heq : (2 * η / β) * (Fintype.card V : ℝ) * (β * Fintype.card V) =
        2 * (η * (Fintype.card V : ℝ) ^ 2) := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  obtain ⟨S, hs, hsmax, hd, hq, hcopy⟩ := exists_degree_pruning G H hHG ht hdegree
  refine ⟨S, ?_, hsmax, ?_, ?_, hcopy⟩
  · nlinarith
  · intro v
    have hgap := mul_lt_mul_of_pos_right hmargin hnR
    have hv := hd v
    have hSreal : (S.card : ℝ) ≤ Fintype.card V := Nat.cast_le.mpr hsmax
    have hS := mul_le_mul_of_nonneg_left hSreal (show 0 ≤ (1 / 3 + γ / 2 : ℝ) by positivity)
    nlinarith
  · have hb := mul_le_mul_of_nonneg_right hratio hnR.le
    nlinarith

end Erdos809.Source
