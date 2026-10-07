module
public import Erdos809.Source.RegularityPaths
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

@[expose] public section

/-!
# The typical-edge regularity reduction

This file separates the local path property from the global edge-loss account.
All endpoint degrees are measured in the original source graph.
-/

noncomputable section

namespace Erdos809.Source

universe u

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (P : Finpartition (univ : Finset V))

/-- Keep only dense regular inter-cluster edges with both endpoints typical
into the opposite original cluster. -/
def typicalReduction (ε d : ℝ) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ P.part a ≠ P.part b ∧ G.IsUniform ε (P.part a) (P.part b) ∧
    d ≤ G.edgeDensity (P.part a) (P.part b) ∧
    (d - ε) * (P.part b).card ≤ ((P.part b).filter (G.Adj a)).card ∧
    (d - ε) * (P.part a).card ≤ ((P.part a).filter (G.Adj b)).card
  symm := ⟨by
    intro a b
    rintro ⟨hab, hparts, hreg, hdense, htypA, htypB⟩
    exact ⟨hab.symm, hparts.symm, hreg.symm, by simpa [edgeDensity_comm] using hdense,
      htypB, htypA⟩⟩
  loopless.irrefl a h := h.1.ne rfl

instance (ε d : ℝ) : DecidableRel (typicalReduction G P ε d).Adj := Classical.decRel _

lemma typicalReduction_le (ε d : ℝ) : typicalReduction G P ε d ≤ G := fun _ _ h => h.1

private lemma typ_size_large {C : Finset V} {X : Finset V} {ε d : ℝ} {k : ℕ}
    (hlarge : (k : ℝ) + 2 ≤ (d - 2 * ε) * C.card)
    (htyp : (d - ε) * C.card ≤ X.card) :
    (C.card : ℝ) * ε + k + 2 ≤ X.card := by
  nlinarith

lemma typicalReduction_three_path {ε d : ℝ} {k : ℕ}
    (hd : ε ≤ d)
    (hlarge : ∀ C ∈ P.parts, (k : ℝ) + 2 ≤ (d - 2 * ε) * C.card)
    {a x y b : V} (hab : a ≠ b)
    (hax : (typicalReduction G P ε d).Adj a x)
    (hxy : (typicalReduction G P ε d).Adj x y)
    (hyb : (typicalReduction G P ε d).Adj y b)
    {F : Finset V} (hF : F.card ≤ k) (ha : a ∉ F) (hb : b ∉ F) :
    HasAvoidingPath G a b 3 F := by
  have hpx : P.part x ∈ P.parts := P.part_mem.mpr (mem_univ _)
  have hpy : P.part y ∈ P.parts := P.part_mem.mpr (mem_univ _)
  have hFreal : (F.card : ℝ) ≤ k := by exact_mod_cast hF
  apply hasAvoidingPath_three_of_uniform
    (X := (P.part x).filter (G.Adj a)) (Y := (P.part y).filter (G.Adj b)) hab ha hb hxy.2.2.1
    (hd.trans hxy.2.2.2.1) (filter_subset _ _) (filter_subset _ _)
  · intro u hu
    exact (mem_filter.mp hu).2
  · intro v hv
    exact (mem_filter.mp hv).2.symm
  · have h := typ_size_large (hlarge _ hpx) hax.2.2.2.2.1
    linarith
  · have h := typ_size_large (hlarge _ hpy) hyb.2.2.2.2.2
    linarith

private lemma typ_neighbors_many {C X : Finset V} {ε d p : ℝ} {k : ℕ}
    (hde : 0 ≤ d - ε) (hdp : d ≤ p)
    (htyp : (d - ε) * C.card ≤ X.card)
    (hlarge : (k : ℝ) + 5 < (d - ε) ^ 2 * C.card) :
    (k : ℝ) + 5 < (p - ε) * X.card := by
  apply hlarge.trans_le
  calc
    (d - ε) ^ 2 * C.card = (d - ε) * ((d - ε) * C.card) := by ring
    _ ≤ (d - ε) * X.card := mul_le_mul_of_nonneg_left htyp hde
    _ ≤ (p - ε) * X.card := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

lemma typicalReduction_five_path {ε d : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hd : 2 * ε ≤ d)
    (hlarge : ∀ C ∈ P.parts, (k : ℝ) + 2 ≤ (1 - 2 * ε) * C.card)
    (hlarge' : ∀ C ∈ P.parts, (k : ℝ) + 5 < (d - ε) ^ 2 * C.card)
    {a x₁ x₂ x₃ x₄ b : V} (hab : a ≠ b)
    (ha1 : (typicalReduction G P ε d).Adj a x₁)
    (h12 : (typicalReduction G P ε d).Adj x₁ x₂)
    (h23 : (typicalReduction G P ε d).Adj x₂ x₃)
    (h34 : (typicalReduction G P ε d).Adj x₃ x₄)
    (h4b : (typicalReduction G P ε d).Adj x₄ b)
    {F : Finset V} (hF : F.card ≤ k) (ha : a ∉ F) (hb : b ∉ F) :
    HasAvoidingPath G a b 5 F := by
  have hp (x : V) : P.part x ∈ P.parts := P.part_mem.mpr (mem_univ _)
  have hFreal : (F.card : ℝ) ≤ k := by exact_mod_cast hF
  have hd' : ε ≤ d := by linarith
  have hde : 0 ≤ d - ε := by linarith
  have h21dense : d ≤ G.edgeDensity (P.part x₂) (P.part x₁) := by
    simpa [edgeDensity_comm] using h12.2.2.2.1
  apply hasAvoidingPath_five_of_regular_chain
    (X := (P.part x₁).filter (G.Adj a)) (W := (P.part x₄).filter (G.Adj b)) hab ha hb h12.2.2.1.symm
    h23.2.2.1 h34.2.2.1 (hd'.trans h21dense) (hd'.trans h23.2.2.2.1)
    (hd'.trans h34.2.2.2.1) (filter_subset _ _) (filter_subset _ _)
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro w hw
    exact (mem_filter.mp hw).2.symm
  · apply le_trans _ ha1.2.2.2.2.1
    have hmul := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (P.part x₁).card)
    nlinarith
  · apply le_trans _ h4b.2.2.2.2.2
    have hmul := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (P.part x₄).card)
    nlinarith
  · have h := hlarge _ (hp x₂)
    nlinarith
  · have h := hlarge _ (hp x₃)
    nlinarith
  · exact lt_of_le_of_lt (by linarith) (typ_neighbors_many hde h21dense ha1.2.2.2.2.1 (hlarge' _ (hp x₁)))
  · exact lt_of_le_of_lt (by linarith) (typ_neighbors_many hde h34.2.2.2.1 h4b.2.2.2.2.2 (hlarge' _ (hp x₄)))


/-- Ordered regular dense cluster pairs. -/
def regularDensePairs (ε d : ℝ) : Finset (Finset V × Finset V) := by
  classical
  exact (P.parts ×ˢ P.parts).filter fun AB =>
    G.IsUniform ε AB.1 AB.2 ∧ d ≤ G.edgeDensity AB.1 AB.2

/-- All ordered pairs beginning at an endpoint atypical into the other cluster.
Nonedges are harmlessly included, which simplifies the complete deletion count. -/
def atypicalPairs (ε d : ℝ) : Finset (V × V) := by
  classical
  exact (regularDensePairs G P ε d).biUnion fun AB =>
    lowNeighbors (G := G) AB.1 AB.2 (d - ε) ×ˢ AB.2

lemma lowNeighbors_density_card_le {A B : Finset V} {ε d : ℝ}
    (hreg : G.IsUniform ε A B) (hd : ε ≤ d) (hdense : d ≤ G.edgeDensity A B)
    (hε : ε ≤ 1) : ((lowNeighbors (G := G) A B (d - ε)).card : ℝ) ≤ A.card * ε := by
  have hsub : lowNeighbors (G := G) A B (d - ε) ⊆
      lowNeighbors (G := G) A B (G.edgeDensity A B - ε) := by
    intro x hx
    obtain ⟨hxA, hxdeg⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hxA, hxdeg.trans_le ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  apply (Nat.cast_le.mpr (card_le_card hsub)).trans
  exact card_lowNeighbors_le hreg (hd.trans hdense) Subset.rfl
    (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)

/-- The total atypical-endpoint charge is εn², with no equal-cluster assumption. -/
lemma card_atypicalPairs_le {ε d : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hd : ε ≤ d) :
    ((atypicalPairs G P ε d).card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hterm (AB : Finset V × Finset V) (hAB : AB ∈ regularDensePairs G P ε d) :
      ((lowNeighbors (G := G) AB.1 AB.2 (d - ε) ×ˢ AB.2).card : ℝ) ≤
      ε * AB.1.card * AB.2.card := by
    obtain ⟨_, hreg, hdense⟩ := mem_filter.mp hAB
    have hc := lowNeighbors_density_card_le G hreg hd hdense hε'
    simpa [card_product, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg AB.2.card)
  have hc : ((atypicalPairs G P ε d).card : ℝ) ≤
      ∑ AB ∈ regularDensePairs G P ε d, ε * AB.1.card * AB.2.card := by
    apply (Nat.cast_le.mpr (card_biUnion_le)).trans
    push_cast
    exact sum_le_sum hterm
  apply hc.trans
  calc
    (∑ AB ∈ regularDensePairs G P ε d, ε * AB.1.card * AB.2.card) ≤
        ∑ AB ∈ P.parts ×ˢ P.parts, ε * AB.1.card * AB.2.card := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro AB _ _
      positivity
    _ = ε * (Fintype.card V : ℝ) ^ 2 := by
      rw [sum_product]
      simp_rw [← mul_sum, ← sum_mul]
      have hsum : (∑ C ∈ P.parts, (C.card : ℝ)) = Fintype.card V := by
        exact_mod_cast P.sum_card_parts
      rw [← mul_sum]
      simp only [hsum]
      ring

/-- Source unordered edges charged by atypical endpoints. -/
def atypicalDeletions (ε d : ℝ) : Finset (Sym2 V) := by
  classical
  exact (atypicalPairs G P ε d).image fun p => s(p.1, p.2)

lemma card_atypicalDeletions_le {ε d : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hd : ε ≤ d) :
    ((atypicalDeletions G P ε d).card : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
  (Nat.cast_le.mpr card_image_le).trans (card_atypicalPairs_le G P hε hε' hd)


lemma regularityReduced_delete_atypical_le {ε d : ℝ} :
    (G.regularityReduced P ε d).deleteEdges (atypicalDeletions G P ε d) ≤
      typicalReduction G P ε d := by
  classical
  intro u v huv
  obtain ⟨huv, hnot⟩ := deleteEdges_adj.mp huv
  obtain ⟨huvG, A, hA, B, hB, huA, hvB, hAB, hreg, hd⟩ := huv
  have hpu := P.part_eq_of_mem hA huA
  have hpv := P.part_eq_of_mem hB hvB
  change G.Adj u v ∧ _
  rw [hpu, hpv]
  refine ⟨huvG, hAB, hreg, hd, ?_, ?_⟩
  · by_contra hbad
    apply hnot
    apply mem_image.mpr
    refine ⟨(u, v), ?_, rfl⟩
    apply mem_biUnion.mpr
    refine ⟨(A, B), mem_filter.mpr ⟨mem_product.mpr ⟨hA, hB⟩, hreg, hd⟩, ?_⟩
    exact mem_product.mpr ⟨mem_filter.mpr ⟨huA, lt_of_not_ge hbad⟩, hvB⟩
  · by_contra hbad
    apply hnot
    apply mem_image.mpr
    refine ⟨(v, u), ?_, Sym2.eq_swap⟩
    apply mem_biUnion.mpr
    refine ⟨(B, A), mem_filter.mpr ⟨mem_product.mpr ⟨hB, hA⟩, hreg.symm, ?_⟩, ?_⟩
    · simpa [edgeDensity_comm] using hd
    · exact mem_product.mpr ⟨mem_filter.mpr ⟨hvB, lt_of_not_ge hbad⟩, huA⟩

lemma typicalReduction_robust_three {ε d : ℝ} {k : ℕ}
    (hd : ε ≤ d)
    (hlarge : ∀ C ∈ P.parts, (k : ℝ) + 2 ≤ (d - 2 * ε) * C.card) :
    RobustAtLength G (typicalReduction G P ε d) 3 k := by
  intro a b hab hp F hF ha hb
  obtain ⟨p, hp⟩ := hp
  cases p with
  | nil => simp at hp
  | cons h₁ p =>
    cases p with
    | nil => simp at hp
    | cons h₂ p =>
      cases p with
      | nil => simp at hp
      | cons h₃ p =>
        cases p with
        | nil => exact typicalReduction_three_path G P hd hlarge hab h₁ h₂ h₃ hF ha hb
        | cons _ p => simp only [Walk.length_cons] at hp; omega

lemma typicalReduction_robust_five {ε d : ℝ} {k : ℕ}
    (hε : 0 ≤ ε) (hd : 2 * ε ≤ d)
    (hlarge : ∀ C ∈ P.parts, (k : ℝ) + 2 ≤ (1 - 2 * ε) * C.card)
    (hlarge' : ∀ C ∈ P.parts, (k : ℝ) + 5 < (d - ε) ^ 2 * C.card) :
    RobustAtLength G (typicalReduction G P ε d) 5 k := by
  intro a b hab hp F hF ha hb
  obtain ⟨p, hp⟩ := hp
  cases p with
  | nil => simp at hp
  | cons h₁ p =>
    cases p with
    | nil => simp at hp
    | cons h₂ p =>
      cases p with
      | nil => simp at hp
      | cons h₃ p =>
        cases p with
        | nil => simp at hp
        | cons h₄ p =>
          cases p with
          | nil => simp at hp
          | cons h₅ p =>
            cases p with
            | nil => exact typicalReduction_five_path G P hε hd hlarge hlarge' hab h₁ h₂ h₃ h₄ h₅ hF ha hb
            | cons _ p => simp only [Walk.length_cons] at hp; omega


/-- Edges in cluster pairs whose original density is less than d. -/
def sparseDeletions (d : ℝ) : Finset (Sym2 V) := by
  classical
  exact ((P.sparsePairs G d).biUnion fun AB => G.interedges AB.1 AB.2).image
    fun p => s(p.1, p.2)

lemma card_sparseDeletions_le (hP : P.IsEquipartition) {d : ℝ} (hd : 0 ≤ d) :
    ((sparseDeletions G P d).card : ℝ) ≤ 4 * d * (Fintype.card V : ℝ) ^ 2 := by
  apply (Nat.cast_le.mpr card_image_le).trans
  simpa using hP.card_interedges_sparsePairs_le (G := G) hd

lemma reduced_delete_sparse_le {ε d₀ d : ℝ} :
    (G.regularityReduced P ε d₀).deleteEdges (sparseDeletions G P d) ≤
      G.regularityReduced P ε d := by
  classical
  intro u v huv
  obtain ⟨huv, hnot⟩ := deleteEdges_adj.mp huv
  obtain ⟨huvG, A, hA, B, hB, huA, hvB, hAB, hreg, _⟩ := huv
  refine ⟨huvG, A, hA, B, hB, huA, hvB, hAB, hreg, ?_⟩
  by_contra hbad
  apply hnot
  apply mem_image.mpr
  refine ⟨(u, v), ?_, rfl⟩
  apply mem_biUnion.mpr
  refine ⟨(A, B), ?_, ?_⟩
  · exact (P.mk_mem_sparsePairs G A B d).mpr ⟨hA, hB, hAB, lt_of_not_ge hbad⟩
  · exact G.mem_interedges_iff.mpr ⟨huA, hvB, huvG⟩

/-- The source edge loss of an arbitrary finite deletion set is at most its size. -/
lemma edge_loss_delete_le (D : Finset (Sym2 V)) :
    (G.edgeFinset.card : ℝ) - (G.deleteEdges D).edgeFinset.card ≤ D.card := by
  classical
  have hE : (G.deleteEdges D).edgeFinset = G.edgeFinset \ D := by
    ext e
    simp [edgeSet_deleteEdges]
  have hc : G.edgeFinset.card ≤ (G.deleteEdges D).edgeFinset.card + D.card := by
    rw [hE]
    exact card_le_card_sdiff_add_card
  have hcR : (G.edgeFinset.card : ℝ) ≤ (G.deleteEdges D).edgeFinset.card + D.card := by
    exact_mod_cast hc
  linarith

/-- Use the library regularity reduction, then pay separately for higher
edge density and typical endpoint conditions. -/
abbrev regularityPathCleaned (α : ℝ) : SimpleGraph V :=
  ((G.regularityReduced P (α / 8) (α / 4)).deleteEdges (sparseDeletions G P (α / 2))).deleteEdges
    (atypicalDeletions G P (α / 8) (α / 2))

lemma regularityPathCleaned_le_typical (α : ℝ) :
    regularityPathCleaned G P α ≤ typicalReduction G P (α / 8) (α / 2) := by
  apply le_trans _ (regularityReduced_delete_atypical_le G P)
  intro u v huv
  obtain ⟨huv, hnot⟩ := deleteEdges_adj.mp huv
  exact deleteEdges_adj.mpr ⟨reduced_delete_sparse_le G P huv, hnot⟩

lemma regularityPathCleaned_le (α : ℝ) : regularityPathCleaned G P α ≤ G :=
  (regularityPathCleaned_le_typical G P α).trans (typicalReduction_le G P _ _)

/-- Complete loss account for the regularity-based cleaner, including all
endpoint typicality deletions. -/
lemma regularityPathCleaned_loss [Nonempty V] {α : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1 / 4) (hP : P.IsEquipartition)
    (hPunif : P.IsUniform G (α / 8)) (hparts : 4 / α ≤ P.parts.card) :
    (G.edgeFinset.card : ℝ) - (regularityPathCleaned G P α).edgeFinset.card <
      4 * α * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hbase := regularityReduced_edges_card_aux (G := G) hα hP hPunif hparts
  have hsparse := card_sparseDeletions_le G P hP (show 0 ≤ α / 2 by positivity)
  have hatyp := card_atypicalDeletions_le G P (show 0 ≤ α / 8 by positivity)
    (show α / 8 ≤ 1 by linarith) (show α / 8 ≤ α / 2 by linarith)
  have hdel₁ := edge_loss_delete_le (G.regularityReduced P (α / 8) (α / 4))
    (sparseDeletions G P (α / 2))
  have hdel₂ := edge_loss_delete_le
    ((G.regularityReduced P (α / 8) (α / 4)).deleteEdges (sparseDeletions G P (α / 2)))
    (atypicalDeletions G P (α / 8) (α / 2))
  have hsq : 0 < (Fintype.card V : ℝ) ^ 2 := by positivity
  change (G.edgeFinset.card : ℝ) - _ < _
  dsimp [regularityPathCleaned]
  simp only [Nat.cast_pow] at hbase
  nlinarith


/-- Uniform cleanup for lengths three and five. The threshold depends only
on the tolerance and forbidden-set budget. The source graph is unchanged. -/
theorem exists_robust_three_five_cleanup (η : ℝ) (hη : 0 < η) (k : ℕ) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (G' : SimpleGraph W) [DecidableRel G'.Adj], N ≤ Fintype.card W →
      ∃ H : SimpleGraph W, ∃ _ : DecidableRel H.Adj, H ≤ G' ∧
        (G'.edgeFinset.card : ℝ) - H.edgeFinset.card < η * (Fintype.card W : ℝ) ^ 2 ∧
        RobustAtLength G' H 3 k ∧ RobustAtLength G' H 5 k := by
  classical
  let α := min (η / 4) (1 / 4)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hα' : α ≤ 1 / 4 := min_le_right _ _
  have hαη : 4 * α ≤ η := by have := min_le_left (η / 4) (1 / 4); dsimp [α]; linarith
  have hpos₁ : 0 < α / 4 := by positivity
  have hpos₂ : 0 < 1 - α / 4 := by linarith
  have hpos₃ : 0 < (3 * α / 8) ^ 2 := by positivity
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max (((k : ℝ) + 2) / (α / 4))
      (max (((k : ℝ) + 2) / (1 - α / 4)) (((k : ℝ) + 5) / (3 * α / 8) ^ 2)))
  have hL₁ : (k : ℝ) + 2 < (α / 4) * L := by
    have h := (div_lt_iff₀ hpos₁).mp ((le_max_left _ _).trans_lt hL)
    simpa [mul_comm] using h
  have hL₂ : (k : ℝ) + 2 < (1 - α / 4) * L := by
    have h := (div_lt_iff₀ hpos₂).mp (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hL)
    simpa [mul_comm] using h
  have hL₃ : (k : ℝ) + 5 < (3 * α / 8) ^ 2 * L := by
    have h := (div_lt_iff₀ hpos₃).mp (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hL)
    simpa [mul_comm] using h
  let l : ℕ := ⌈4 / α⌉₊
  let M := SzemerediRegularity.bound (α / 8) l
  refine ⟨max 1 (max l (L * M)), ?_⟩
  intro W instW instEq G' instG hn
  have hnpos : 0 < Fintype.card W := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hn)
  letI : Nonempty W := Fintype.card_pos_iff.mp hnpos
  have hnl : l ≤ Fintype.card W := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : L * M ≤ Fintype.card W := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨P', hPeq, hPl, hPM, hPunif⟩ := szemeredi_regularity G' (show 0 < α / 8 by positivity) hnl
  have hparts : 4 / α ≤ (P'.parts.card : ℝ) :=
    (Nat.le_ceil (4 / α)).trans (by exact_mod_cast hPl)
  have hpartpos : 0 < P'.parts.card := by
    have hpos : (0 : ℝ) < P'.parts.card := lt_of_lt_of_le (by positivity) hparts
    exact_mod_cast hpos
  have hLpart : ∀ C ∈ P'.parts, L ≤ C.card := by
    intro C hC
    have hdiv : L ≤ Fintype.card W / P'.parts.card := by
      apply (Nat.le_div_iff_mul_le hpartpos).mpr
      exact (Nat.mul_le_mul_left L hPM).trans hnM
    exact hdiv.trans (by simpa using hPeq.average_le_card_part hC)
  have hlarge₁ : ∀ C ∈ P'.parts, (k : ℝ) + 2 ≤ (α / 2 - 2 * (α / 8)) * C.card := by
    intro C hC
    have hstep := mul_le_mul_of_nonneg_left (show (L : ℝ) ≤ C.card by exact_mod_cast hLpart C hC) hpos₁.le
    nlinarith only [hL₁, hstep]
  have hlarge₂ : ∀ C ∈ P'.parts, (k : ℝ) + 2 ≤ (1 - 2 * (α / 8)) * C.card := by
    intro C hC
    have hstep := mul_le_mul_of_nonneg_left (show (L : ℝ) ≤ C.card by exact_mod_cast hLpart C hC) hpos₂.le
    nlinarith only [hL₂, hstep]
  have hlarge₃ : ∀ C ∈ P'.parts, (k : ℝ) + 5 < (α / 2 - α / 8) ^ 2 * C.card := by
    intro C hC
    have hstep := mul_le_mul_of_nonneg_left (show (L : ℝ) ≤ C.card by exact_mod_cast hLpart C hC) hpos₃.le
    nlinarith only [hL₃, hstep]
  refine ⟨regularityPathCleaned G' P' α, inferInstance, regularityPathCleaned_le G' P' α, ?_, ?_, ?_⟩
  · apply (regularityPathCleaned_loss G' P' hα hα' hPeq hPunif hparts).trans_le
    exact mul_le_mul_of_nonneg_right hαη (sq_nonneg _)
  · exact (typicalReduction_robust_three G' P' (by linarith) hlarge₁).mono
      (regularityPathCleaned_le_typical G' P' α)
  · exact (typicalReduction_robust_five G' P' (by positivity) (by linarith) hlarge₂ hlarge₃).mono
      (regularityPathCleaned_le_typical G' P' α)

end Erdos809.Source
