import Erdos809.Source.RobustPaths
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.FinCases

/-!
# Tripartite graph for robust two-path cleanup

The middle part records genuine common neighbors; virtual edges join pairs
with small original codegree. Every auxiliary triangle is a bad source wedge.
-/

noncomputable section

namespace Erdos809.Source

universe u

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Distinct source endpoints whose original codegree is at most k. -/
def lowCodegree (k : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ (G.neighborFinset u ∩ G.neighborFinset v).card ≤ k

private def auxForward (k : ℕ) (a b : Fin 3 × V) : Prop :=
  (a.1 = 0 ∧ b.1 = 1 ∧ G.Adj a.2 b.2) ∨
  (a.1 = 1 ∧ b.1 = 2 ∧ G.Adj a.2 b.2) ∨
  (a.1 = 0 ∧ b.1 = 2 ∧ lowCodegree G k a.2 b.2)

/-- Auxiliary tripartite graph with two original-edge layers and one virtual layer. -/
def twoPathAux (k : ℕ) : SimpleGraph (Fin 3 × V) where
  Adj a b := auxForward G k a b ∨ auxForward G k b a
  symm := fun _ _ h => h.symm
  loopless := ⟨by
    intro a h
    simp only [auxForward] at h
    rcases h with (⟨h0, h1, _⟩ | ⟨h1, h2, _⟩ | ⟨h0, h2, _⟩) |
      (⟨h0, h1, _⟩ | ⟨h1, h2, _⟩ | ⟨h0, h2, _⟩) <;> omega⟩

instance (k : ℕ) : DecidableRel (twoPathAux G k).Adj := Classical.decRel _

@[simp] lemma twoPathAux_adj_01 {k : ℕ} {u w : V} :
    (twoPathAux G k).Adj (0, u) (1, w) ↔ G.Adj u w := by
  simp [twoPathAux, auxForward]

@[simp] lemma twoPathAux_adj_12 {k : ℕ} {w v : V} :
    (twoPathAux G k).Adj (1, w) (2, v) ↔ G.Adj w v := by
  simp [twoPathAux, auxForward]

@[simp] lemma twoPathAux_adj_02 {k : ℕ} {u v : V} :
    (twoPathAux G k).Adj (0, u) (2, v) ↔ lowCodegree G k u v := by
  simp [twoPathAux, auxForward]

lemma twoPathAux_adj_parts_ne {k : ℕ} {a b : Fin 3 × V}
    (h : (twoPathAux G k).Adj a b) : a.1 ≠ b.1 := by
  rcases h with (⟨h0, h1, _⟩ | ⟨h1, h2, _⟩ | ⟨h0, h2, _⟩) |
    (⟨h0, h1, _⟩ | ⟨h1, h2, _⟩ | ⟨h0, h2, _⟩) <;> omega

/-- The canonical ordered triples underlying auxiliary triangles. -/
def badWedges (k : ℕ) : Finset (V × V × V) := by
  classical
  exact univ.filter fun p => lowCodegree G k p.1 p.2.2 ∧ G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2

lemma mem_badWedges {k : ℕ} {u w v : V} :
    (u, w, v) ∈ badWedges G k ↔
      lowCodegree G k u v ∧ G.Adj u w ∧ G.Adj w v := by
  simp [badWedges]

/-- Every auxiliary triangle has a canonical representative with one vertex
in each part. This counts ordinary unordered clique finsets, not ordered walks. -/
lemma cliqueFinset_twoPathAux_subset_image (k : ℕ) :
    (twoPathAux G k).cliqueFinset 3 ⊆
      (badWedges G k).image (fun p => {(0, p.1), (1, p.2.1), (2, p.2.2)}) := by
  classical
  intro T hT
  have hcl : (twoPathAux G k).IsClique (T : Set (Fin 3 × V)) :=
    ((mem_cliqueFinset_iff.mp hT).1)
  have hcard : T.card = 3 := (mem_cliqueFinset_iff.mp hT).2
  have hinj : Set.InjOn Prod.fst (T : Set (Fin 3 × V)) := by
    intro a ha b hb heq
    by_contra hne
    exact twoPathAux_adj_parts_ne G (hcl ha hb hne) heq
  have himage : T.image Prod.fst = (univ : Finset (Fin 3)) := by
    apply eq_univ_of_card
    rw [card_image_iff.mpr hinj, hcard]
    simp
  have hex (i : Fin 3) : ∃ x : V, (i, x) ∈ T := by
    have hi : i ∈ T.image Prod.fst := by rw [himage]; exact mem_univ _
    obtain ⟨⟨j, x⟩, hx, heq⟩ := mem_image.mp hi
    cases heq
    exact ⟨x, hx⟩
  obtain ⟨u, hu⟩ := hex 0
  obtain ⟨w, hw⟩ := hex 1
  obtain ⟨v, hv⟩ := hex 2
  have huw : G.Adj u w := (twoPathAux_adj_01 G).mp (hcl hu hw (by simp))
  have hwv : G.Adj w v := (twoPathAux_adj_12 G).mp (hcl hw hv (by simp))
  have huv : lowCodegree G k u v := (twoPathAux_adj_02 G).mp (hcl hu hv (by simp))
  apply mem_image.mpr
  refine ⟨(u, w, v), (mem_badWedges G).mpr ⟨huv, huw, hwv⟩, ?_⟩
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simp [hcard]


lemma card_badWedges_le (k : ℕ) :
    (badWedges G k).card ≤ k * Fintype.card V ^ 2 := by
  classical
  let C : V × V → Finset (V × V × V) := fun p =>
    if lowCodegree G k p.1 p.2 then
      (G.neighborFinset p.1 ∩ G.neighborFinset p.2).image (fun w => (p.1, w, p.2))
    else ∅
  have hC : ∀ p, (C p).card ≤ k := by
    intro p
    dsimp [C]
    split_ifs with hp
    · exact card_image_le.trans hp.2
    · simp
  have hsub : badWedges G k ⊆ univ.biUnion C := by
    rintro ⟨u, w, v⟩ hp
    obtain ⟨huv, huw, hwv⟩ := (mem_badWedges G).mp hp
    apply mem_biUnion.mpr
    refine ⟨(u, v), mem_univ _, ?_⟩
    dsimp [C]
    rw [if_pos huv]
    apply mem_image.mpr
    refine ⟨w, ?_, rfl⟩
    simp [huw, hwv.symm]
  calc
    (badWedges G k).card ≤ (univ.biUnion C).card := card_le_card hsub
    _ ≤ ∑ p : V × V, (C p).card := card_biUnion_le
    _ ≤ ∑ _p : V × V, k := sum_le_sum (fun p _ => hC p)
    _ = k * Fintype.card V ^ 2 := by simp; ring

/-- There are only quadratically many auxiliary triangles, uniformly over G. -/
lemma card_triangles_twoPathAux_le (k : ℕ) :
    ((twoPathAux G k).cliqueFinset 3).card ≤ k * Fintype.card V ^ 2 := by
  exact (card_le_card (cliqueFinset_twoPathAux_subset_image G k)).trans
    (card_image_le.trans (card_badWedges_le G k))


/-- Source edges to delete when an ordered auxiliary pair has been removed. -/
def deletionFiber (k : ℕ) (p : (Fin 3 × V) × (Fin 3 × V)) : Finset (Sym2 V) := by
  classical
  exact if p.1.1 = 0 ∧ p.2.1 = 2 ∧ lowCodegree G k p.1.2 p.2.2 then
    (G.neighborFinset p.1.2 ∩ G.neighborFinset p.2.2).image (fun w => s(p.1.2, w))
  else {s(p.1.2, p.2.2)}

lemma card_deletionFiber_le (k : ℕ) (p : (Fin 3 × V) × (Fin 3 × V)) :
    (deletionFiber G k p).card ≤ k + 1 := by
  classical
  dsimp [deletionFiber]
  split_ifs with h
  · exact card_image_le.trans (h.2.2.2.trans (Nat.le_succ k))
  · simp

/-- Ordered auxiliary edges absent from the triangle-free subgraph. -/
def missingAuxPairs (k : ℕ) (A : SimpleGraph (Fin 3 × V)) :
    Finset ((Fin 3 × V) × (Fin 3 × V)) := by
  classical
  exact univ.filter fun p => (twoPathAux G k).Adj p.1 p.2 ∧ ¬A.Adj p.1 p.2

/-- The full source deletion set, including every cost of a deleted virtual edge. -/
def twoPathDeletions (k : ℕ) (A : SimpleGraph (Fin 3 × V)) : Finset (Sym2 V) := by
  classical
  exact (missingAuxPairs G k A).biUnion (deletionFiber G k)

lemma card_twoPathDeletions_le (k : ℕ) (A : SimpleGraph (Fin 3 × V)) :
    (twoPathDeletions G k A).card ≤ (missingAuxPairs G k A).card * (k + 1) := by
  classical
  apply card_biUnion_le.trans
  exact (sum_le_sum fun p _ => card_deletionFiber_le G k p).trans_eq (by simp)

/-- The actual source graph obtained from an auxiliary triangle-free graph. -/
abbrev twoPathCleaned (k : ℕ) (A : SimpleGraph (Fin 3 × V)) : SimpleGraph V :=
  G.deleteEdges (twoPathDeletions G k A)

lemma twoPathCleaned_le (k : ℕ) (A : SimpleGraph (Fin 3 × V)) : twoPathCleaned G k A ≤ G :=
  sdiff_le

private lemma mem_twoPathDeletions {k : ℕ} {A : SimpleGraph (Fin 3 × V)}
    {p : (Fin 3 × V) × (Fin 3 × V)} {e : Sym2 V}
    (hp : (twoPathAux G k).Adj p.1 p.2) (hmiss : ¬A.Adj p.1 p.2)
    (he : e ∈ deletionFiber G k p) : e ∈ twoPathDeletions G k A := by
  classical
  apply mem_biUnion.mpr
  exact ⟨p, mem_filter.mpr ⟨mem_univ _, hp, hmiss⟩, he⟩

/-- No surviving source wedge has original codegree at most k. -/
lemma twoPathCleaned_wedge_codegree {k : ℕ} {A : SimpleGraph (Fin 3 × V)}
    (hA : A.CliqueFree 3) {u w v : V} (huv : u ≠ v)
    (huw : (twoPathCleaned G k A).Adj u w)
    (hwv : (twoPathCleaned G k A).Adj w v) :
    k < (G.neighborFinset u ∩ G.neighborFinset v).card := by
  classical
  obtain ⟨huwG, huwD⟩ := deleteEdges_adj.mp huw
  obtain ⟨hwvG, hwvD⟩ := deleteEdges_adj.mp hwv
  by_contra hnot
  have hlow : lowCodegree G k u v := ⟨huv, Nat.le_of_not_gt hnot⟩
  have h01 : A.Adj (0, u) (1, w) := by
    by_contra hmiss
    apply huwD
    apply mem_twoPathDeletions G (p := ((0, u), (1, w))) ((twoPathAux_adj_01 G).mpr huwG) hmiss
    simp [deletionFiber]
  have h12 : A.Adj (1, w) (2, v) := by
    by_contra hmiss
    apply hwvD
    apply mem_twoPathDeletions G (p := ((1, w), (2, v))) ((twoPathAux_adj_12 G).mpr hwvG) hmiss
    simp [deletionFiber]
  have h02 : A.Adj (0, u) (2, v) := by
    by_contra hmiss
    apply huwD
    apply mem_twoPathDeletions G (p := ((0, u), (2, v))) ((twoPathAux_adj_02 G).mpr hlow) hmiss
    simp only [deletionFiber, hlow, and_self, ↓reduceIte]
    apply mem_image.mpr
    refine ⟨w, ?_, rfl⟩
    simp [huwG, hwvG.symm]
  exact hA {(0, u), (1, w), (2, v)} (is3Clique_triple_iff.mpr ⟨h01, h02, h12⟩)


lemma card_missingAuxPairs {k : ℕ} {A : SimpleGraph (Fin 3 × V)}
    [DecidableRel A.Adj] (hA : A ≤ twoPathAux G k) :
    ((missingAuxPairs G k A).card : ℝ) =
      2 * ((twoPathAux G k).edgeFinset.card - (A.edgeFinset.card : ℝ)) := by
  classical
  let U := univ.filter (fun p : (Fin 3 × V) × (Fin 3 × V) => (twoPathAux G k).Adj p.1 p.2)
  let T := univ.filter (fun p : (Fin 3 × V) × (Fin 3 × V) => A.Adj p.1 p.2)
  have hsub : T ⊆ U := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, hA (mem_filter.mp hp).2⟩
  have hD : missingAuxPairs G k A = U \ T := by
    ext p
    simp [missingAuxPairs, U, T]
  have hcount : (missingAuxPairs G k A).card + 2 * A.edgeFinset.card =
      2 * (twoPathAux G k).edgeFinset.card := by
    rw [hD, two_mul_card_edgeFinset, two_mul_card_edgeFinset]
    exact card_sdiff_add_card_eq_card hsub
  have hR : ((missingAuxPairs G k A).card : ℝ) + 2 * A.edgeFinset.card =
      2 * (twoPathAux G k).edgeFinset.card := by exact_mod_cast hcount
  linarith

lemma twoPathCleaned_loss_le {k : ℕ} {A : SimpleGraph (Fin 3 × V)}
    [DecidableRel A.Adj] (hA : A ≤ twoPathAux G k) :
    (G.edgeFinset.card : ℝ) - (twoPathCleaned G k A).edgeFinset.card ≤
      2 * (k + 1 : ℝ) * ((twoPathAux G k).edgeFinset.card - (A.edgeFinset.card : ℝ)) := by
  have hs : G.edgeFinset.card ≤ (twoPathCleaned G k A).edgeFinset.card +
      (twoPathDeletions G k A).card := by
    have hE : (twoPathCleaned G k A).edgeFinset.card =
        (G.edgeFinset \ twoPathDeletions G k A).card := by
      have h := congrArg Finset.card
        (edgeFinset_deleteEdges (G := G) (twoPathDeletions G k A))
      simpa only [twoPathCleaned, SimpleGraph.edgeFinset, Set.toFinset_card,
        ← Nat.card_eq_fintype_card] using h
    rw [hE]
    exact card_le_card_sdiff_add_card
  have hsR : (G.edgeFinset.card : ℝ) ≤ (twoPathCleaned G k A).edgeFinset.card +
      (twoPathDeletions G k A).card := by exact_mod_cast hs
  have hbound : ((twoPathDeletions G k A).card : ℝ) ≤
      (missingAuxPairs G k A).card * (k + 1 : ℝ) := by
    exact_mod_cast card_twoPathDeletions_le G k A
  rw [card_missingAuxPairs G hA] at hbound
  nlinarith

lemma twoPathCleaned_robust {k : ℕ} {A : SimpleGraph (Fin 3 × V)}
    (hA : A.CliqueFree 3) : RobustAtLength G (twoPathCleaned G k A) 2 k := by
  apply robustAtLength_two_of_codegree
  intro u v huv hp
  obtain ⟨p, hp⟩ := hp
  cases p with
  | nil => simp at hp
  | cons h₁ p =>
    cases p with
    | nil => simp at hp
    | cons h₂ p =>
      cases p with
      | nil => exact twoPathCleaned_wedge_codegree G hA huv h₁ h₂
      | cons _ p => simp only [Walk.length_cons] at hp; omega


/-- Triangle removal gives robust two-path cleanup with its entire edge loss
charged back to the original source graph. -/
theorem exists_twoPathCleanup_of_small_triangles {k : ℕ} {η : ℝ} (hη : 0 < η)
    (hsmall : (k : ℝ) * (Fintype.card V : ℝ) ^ 2 <
      triangleRemovalBound (η / (18 * (k + 1))) * (3 * (Fintype.card V : ℝ)) ^ 3) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧
      (G.edgeFinset.card : ℝ) - H.edgeFinset.card < η * (Fintype.card V : ℝ) ^ 2 ∧
      RobustAtLength G H 2 k := by
  classical
  have htri : (((twoPathAux G k).cliqueFinset 3).card : ℝ) <
      triangleRemovalBound (η / (18 * (k + 1))) * (Fintype.card (Fin 3 × V) : ℝ) ^ 3 := by
    have hc : (((twoPathAux G k).cliqueFinset 3).card : ℝ) ≤
        (k : ℝ) * (Fintype.card V : ℝ) ^ 2 := by
      exact_mod_cast card_triangles_twoPathAux_le G k
    apply hc.trans_lt
    simpa [Fintype.card_prod] using hsmall
  obtain ⟨A, hA, instA, hloss, hfree⟩ := triangle_removal htri
  letI := instA
  refine ⟨twoPathCleaned G k A, inferInstance, twoPathCleaned_le G k A, ?_, twoPathCleaned_robust G hfree⟩
  apply (twoPathCleaned_loss_le G hA).trans_lt
  have hmul := mul_lt_mul_of_pos_left hloss (show (0 : ℝ) < 2 * (k + 1) by positivity)
  have hscale : 2 * (k + 1 : ℝ) *
      (η / (18 * (k + 1)) * (Fintype.card (Fin 3 × V) ^ 2 : ℕ)) =
      η * (Fintype.card V : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring
  rwa [hscale] at hmul


/-- Uniform robust length-two cleanup for every finite source graph. The
order threshold depends only on the requested edge loss and forbidden-set
budget, and not on the host or its endpoint choices. -/
theorem exists_robust_two_cleanup (η : ℝ) (hη : 0 < η) (k : ℕ) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (G' : SimpleGraph W) [DecidableRel G'.Adj], N ≤ Fintype.card W →
      ∃ H : SimpleGraph W, ∃ _ : DecidableRel H.Adj, H ≤ G' ∧
        (G'.edgeFinset.card : ℝ) - H.edgeFinset.card < η * (Fintype.card W : ℝ) ^ 2 ∧
        RobustAtLength G' H 2 k := by
  let δ := triangleRemovalBound (η / (18 * (k + 1)))
  have hδ : 0 < δ := triangleRemovalBound_pos (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((k : ℝ) / (27 * δ))
  refine ⟨max 1 N₀, ?_⟩
  intro W instW instEq G' instG hn
  apply exists_twoPathCleanup_of_small_triangles G' hη
  have hNN : N₀ ≤ Fintype.card W := (le_max_right 1 N₀).trans hn
  have hNpos : 0 < Fintype.card W := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left 1 N₀).trans hn)
  have hnR : (0 : ℝ) < Fintype.card W := by exact_mod_cast hNpos
  have hkn : (k : ℝ) < (Fintype.card W : ℝ) * (27 * δ) := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 27 * δ by positivity)).mp
    exact hN₀.trans_le (by exact_mod_cast hNN)
  have hmul := mul_lt_mul_of_pos_right hkn (pow_pos hnR 2)
  change (k : ℝ) * (Fintype.card W : ℝ) ^ 2 < δ * (3 * (Fintype.card W : ℝ)) ^ 3
  nlinarith only [hmul]

end Erdos809.Source
