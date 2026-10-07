module
public import Erdos809.LongOddCycles.FourPathCounting
public import Erdos809.LongOddCycles.ScalarBounds
public import Erdos809.Source.DegreePruning
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-!
# Exact four-paths and forbidden-vertex deletion

BCM Lemma 3.2 is implemented in three independent steps: finite neighborhood
counting, its scalar contradiction, and transfer after adding the endpoint edge.
-/

namespace Erdos809.LongOddCycles

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A simple path of length at least two cannot contain the edge between its
endpoints. This is the reason adding that edge is harmless for the four-path lemma. -/
lemma endpoint_edge_not_mem_of_isPath {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) (hlen : 2 ≤ p.length) : s(x, y) ∉ p.edges := by
  intro he
  have hs := hp.eq_snd_of_mem_edges he
  have hget : p.getVert 1 = y := hs.symm
  have := (hp.getVert_eq_end_iff (by omega : 1 ≤ p.length)).mp hget
  omega

/-- Adding only the endpoint edge does not create any new simple four-path
between the endpoints. The walk is transferred edge by edge back to the source. -/
lemma hasAvoidingPath_four_sup_edge_iff {x y : V} (hxy : x ≠ y) :
    Source.HasAvoidingPath (G ⊔ SimpleGraph.edge x y) x y 4 ∅ ↔
      Source.HasAvoidingPath G x y 4 ∅ := by
  constructor
  · rintro ⟨p, hp, hlen, _⟩
    have hedge : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      have he' := p.edges_subset_edgeSet he
      rw [SimpleGraph.edgeSet_sup, SimpleGraph.edge_edgeSet_of_ne hxy] at he'
      rcases he' with h | h
      · exact h
      · have heq : e = s(x, y) := h
        subst e
        exact (endpoint_edge_not_mem_of_isPath hp (by omega) he).elim
    refine ⟨p.transfer G hedge, hp.transfer hedge, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.length_transfer] using hlen
    · simp
  · rintro ⟨p, hp, hlen, _⟩
    refine ⟨p.map (.ofLE le_sup_left), p.map_isPath_of_injective (Function.injective_id) hp, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.length_map] using hlen
    · simp

/-- Lift an avoiding path in the induced complement of a forbidden set. -/
lemma avoidingPath_of_induce_compl {x y : V} {L : ℕ} (F : Finset V)
    (hx : x ∉ F) (hy : y ∉ F)
    (hpath : Source.HasAvoidingPath (G.induce (↑(univ \ F) : Set V))
      ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ L ∅) :
    Source.HasAvoidingPath G x y L F := by
  obtain ⟨p, hp, hlen, _⟩ := hpath
  have hqlen : (p.map (SimpleGraph.Embedding.induce _).toHom).length = L := by
    rw [SimpleGraph.Walk.length_map, hlen]
  have hqsupp : ∀ z ∈ (p.map (SimpleGraph.Embedding.induce _).toHom).support, z ∉ F := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, _, rfl⟩ := hz
    simpa using w.property
  exact ⟨p.map (SimpleGraph.Embedding.induce _).toHom,
    p.map_isPath_of_injective Subtype.val_injective hp, hqlen, hqsupp⟩

/-- The exact simple-graph density ceiling, stated over the reals. -/
lemma card_edgeFinset_le_real_clique_bound :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
  have hsum : ∑ v : V, (G.degree v : ℝ) ≤
      ∑ _v : V, ((Fintype.card V : ℝ) - 1) := by
    apply Finset.sum_le_sum
    intro v _
    have hd : (G.degree v : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast G.degree_lt_card_verts v
    linarith
  have handshake := congrArg (fun z : ℕ => (z : ℝ)) G.sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at handshake
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  nlinarith

/-- The repaired integral minimum-degree parameter in BCM Lemma 3.2.
The hypothesis forces at least six vertices; integral degrees then upgrade the
strict lower bound greater than two to the needed bound of three. -/
lemma fourPath_repaired_parameter
    (hm : (Fintype.card V : ℝ)^2 / 4 + 4 ≤ (G.edgeFinset.card : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2 ≤
      (G.degree v : ℝ)) :
    6 ≤ (Fintype.card V : ℝ) ∧
      ∀ v, max 3 ((Fintype.card V : ℝ) / 2 -
        Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2) ≤
        (G.degree v : ℝ) := by
  have hmupper := card_edgeFinset_le_real_clique_bound (G := G)
  have hn : 6 ≤ (Fintype.card V : ℝ) := by
    by_contra h
    have hn6 : Fintype.card V < 6 := by exact_mod_cast (show (Fintype.card V : ℝ) < 6 by linarith)
    have hn5 : Fintype.card V ≤ 5 := by omega
    have hn0 : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have hn5R : (Fintype.card V : ℝ) ≤ 5 := by exact_mod_cast hn5
    nlinarith [mul_nonneg hn0 (by linarith : 0 ≤ 5 - (Fintype.card V : ℝ))]
  refine ⟨hn, fun v => max_le ?_ (hdegree v)⟩
  have ha := fourPathThreshold_pos (Fintype.card V : ℝ) (G.edgeFinset.card : ℝ)
    (by linarith) hmupper
  have hd : 2 < (G.degree v : ℝ) := lt_of_lt_of_le ha (hdegree v)
  exact_mod_cast (show 3 ≤ G.degree v by exact_mod_cast hd)

/-- The adjacent, degree-ordered case of BCM Lemma 3.2. -/
lemma bcm_four_path_of_adj_of_degree_le {x y : V}
    (hm : (Fintype.card V : ℝ)^2 / 4 + 4 ≤ (G.edgeFinset.card : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2 ≤
      (G.degree v : ℝ)) (hxy : G.Adj x y) (horder : G.degree y ≤ G.degree x) :
    Source.HasAvoidingPath G x y 4 ∅ := by
  by_contra hno
  obtain ⟨hn, hdeg⟩ := fourPath_repaired_parameter hm hdegree
  let b := max 3 ((Fintype.card V : ℝ) / 2 -
    Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2)
  have hcount := no_four_path_degree_sum_bound hxy horder hno b (le_max_left _ _)
    (fourPathParameter_le_half _ _ hn hm) hdeg
  exact fourPathPolynomial_contradiction _ _ hn hm hcount

/-- The adjacent-endpoint case, with no chosen degree orientation. -/
lemma bcm_four_path_of_adj {x y : V}
    (hm : (Fintype.card V : ℝ)^2 / 4 + 4 ≤ (G.edgeFinset.card : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2 ≤
      (G.degree v : ℝ)) (hxy : G.Adj x y) :
    Source.HasAvoidingPath G x y 4 ∅ := by
  rcases le_total (G.degree y) (G.degree x) with horder | horder
  · exact bcm_four_path_of_adj_of_degree_le hm hdegree hxy horder
  · obtain ⟨p, hp, hlen, _⟩ := bcm_four_path_of_adj_of_degree_le hm hdegree hxy.symm horder
    refine ⟨p.reverse, hp.reverse, ?_, ?_⟩
    · simpa using hlen
    · simp

set_option maxHeartbeats 200000 in
/-- BCM Lemma 3.2, with the real/integer repair: the stated density and minimum
degree guarantee a simple path of exactly four edges between distinct endpoints. -/
theorem bcm_four_path {x y : V}
    (hm : (Fintype.card V : ℝ)^2 / 4 + 4 ≤ (G.edgeFinset.card : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2 ≤
      (G.degree v : ℝ)) (hxy : x ≠ y) : Source.HasAvoidingPath G x y 4 ∅ := by
  let H := G ⊔ SimpleGraph.edge x y
  letI : Fintype H.edgeSet := H.fintypeEdgeSet
  have hGH : G ≤ H := le_sup_left
  have hmmono : (G.edgeFinset.card : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have hmH : (Fintype.card V : ℝ)^2 / 4 + 4 ≤ (H.edgeFinset.card : ℝ) := hm.trans hmmono
  have hdegreeH : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((H.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4) + 2 ≤
      (H.degree v : ℝ) := by
    intro v
    have hroot := Real.sqrt_le_sqrt (sub_le_sub_right hmmono ((Fintype.card V : ℝ)^2 / 4))
    have hdegmono : (G.degree v : ℝ) ≤ (H.degree v : ℝ) := by
      exact_mod_cast G.degree_le_of_le hGH (v := v)
    have hv := hdegree v
    linarith
  have hxyH : H.Adj x y := Or.inr (by simp [SimpleGraph.edge_adj, hxy])
  exact (hasAvoidingPath_four_sup_edge_iff (G := G) hxy).mp
    (bcm_four_path_of_adj (G := H) hmH hdegreeH hxyH)

/-- The edge-loss and degree-loss estimates preserve the exact hypotheses of
BCM's four-path lemma after deleting a bounded forbidden set. -/
lemma fourPath_induce_compl_hypotheses (r : ℕ) (F : Finset V)
    (hF : F.card + 2 ≤ r)
    (hsurplus : 4 ≤ (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4 -
      r * (Fintype.card V : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4 -
        r * (Fintype.card V : ℝ)) + r ≤ (G.degree v : ℝ)) :
    let W := (↑(univ \ F) : Set V)
    let H := G.induce W
    (Fintype.card W : ℝ)^2 / 4 + 4 ≤ (H.edgeFinset.card : ℝ) ∧
      ∀ v, (Fintype.card W : ℝ) / 2 -
        Real.sqrt ((H.edgeFinset.card : ℝ) - (Fintype.card W : ℝ)^2 / 4) + 2 ≤
        (H.degree v : ℝ) := by
  classical
  let W := (↑(univ \ F) : Set V)
  let H := G.induce W
  have hn : (Fintype.card W : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective (fun v : W => (v : V)) Subtype.val_injective
  have hn0 : 0 ≤ (Fintype.card W : ℝ) := Nat.cast_nonneg _
  have hnV : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hFcast : (F.card : ℝ) + 2 ≤ r := by exact_mod_cast hF
  have hloss : (G.edgeFinset.card : ℝ) - (H.edgeFinset.card : ℝ) ≤
      (F.card : ℝ) * Fintype.card V := Source.edge_loss_induce_compl_le G F
  have hsmall : (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4 -
      r * (Fintype.card V : ℝ) ≤
      (H.edgeFinset.card : ℝ) - (Fintype.card W : ℝ)^2 / 4 := by
    have hsquares := mul_self_le_mul_self hn0 hn
    nlinarith [mul_nonneg (by linarith : 0 ≤ (r : ℝ) - F.card) hnV]
  constructor
  · change (Fintype.card W : ℝ)^2 / 4 + 4 ≤ (H.edgeFinset.card : ℝ)
    linarith
  · intro v
    change (Fintype.card W : ℝ) / 2 -
        Real.sqrt ((H.edgeFinset.card : ℝ) - (Fintype.card W : ℝ)^2 / 4) + 2 ≤
        (H.degree v : ℝ)
    have hroot := Real.sqrt_le_sqrt hsmall
    have hd : (G.degree v.val : ℝ) ≤ (H.degree v : ℝ) + F.card := by
      exact_mod_cast Source.degree_induce_compl_lower G F v
    have hv := hdegree v.val
    linarith

/-- Robust four-paths obtained by deleting the forbidden vertices first.
The budget includes the two units required by the exact four-path degree bound. -/
theorem bcm_four_path_avoiding {x y : V} (r : ℕ) (F : Finset V)
    (hF : F.card + 2 ≤ r) (hx : x ∉ F) (hy : y ∉ F) (hxy : x ≠ y)
    (hsurplus : 4 ≤ (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4 -
      r * (Fintype.card V : ℝ))
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)^2 / 4 -
        r * (Fintype.card V : ℝ)) + r ≤ (G.degree v : ℝ)) :
    Source.HasAvoidingPath G x y 4 F := by
  classical
  obtain ⟨hm, hdeg⟩ := fourPath_induce_compl_hypotheses r F hF hsurplus hdegree
  apply avoidingPath_of_induce_compl F hx hy
  apply bcm_four_path hm hdeg
  intro heq
  exact hxy (congrArg Subtype.val heq)

end Erdos809.LongOddCycles
