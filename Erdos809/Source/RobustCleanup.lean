import Erdos809.Source.TwoPathCleanup
import Erdos809.Source.RegularityCleanup

/-!
# Uniform robust source-path cleanup

The independent length-two and length-three/five cleanups are intersected.
Every lifted path remains a path in the original source graph.
-/

noncomputable section

namespace Erdos809.Source

open SimpleGraph Finset

universe u

lemma edge_loss_inf_le {V : Type*} [Fintype V] [DecidableEq V]
    {G H J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hH : H ≤ G) (hJ : J ≤ G) :
    (G.edgeFinset.card : ℝ) - (H ⊓ J).edgeFinset.card ≤
      ((G.edgeFinset.card : ℝ) - H.edgeFinset.card) +
        ((G.edgeFinset.card : ℝ) - J.edgeFinset.card) := by
  have hsub : H.edgeFinset ∪ J.edgeFinset ⊆ G.edgeFinset :=
    union_subset (edgeFinset_mono hH) (edgeFinset_mono hJ)
  have hcard := card_le_card hsub
  have hsum := card_union_add_card_inter H.edgeFinset J.edgeFinset
  have hsumR : ((H.edgeFinset ∪ J.edgeFinset).card : ℝ) +
      (H.edgeFinset ∩ J.edgeFinset).card = H.edgeFinset.card + J.edgeFinset.card := by
    exact_mod_cast hsum
  have hcardR : ((H.edgeFinset ∪ J.edgeFinset).card : ℝ) ≤ G.edgeFinset.card := by
    exact_mod_cast hcard
  rw [edgeFinset_inf]
  linarith

/-- For every edge-loss tolerance and fixed forbidden-set budget there is
one order threshold, uniform over all hosts, endpoints and retained walks,
for exact-length simple source paths of lengths two, three and five. -/
theorem exists_robust_cleanup (η : ℝ) (hη : 0 < η) (k : ℕ) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧
        (G.edgeFinset.card : ℝ) - H.edgeFinset.card < η * (Fintype.card V : ℝ) ^ 2 ∧
        RobustAtLength G H 2 k ∧ RobustAtLength G H 3 k ∧ RobustAtLength G H 5 k := by
  obtain ⟨N₂, h₂⟩ := exists_robust_two_cleanup (η / 2) (by positivity) k
  obtain ⟨N₃₅, h₃₅⟩ := exists_robust_three_five_cleanup (η / 2) (by positivity) k
  refine ⟨max N₂ N₃₅, ?_⟩
  intro V instV instEq G instG hn
  obtain ⟨H₂, inst₂, hH₂, hloss₂, hrobust₂⟩ := h₂ V G ((le_max_left _ _).trans hn)
  obtain ⟨H₃₅, inst₃₅, hH₃₅, hloss₃₅, hrobust₃, hrobust₅⟩ := h₃₅ V G ((le_max_right _ _).trans hn)
  letI := inst₂
  letI := inst₃₅
  refine ⟨H₂ ⊓ H₃₅, inferInstance, inf_le_left.trans hH₂, ?_,
    hrobust₂.mono inf_le_left, hrobust₃.mono inf_le_right, hrobust₅.mono inf_le_right⟩
  have hbound := edge_loss_inf_le hH₂ hH₃₅
  have hsum := add_lt_add hloss₂ hloss₃₅
  have hscale : η / 2 * (Fintype.card V : ℝ) ^ 2 +
      η / 2 * (Fintype.card V : ℝ) ^ 2 = η * (Fintype.card V : ℝ) ^ 2 := by ring
  rw [hscale] at hsum
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] using
    hbound.trans_lt hsum

end Erdos809.Source
