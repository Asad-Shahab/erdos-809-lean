import Erdos809.Source.Potential
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.ByContra

/-!
# Finite fixed-margin peeling

The graph theorem below is proved by minimizing the order of an induced
subgraph satisfying an explicit potential invariant. This replaces an
algorithmic deletion loop with a finite well-founded argument.
-/

noncomputable section

namespace Erdos809.Source

universe u

private def reserve (n γ : ℝ) : ℝ := (3 * γ / 4) * n * (n + 1) + 7 * n / 4

private lemma reserve_nonneg {n γ : ℝ} (hn : 0 ≤ n) (hγ : 0 ≤ γ) :
    0 ≤ reserve n γ := by unfold reserve; positivity

private lemma deletion_invariant {n N m d γ : ℝ}
    (hp : peelingBound n γ + reserve N γ ≤ potential N m)
    (hd : d < (1 / 3 + γ) * N + 1) :
    peelingBound n γ + reserve (N - 1) γ ≤ potential (N - 1) (m - d) := by
  have h := potential_delete_lower (m := m) hd
  unfold reserve at *
  nlinarith

private lemma edge_count_le_half_square {W : Type u} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (H.edgeFinset.card : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 / 2 := by
  classical
  have hs : (∑ v : W, H.degree v) ≤ ∑ _v : W, Fintype.card W := by
    exact Finset.sum_le_sum fun v _ => (H.degree_lt_card_verts v).le
  rw [H.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  have hs' : (2 : ℝ) * H.edgeFinset.card ≤ (Fintype.card W : ℝ) * Fintype.card W := by
    exact_mod_cast hs
  nlinarith

private lemma order_gt_third {n h m γ : ℝ}
    (hn : 64 ≤ n) (hh : 0 ≤ h) (hγ : γ ≤ 1 / 48)
    (hm : m ≤ h ^ 2 / 2) (hp : peelingBound n γ ≤ potential h m) : n / 3 < h := by
  by_contra hnot
  have hh' : h ≤ n / 3 := le_of_not_gt hnot
  have hpn := peelingBound_ge_numeric (by linarith : 0 ≤ n) hγ
  have hsq : h ^ 2 ≤ n ^ 2 / 9 := by nlinarith [sq_nonneg (n / 3 - h)]
  have hlarge : 64 * n ≤ n ^ 2 := by nlinarith
  unfold potential at hp
  nlinarith

/-- Every eligible finite simple graph has an induced subgraph retaining
strict eligibility, order greater than one third, the required minimum
degree margin, and the full potential lower bound. The result applies to
all eligible graphs, including the exact single-edge threshold. -/
theorem exists_peeled_graph {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {γ : ℝ}
    (hn : 64 ≤ Fintype.card V) (hγpos : 0 < γ) (hγ : γ ≤ 1 / 48)
    (hG : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      Nonempty (H ↪g G) ∧
      (Fintype.card V : ℝ) / 3 < Fintype.card W ∧
      (Fintype.card W : ℝ) ^ 2 / 4 < H.edgeFinset.card ∧
      (∀ v : W, (1 / 3 + γ) * Fintype.card W + 1 ≤ H.degree v) ∧
      peelingBound (Fintype.card V) γ ≤ potential (Fintype.card W) H.edgeFinset.card := by
  classical
  let Good : ℕ → Prop := fun k =>
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      Fintype.card W = k ∧ Nonempty (H ↪g G) ∧
      (Fintype.card W : ℝ) ^ 2 / 4 < H.edgeFinset.card ∧
      peelingBound (Fintype.card V) γ + reserve (Fintype.card W) γ ≤
        potential (Fintype.card W) H.edgeFinset.card
  have hgood : ∃ k, Good k := by
    refine ⟨Fintype.card V, V, inferInstance, G, inferInstance, rfl, ⟨.refl⟩, hG, ?_⟩
    have hp := potential_initial hG
    unfold peelingBound reserve
    linarith
  obtain ⟨W, instW, H, instH, hk, hHG, hHeligible, hHinv⟩ := Nat.find_spec hgood
  letI := instW
  letI := instH
  have hbase : peelingBound (Fintype.card V) γ ≤ potential (Fintype.card W) H.edgeFinset.card :=
    le_trans (le_add_of_nonneg_right (reserve_nonneg (Nat.cast_nonneg _) hγpos.le)) hHinv
  have horder : (Fintype.card V : ℝ) / 3 < Fintype.card W :=
    order_gt_third (by exact_mod_cast hn) (Nat.cast_nonneg _) hγ
      (edge_count_le_half_square H) hbase
  refine ⟨W, instW, H, instH, hHG, horder, hHeligible, ?_, hbase⟩
  intro v
  by_contra hnot
  have hd : (H.degree v : ℝ) < (1 / 3 + γ) * Fintype.card W + 1 := lt_of_not_ge hnot
  let W' : Type u := ({v}ᶜ : Set W)
  let H' : SimpleGraph W' := H.induce {v}ᶜ
  have hcard : Fintype.card W' = Fintype.card W - 1 := by
    calc
      Fintype.card W' = (Finset.univ.erase v).card :=
        Fintype.card_of_subtype _ (by intro w; simp)
      _ = Fintype.card W - 1 := by simp
  have hWpos : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcardR : (Fintype.card W' : ℝ) = (Fintype.card W : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ Fintype.card W)]
    norm_num
  have hedges : H'.edgeFinset.card = H.edgeFinset.card - H.degree v := by
    simpa only [H', SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] using
      (H.card_edgeFinset_induce_compl_singleton v).trans (H.card_edgeFinset_deleteIncidenceSet v)
  have hedgesR : (H'.edgeFinset.card : ℝ) = (H.edgeFinset.card : ℝ) - H.degree v := by
    rw [hedges, Nat.cast_sub (H.degree_le_card_edgeFinset (v := v))]
  have hH'inv : peelingBound (Fintype.card V) γ + reserve (Fintype.card W') γ ≤
      potential (Fintype.card W') H'.edgeFinset.card := by
    rw [hcardR, hedgesR]
    exact deletion_invariant hHinv hd
  have hlarge : 64 / 3 < (Fintype.card W : ℝ) := by
    have hnR : (64 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
    linarith
  have hH'eligible : (Fintype.card W' : ℝ) ^ 2 / 4 < H'.edgeFinset.card := by
    have hs := surplus_delete_strict (m := H.edgeFinset.card) hγ hlarge hd
    rw [hcardR, hedgesR]
    unfold quarterSurplus at hs
    linarith
  have hnew : Good (Fintype.card W') := by
    obtain ⟨e⟩ := hHG
    refine ⟨W', inferInstance, H', inferInstance, rfl, ?_, hH'eligible, hH'inv⟩
    exact ⟨(SimpleGraph.Embedding.induce {v}ᶜ).trans e⟩
  have hmin := Nat.find_min' hgood hnew
  rw [← hk] at hmin
  omega

end Erdos809.Source
