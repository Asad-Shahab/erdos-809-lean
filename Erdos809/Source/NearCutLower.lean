import Erdos809.Source.NearCutWitness
import Erdos809.Source.Potential
import Mathlib.Tactic.FieldSimp

/-!
# The quantitative near-cut lower bound

This module assembles the source counting and seven-cycle results. The exact
integer one-edge surplus is related explicitly to strict real quarter density.
-/

namespace Erdos809.Source

open SimpleGraph Finset

/-- The integral Mantel threshold plus one is exactly strict real quarter density. -/
theorem exactThreshold_le_iff_real_excess (n m : ℕ) :
    exactThreshold n ≤ m ↔ (n : ℝ) ^ 2 / 4 < m := by
  constructor
  · intro h
    have hq : n * n / 4 < m := by unfold exactThreshold at h; omega
    have hi := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mp hq
    have hr : (n : ℝ) * n < m * 4 := by exact_mod_cast hi
    nlinarith only [hr]
  · intro h
    have hr : (n : ℝ) * n < m * 4 := by nlinarith only [h]
    have hi : n * n < m * 4 := by exact_mod_cast hr
    have hq := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr hi
    unfold exactThreshold
    omega

variable {V K : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem real_excess_of_exactThreshold
    (he : exactThreshold (Fintype.card V) ≤ EdgeCount G) :
    (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card := by
  have h := (exactThreshold_le_iff_real_excess (Fintype.card V) (EdgeCount G)).mp he
  simpa only [EdgeCount, Nat.card_eq_fintype_card, ← edgeFinset_card] using h

/-- Either orientation of the internal trigger gives the same palette estimate. -/
theorem nearCut_palette_lower_of_either_trigger {P Q T : Finset V} {τ n : ℝ}
    (hPQ : Disjoint P Q)
    (hpar : NearCutParameters τ n P.card Q.card T.card)
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    (htypQ : ∀ y ∈ Q, y ∉ T → (crossDefect G P y : ℝ) ≤ τ * n)
    (htrigger : NearCutTrigger G P Q T ∨ NearCutTrigger G Q P T)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (1 / 8 - 9 * τ / 8) * n ^ 2 ≤ (usedColors c : ℝ) := by
  rcases htrigger with h | h
  · exact nearCut_palette_lower_of_trigger hPQ.symm hpar.symm htypQ htypP h c hc
  · exact nearCut_palette_lower_of_trigger hPQ hpar htypP htypQ h c hc

/-- Any large cut in an eligible graph gives the quantitative near-cut bound.
The proof chooses a maximum cut only after the source host is fixed. -/
theorem nearCut_palette_lower_of_large_cut {τ : ℝ}
    (hτpos : 0 < τ) (hτle : τ ≤ 1 / 32)
    (hnlarge : 8 / τ ^ 3 ≤ (Fintype.card V : ℝ))
    (helig : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card)
    (hcut : ∃ A : Finset V, (1 / 4 - τ ^ 3) * (Fintype.card V : ℝ) ^ 2 ≤
      (G.interedges A Aᶜ).card)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (1 / 8 - 9 * τ / 8) * (Fintype.card V : ℝ) ^ 2 ≤ (usedColors c : ℝ) := by
  obtain ⟨P, hmax⟩ := exists_maximum_cut G
  obtain ⟨A, hA⟩ := hcut
  have hPcut : (1 / 4 - τ ^ 3) * (Fintype.card V : ℝ) ^ 2 ≤
      (G.interedges P Pᶜ).card := hA.trans (Nat.cast_le.mpr (hmax A))
  have hPQ : Disjoint P Pᶜ := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (mem_compl.mp hx') hx
  have hpar := parameters_of_large_cut G hPQ (show P ∪ Pᶜ = univ by simp)
    hτpos hτle hnlarge hPcut
  have htrigger := maximum_cut_has_trigger G hmax helig hpar
  exact nearCut_palette_lower_of_either_trigger hPQ hpar
    (fun _ hx hxT ↦ typical_of_not_cutBad_left G hx hxT)
    (fun _ hy hyT ↦ typical_of_not_cutBad_right G hy hyT) htrigger c hc

/-- The manuscript's epsilon form, with the exact integral one-edge excess,
all sufficiently large orders and arbitrary original color labels. -/
theorem nearCut_palette_lower {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 16)
    (hnlarge : 64 / ε ^ 3 ≤ (Fintype.card V : ℝ))
    (helig : exactThreshold (Fintype.card V) ≤ EdgeCount G)
    (hcut : ∃ A : Finset V, (1 / 4 - ε ^ 3 / 8) * (Fintype.card V : ℝ) ^ 2 ≤
      (G.interedges A Aᶜ).card)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (1 / 8 - ε) * (Fintype.card V : ℝ) ^ 2 ≤ (usedColors c : ℝ) := by
  have hscale : 8 / (ε / 2) ^ 3 = 64 / ε ^ 3 := by
    field_simp [ne_of_gt hε]
    ring
  have hnτ : 8 / (ε / 2) ^ 3 ≤ (Fintype.card V : ℝ) := by
    rwa [hscale]
  have hcutτ : ∃ A : Finset V, (1 / 4 - (ε / 2) ^ 3) * (Fintype.card V : ℝ) ^ 2 ≤
      (G.interedges A Aᶜ).card := by
    obtain ⟨A, hA⟩ := hcut
    refine ⟨A, ?_⟩
    simpa only [show (ε / 2) ^ 3 = ε ^ 3 / 8 by ring] using hA
  have hbound := nearCut_palette_lower_of_large_cut (G := G)
    (show 0 < ε / 2 by positivity) (show ε / 2 ≤ 1 / 32 by linarith)
    hnτ (real_excess_of_exactThreshold helig) hcutτ c hc
  have hcoef : (1 / 8 - ε) ≤ (1 / 8 - 9 * (ε / 2) / 8) := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans hbound

/-- A cut contains at most one quarter of all ordered pairs of vertices. -/
theorem cut_card_le_quarter (A : Finset V) :
    ((G.interedges A Aᶜ).card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
  have hparts : (A.card : ℝ) + Aᶜ.card = Fintype.card V := by
    exact_mod_cast card_add_card_compl A
  have hcap : ((G.interedges A Aᶜ).card : ℝ) ≤ (A.card : ℝ) * Aᶜ.card := by
    exact_mod_cast G.card_interedges_le_mul A Aᶜ
  nlinarith only [hparts, hcap, sq_nonneg ((A.card : ℝ) - Aᶜ.card)]

/-- In the near-cut branch the source palette pays the full potential with
the stated error, including the possible excess above one quarter density. -/
theorem nearCut_potential_lower_of_cut_deficit {ε ρ : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1 / 16) (hρ : ρ ≤ ε ^ 3 / 8)
    (hnlarge : 64 / ε ^ 3 ≤ (Fintype.card V : ℝ))
    (helig : exactThreshold (Fintype.card V) ≤ EdgeCount G)
    (A : Finset V)
    (hdeficit : (G.edgeFinset.card : ℝ) - (G.interedges A Aᶜ).card ≤
      ρ * (Fintype.card V : ℝ) ^ 2)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    potential (Fintype.card V) G.edgeFinset.card -
      (ε + 3 * ρ / 2) * (Fintype.card V : ℝ) ^ 2 ≤ (usedColors c : ℝ) := by
  have hsq : 0 ≤ (Fintype.card V : ℝ) ^ 2 := sq_nonneg _
  have hreal := real_excess_of_exactThreshold helig
  have hρscaled := mul_le_mul_of_nonneg_right hρ hsq
  have hcut : (1 / 4 - ε ^ 3 / 8) * (Fintype.card V : ℝ) ^ 2 ≤
      (G.interedges A Aᶜ).card := by
    nlinarith only [hreal, hdeficit, hρscaled]
  have hpalette := nearCut_palette_lower hε hεle hnlarge helig ⟨A, hcut⟩ c hc
  have hcap := cut_card_le_quarter (G := G) A
  unfold potential
  nlinarith only [hpalette, hcap, hdeficit]

end Erdos809.Source
