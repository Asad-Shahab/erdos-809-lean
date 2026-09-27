import Erdos809.Source.Peeling
import Erdos809.Source.RobustCleanup
import Erdos809.Source.DegreePruning
import Erdos809.Source.ColorClassCover
import Erdos809.Source.NearCutLower
import Erdos809.Source.CutTransport
import Erdos809.FreeSector
import Erdos809.WeightedCuts
import Erdos809.UniformWeights

/-!
# Explicit source reduction interfaces for the lower bound

This module assembles proved source reductions. Conditional conclusions name
their terminal or finite weighted hypotheses explicitly; they do not assert
that the finite CP theorem has been proved.
-/

noncomputable section

namespace Erdos809.Source

open SimpleGraph Finset

universe u

open Classical in
/-- The missing finite weighted theorem, stated as an explicit hypothesis.
Its domain is the actual outside-S edge set of the same full host G. It must
hold for every exact whole-pattern cover, not only a chosen optimal cover. -/
def WeightedStableCP : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : VertexWeights V), (∀ v, 0 < x.weight v) →
    ∀ δ ξ ρ : ℝ, 1 / 3 < δ → x.MinDegreeAtLeast G δ →
      0 ≤ ξ → 0 < ρ → ξ ≤ ρ / 2 →
      1 / 4 - ξ ≤ x.edgeMass G → ρ ≤ x.edgeMass G - x.maxCut G →
      ∀ (P : Type) [Fintype P] (edges : P → Finset (outsideSector G).edgeSet),
        (∀ p, (edges p : Set (outsideSector G).edgeSet).Pairwise
          (fun e f => Compatible G
            (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)
            (edgeLeft (outsideSector G) f) (edgeRight (outsideSector G) f))) →
        ∀ cover : ExactPatternCover
          (fun e : (outsideSector G).edgeSet =>
            x.capacity (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)) edges,
          3 * x.edgeMass G / 2 - 1 / 4 - 2 * ξ / ρ ≤ cover.cost

/-- An actual original-color cover of the pruned outside sector can be fed
to the explicitly assumed finite weighted theorem. No source color is dropped
from the objective when its retained class becomes empty. -/
theorem original_palette_of_weightedStableCP (hCP : WeightedStableCP)
    {V : Type u} [Fintype V] {W K : Type} [Fintype W] [DecidableEq W]
    {G H : SimpleGraph V} {J : SimpleGraph W} [DecidableRel J.Adj]
    (hHG : H ≤ G) (F : Copy J H) (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hr2 : RobustAtLength G H 2 5) (hr3 : RobustAtLength G H 3 5)
    (hr5 : RobustAtLength G H 5 5)
    (x : VertexWeights W) (hx : ∀ v, 0 < x.weight v)
    {δ ξ ρ w : ℝ} (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast J δ)
    (hξ : 0 ≤ ξ) (hρ : 0 < ρ) (hsmall : ξ ≤ ρ / 2)
    (hdensity : 1 / 4 - ξ ≤ x.edgeMass J) (hdeficit : ρ ≤ x.edgeMass J - x.maxCut J)
    (hw : 0 ≤ w) (hcapacity : ∀ u v, x.capacity u v = w) :
    3 * x.edgeMass J / 2 - 1 / 4 - 2 * ξ / ρ ≤ (usedColors c : ℝ) * w := by
  classical
  let E := (outsideSector J).edgeSet
  let u : E → W := edgeLeft (outsideSector J)
  let v : E → W := edgeRight (outsideSector J)
  have hedge (e : E) : J.Adj (u e) (v e) :=
    outsideSector_le J (edge_endpoints_adj (outsideSector J) e)
  have hinj : Function.Injective (fun e : E => s(u e, v e)) := by
    intro e f h
    apply Subtype.ext
    simpa only [u, v, edge_endpoints] using h
  have hout (e : E) : OnTriangle J (u e) ∨ OnTriangle J (v e) := by
    have he := (edge_endpoints_adj (outsideSector J) e).2
    simpa only [onTriangle_iff_not_triangleFree, not_and_or] using he
  let src : E → G.edgeSet := prunedSourceEdges hHG F u v hedge
  letI : Fintype (Set.range c) := Fintype.ofFinite _
  have hpattern (p : Set.range c) :
      (sourceColorClass c src p : Set E).Pairwise
        (fun e f => Compatible J (u e) (v e) (u f) (v f)) := by
    intro e he f hf hef
    exact (sourceColorClass_pattern_copy hHG F c hc hr2 hr3 hr5
      u v hedge hinj hout p he hf hef).2
  let cover : ExactPatternCover
      (fun e : E => x.capacity (u e) (v e)) (sourceColorClass c src) := {
    amount := fun _ => w
    nonneg := fun _ => hw
    covers := fun e => by
      rw [hcapacity]
      exact (sourceColorCover c src w hw).covers e
  }
  have hbound := hCP W J x hx δ ξ ρ hδ hmin hξ hρ hsmall hdensity hdeficit
    (Set.range c) (sourceColorClass c src) hpattern cover
  apply hbound.trans_eq
  exact sourceColorCover_cost c src w hw

/-- Uniform weights turn the finite weighted conclusion into the exact
ordinary retained-host potential estimate, with its full stability error. -/
theorem pruned_palette_of_weightedStableCP (hCP : WeightedStableCP)
    {V : Type u} [Fintype V] {W K : Type} [Fintype W] [DecidableEq W] [Nonempty W]
    {G H : SimpleGraph V} {J : SimpleGraph W} [DecidableRel J.Adj]
    (hHG : H ≤ G) (F : Copy J H) (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hr2 : RobustAtLength G H 2 5) (hr3 : RobustAtLength G H 3 5)
    (hr5 : RobustAtLength G H 5 5)
    {γ ξ ρ : ℝ} (hγ : 0 < γ) (hξ : 0 ≤ ξ) (hρ : 0 < ρ) (hsmall : ξ ≤ ρ / 2)
    (hdegree : ∀ v, (1 / 3 + γ) * (Fintype.card W : ℝ) ≤ J.degree v)
    (hdensity : (1 / 4 - ξ) * (Fintype.card W : ℝ) ^ 2 ≤ J.edgeFinset.card)
    (hdeficit : ∀ A : Finset W, ρ * (Fintype.card W : ℝ) ^ 2 ≤
      (J.edgeFinset.card : ℝ) - (J.interedges A Aᶜ).card) :
    potential (Fintype.card W) J.edgeFinset.card -
      (2 * ξ / ρ) * (Fintype.card W : ℝ) ^ 2 ≤ (usedColors c : ℝ) := by
  have hn : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr Fintype.card_pos
  have hsq : (0 : ℝ) < (Fintype.card W : ℝ) ^ 2 := pow_pos hn 2
  have hmin : (uniformWeights W).MinDegreeAtLeast J (1 / 3 + γ) :=
    (uniform_minDegree_iff J _).mpr hdegree
  have hdensityW : 1 / 4 - ξ ≤ (uniformWeights W).edgeMass J := by
    rw [uniform_edgeMass]
    exact (le_div_iff₀ hsq).mpr hdensity
  obtain ⟨A, _, hA⟩ := uniform_maxCut_attained J
  have hdeficitW : ρ ≤ (uniformWeights W).edgeMass J - (uniformWeights W).maxCut J := by
    rw [uniform_maxCut_deficit J A hA]
    exact (le_div_iff₀ hsq).mpr (hdeficit A)
  have hbound := original_palette_of_weightedStableCP hCP hHG F c hc hr2 hr3 hr5
    (uniformWeights W) uniform_weight_pos (by linarith : 1 / 3 < 1 / 3 + γ)
    hmin hξ hρ hsmall hdensityW hdeficitW
    (show 0 ≤ 1 / (Fintype.card W : ℝ) ^ 2 by positivity) uniform_capacity
  rw [uniform_edgeMass] at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound hsq.le
  have hleft : (3 * ((J.edgeFinset.card : ℝ) / (Fintype.card W : ℝ) ^ 2) / 2 -
      1 / 4 - 2 * ξ / ρ) * (Fintype.card W : ℝ) ^ 2 =
      potential (Fintype.card W) J.edgeFinset.card -
        (2 * ξ / ρ) * (Fintype.card W : ℝ) ^ 2 := by
    unfold potential
    field_simp [ne_of_gt hn, ne_of_gt hρ]
  have hright : ((usedColors c : ℝ) * (1 / (Fintype.card W : ℝ) ^ 2)) *
      (Fintype.card W : ℝ) ^ 2 = usedColors c := by field_simp
  rwa [hleft, hright] at hmul

/-- One uniform cutoff supplies both robust source paths and degree pruning.
The retained paths still live in G, and all deleted incident edges are charged. -/
theorem exists_robust_pruned_source (γ β η : ℝ)
    (hγ : 0 < γ) (hβ : 0 < β) (hη : 0 < η)
    (hmargin : β + 2 * η / β < γ / 2) :
    ∃ N : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      (∀ v, (1 / 3 + γ) * (Fintype.card V : ℝ) ≤ G.degree v) →
      ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, ∃ S : Finset V,
        H ≤ G ∧ RobustAtLength G H 2 5 ∧ RobustAtLength G H 3 5 ∧
        RobustAtLength G H 5 5 ∧
        (1 - 2 * η / β) * (Fintype.card V : ℝ) ≤ S.card ∧
        S.card ≤ Fintype.card V ∧
        (∀ v : (S : Set V), (1 / 3 + γ / 2) * (S.card : ℝ) <
          ((H.induce (S : Set V)).degree v : ℝ)) ∧
        (G.edgeFinset.card : ℝ) - (H.induce (S : Set V)).edgeFinset.card ≤
          (η + 2 * η / β) * (Fintype.card V : ℝ) ^ 2 ∧
        Nonempty (H.induce (S : Set V) ↪g H) := by
  obtain ⟨N, hN⟩ := exists_robust_cleanup η hη 5
  refine ⟨max 1 N, ?_⟩
  intro V instV instEq G instG hn hdegree
  obtain ⟨H, instH, hHG, hloss, hr2, hr3, hr5⟩ :=
    hN V G ((le_max_right _ _).trans hn)
  letI := instH
  have hnpos : 0 < Fintype.card V :=
    Nat.zero_lt_one.trans_le ((le_max_left _ _).trans hn)
  obtain ⟨S, horder, horderMax, hdeg, hcost, hcopy⟩ :=
    exists_degree_pruning_margin G H hHG hγ hβ hnpos hloss.le hmargin hdegree
  exact ⟨H, instH, S, hHG, hr2, hr3, hr5, horder, horderMax, hdeg, hcost, hcopy⟩

/-- Transport a retained palette estimate back through the complete deletion
cost. This is the exact coefficient in the frozen campaign source reduction. -/
lemma palette_from_pruned_potential {n h m e r ρ : ℝ}
    (hh : 0 ≤ h) (hhn : h ≤ n)
    (hretained : potential h e - 4 * (m - e) / ρ ≤ r) :
    potential n m - (3 / 2 + 4 / ρ) * (m - e) ≤ r := by
  have hpotential := potential_loss (m := m) (q := m - e) hh hhn
  have hid : m - (m - e) = e := by ring
  rw [hid] at hpotential
  have hscale : (3 / 2 + 4 / ρ) * (m - e) = 3 * (m - e) / 2 + 4 * (m - e) / ρ := by ring
  rw [hscale]
  linarith only [hpotential, hretained]

/-- Positive cleanup tolerances can pay both the degree margin and the full
potential error. All choices precede the order cutoff. -/
lemma exists_source_tolerances {γ ρ t : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ β η : ℝ, 0 < β ∧ 0 < η ∧ β + 2 * η / β < γ / 2 ∧
      2 * η / β ≤ 1 / 2 ∧ η + 2 * η / β ≤ ρ / 16 ∧
      (3 / 2 + 4 / ρ) * (η + 2 * η / β) ≤ t := by
  let β := γ / 4
  let D := 1 + 2 / β
  let C := 3 / 2 + 4 / ρ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : 0 < min (β * γ / 8) (min (β / 4) (min (ρ / (16 * D)) (t / (C * D)))) := by
    positivity
  obtain ⟨η, hη, hηsmall⟩ := exists_between hsmall
  have hη₁ := hηsmall.trans_le (min_le_left _ _)
  have hηrest := hηsmall.trans_le (min_le_right _ _)
  have hη₂ := hηrest.trans_le (min_le_left _ _)
  have hηrest' := hηrest.trans_le (min_le_right _ _)
  have hη₃ := hηrest'.trans_le (min_le_left _ _)
  have hη₄ := hηrest'.trans_le (min_le_right _ _)
  have hid : η + 2 * η / β = η * D := by dsimp [D]; ring
  refine ⟨β, η, hβ, hη, ?_, ?_, ?_, ?_⟩
  · have hb : 2 * η / β < γ / 4 := (div_lt_iff₀ hβ).mpr (by linarith)
    dsimp [β] at *
    linarith only [hb]
  · exact (div_le_iff₀ hβ).mpr (by linarith)
  · rw [hid]
    have hb := (lt_div_iff₀ (show 0 < 16 * D by positivity)).mp hη₃
    linarith only [hb]
  · change C * (η + 2 * η / β) ≤ t
    rw [hid]
    have hb := (lt_div_iff₀ (mul_pos hC hD)).mp hη₄
    nlinarith only [hb]

/-- The far-cut source theorem, still explicitly conditional on the finite
weighted statement. Every original cut has the prescribed deficit. -/
theorem farSourcePotentialBound_of_weightedStableCP (hCP : WeightedStableCP)
    {γ ρ t : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) (ht : 0 < t) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (K : Type) (c : G.edgeSet → K),
      N ≤ Fintype.card V → exactThreshold (Fintype.card V) ≤ EdgeCount G →
      ValidC7Coloring c →
      (∀ v, (1 / 3 + γ) * (Fintype.card V : ℝ) ≤ G.degree v) →
      (∀ A : Finset V, ρ * (Fintype.card V : ℝ) ^ 2 ≤
        (G.edgeFinset.card : ℝ) - (G.interedges A Aᶜ).card) →
      potential (Fintype.card V) G.edgeFinset.card -
        t * (Fintype.card V : ℝ) ^ 2 ≤ (usedColors c : ℝ) := by
  obtain ⟨β, η, hβ, hη, hmargin, hhalf, hsmall, hpay⟩ :=
    exists_source_tolerances hγ hρ ht
  obtain ⟨N, hN⟩ := exists_robust_pruned_source γ β η hγ hβ hη hmargin
  refine ⟨max 1 N, ?_⟩
  intro V instV instEq G instG K c hn helig hc hdegree hdeficit
  classical
  have hnpos : 0 < Fintype.card V :=
    Nat.zero_lt_one.trans_le ((le_max_left _ _).trans hn)
  have hnR : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hnpos
  obtain ⟨H, instH, S, hHG, hr2, hr3, hr5, horder, horderMax, hdeg, hcost, hcopy⟩ :=
    hN V G ((le_max_right _ _).trans hn) hdegree
  letI := instH
  let W := (S : Set V)
  let J := H.induce (S : Set V)
  obtain ⟨F⟩ := hcopy
  let Fsource : Copy J G := (Copy.ofLE H G hHG).comp F.toCopy
  have hcard : Fintype.card W = S.card := Fintype.card_coe _
  have hhhalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card W := by
    rw [hcard]
    have hh := mul_le_mul_of_nonneg_right hhalf hnR.le
    nlinarith only [horder, hh]
  have hhR : (0 : ℝ) < Fintype.card W := lt_of_lt_of_le (half_pos hnR) hhhalf
  letI : Nonempty W := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hhR)
  have hhn : (Fintype.card W : ℝ) ≤ Fintype.card V := by
    rw [hcard]
    exact_mod_cast horderMax
  have hh2 : (0 : ℝ) < (Fintype.card W : ℝ) ^ 2 := pow_pos hhR 2
  have hsq : (Fintype.card W : ℝ) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 :=
    pow_le_pow_left₀ hhR.le hhn 2
  have hsqhalf : (Fintype.card V : ℝ) ^ 2 ≤ 4 * (Fintype.card W : ℝ) ^ 2 := by
    nlinarith only [hhhalf, hhR, hnR]
  let q : ℝ := (G.edgeFinset.card : ℝ) - J.edgeFinset.card
  have hq : 0 ≤ q := by
    have he := edgeCount_mono Fsource
    have he' : J.edgeFinset.card ≤ G.edgeFinset.card := by
      simpa only [EdgeCount, Nat.card_eq_fintype_card, ← edgeFinset_card] using he
    exact sub_nonneg.mpr (Nat.cast_le.mpr he')
  have hcost' : q ≤ (η + 2 * η / β) * (Fintype.card V : ℝ) ^ 2 := hcost
  have hqsmall : q ≤ ρ / 16 * (Fintype.card V : ℝ) ^ 2 :=
    hcost'.trans (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))
  have hqretained : q ≤ ρ / 4 * (Fintype.card W : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsqhalf (show 0 ≤ ρ / 16 by positivity)
    nlinarith only [hqsmall, hm]
  let ξ := q / (Fintype.card W : ℝ) ^ 2
  have hξ : 0 ≤ ξ := div_nonneg hq hh2.le
  have hξsmall : ξ ≤ (ρ / 2) / 2 := by
    apply (div_le_iff₀ hh2).mpr
    linarith only [hqretained]
  have hξeq : ξ * (Fintype.card W : ℝ) ^ 2 = q := div_mul_cancel₀ q (ne_of_gt hh2)
  have hdensity : (1 / 4 - ξ) * (Fintype.card W : ℝ) ^ 2 ≤ J.edgeFinset.card := by
    have he := real_excess_of_exactThreshold helig
    dsimp [q] at hξeq
    nlinarith only [he, hsq, hξeq]
  have hdeficitJ (A : Finset W) : (ρ / 2) * (Fintype.card W : ℝ) ^ 2 ≤
      (J.edgeFinset.card : ℝ) - (J.interedges A Aᶜ).card := by
    have hcut := cut_deficit_copy Fsource hdeficit A
    change ρ * (Fintype.card V : ℝ) ^ 2 - q ≤ _ at hcut
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ρ / 2 by positivity)
    nlinarith only [hcut, hqsmall, hm, sq_nonneg (Fintype.card V : ℝ), hρ]
  have hdegreeJ (v : W) : (1 / 3 + γ / 2) * (Fintype.card W : ℝ) ≤ J.degree v := by
    rw [hcard]
    exact (hdeg v).le
  have hretained := pruned_palette_of_weightedStableCP hCP hHG F.toCopy c hc hr2 hr3 hr5
    (show 0 < γ / 2 by positivity) hξ (show 0 < ρ / 2 by positivity) hξsmall
    hdegreeJ hdensity hdeficitJ
  have herr : (2 * ξ / (ρ / 2)) * (Fintype.card W : ℝ) ^ 2 = 4 * q / ρ := by
    dsimp [ξ]
    field_simp [ne_of_gt hhR, ne_of_gt hρ]
    ring
  rw [herr] at hretained
  have hsource := palette_from_pruned_potential hhR.le hhn hretained
  have hC : 0 ≤ (3 / 2 : ℝ) + 4 / ρ := by positivity
  have hpaid : (3 / 2 + 4 / ρ) * q ≤ t * (Fintype.card V : ℝ) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hcost' hC
    have h₂ := mul_le_mul_of_nonneg_right hpay (sq_nonneg (Fintype.card V : ℝ))
    nlinarith only [h₁, h₂]
  exact (by linarith only [hsource, hpaid])

/-- The terminal source statement needed by peeling. The cutoff is uniform
over every finite host, original label type and valid coloring. -/
def TerminalPotentialBound (γ t : ℝ) : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : Type) (c : G.edgeSet → K),
    N ≤ Fintype.card V → exactThreshold (Fintype.card V) ≤ EdgeCount G →
    ValidC7Coloring c →
    (∀ v, (1 / 3 + γ) * (Fintype.card V : ℝ) ≤ G.degree v) →
    potential (Fintype.card V) G.edgeFinset.card -
      t * (Fintype.card V : ℝ) ^ 2 ≤ (usedColors c : ℝ)

/-- Near cuts are handled by explicit seven-cycles; all remaining cuts are
handled by robust cleanup and the assumed weighted theorem. The cutoff is
uniform over hosts, source labels, and valid colorings. -/
theorem terminalPotentialBound_of_weightedStableCP (hCP : WeightedStableCP)
    {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) : TerminalPotentialBound γ t := by
  let ε := min (t / 2) (1 / 16)
  let ρ := min (ε ^ 3 / 8) (t / 3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεle : ε ≤ 1 / 16 := min_le_right _ _
  have hεt : ε ≤ t / 2 := min_le_left _ _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsmall : ρ ≤ ε ^ 3 / 8 := min_le_left _ _
  have hρt : ρ ≤ t / 3 := min_le_right _ _
  have hpay : ε + 3 * ρ / 2 ≤ t := by linarith only [hεt, hρt]
  obtain ⟨N, hN⟩ := farSourcePotentialBound_of_weightedStableCP hCP hγ hρ ht
  refine ⟨max N ⌈64 / ε ^ 3⌉₊, ?_⟩
  intro V instV instEq G instG K c hn helig hc hdegree
  have hlarge : 64 / ε ^ 3 ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hn))
  by_cases hnear : ∃ A : Finset V,
      (G.edgeFinset.card : ℝ) - (G.interedges A Aᶜ).card ≤
        ρ * (Fintype.card V : ℝ) ^ 2
  · obtain ⟨A, hA⟩ := hnear
    have hb := nearCut_potential_lower_of_cut_deficit hε hεle hρsmall hlarge helig A hA c hc
    have hp := mul_le_mul_of_nonneg_right hpay (sq_nonneg (Fintype.card V : ℝ))
    linarith only [hb, hp]
  · exact hN V G K c ((le_max_left _ _).trans hn) helig hc hdegree
      (fun A => (lt_of_not_ge (fun hA => hnear ⟨A, hA⟩)).le)

/-- Once a uniform terminal bound is supplied, the proved peeling theorem
preserves the exact threshold and gives the requested finite epsilon bound. -/
theorem lowerBoundAt_of_terminal {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 16)
    (hterminal : TerminalPotentialBound (ε / 12) (ε / 2)) :
    ∃ N : ℕ, ∀ n ≥ N, LowerBoundAt ε n := by
  classical
  obtain ⟨N₀, hN₀⟩ := hterminal
  refine ⟨max 64 (max (3 * N₀) ⌈64 / ε⌉₊), ?_⟩
  intro n hn G K c he hc
  have hn64 : 64 ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 * N₀ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnceil : ⌈64 / ε⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnlarge : 64 / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hnceil)
  have hγ : 0 < ε / 12 := by positivity
  have hγle : ε / 12 ≤ 1 / 48 := by linarith
  have helig : (Fintype.card (Fin n) : ℝ) ^ 2 / 4 < G.edgeFinset.card :=
    real_excess_of_exactThreshold (by simpa only [Fintype.card_fin] using he)
  obtain ⟨W, instW, H, instH, hcopy, horder, hHelig, hdegree, hpotential⟩ :=
    exists_peeled_graph G (by simpa only [Fintype.card_fin] using hn64) hγ hγle helig
  letI := instW
  letI := instH
  obtain ⟨F⟩ := hcopy
  simp only [Fintype.card_fin] at horder hpotential
  have hN : N₀ ≤ Fintype.card W := by
    have hn3R : 3 * (N₀ : ℝ) ≤ n := by exact_mod_cast hn3
    have hNR : (N₀ : ℝ) ≤ Fintype.card W := by linarith
    exact_mod_cast hNR
  have hHthreshold : exactThreshold (Fintype.card W) ≤ EdgeCount H := by
    apply (exactThreshold_le_iff_real_excess _ _).mpr
    simpa only [EdgeCount, Nat.card_eq_fintype_card, ← edgeFinset_card] using hHelig
  have hterminalH := hN₀ W H K (c ∘ F.toCopy.mapEdgeSet) hN hHthreshold (hc.comap F.toCopy)
    (fun v => by have hv := hdegree v; linarith)
  have hpalette : (usedColors (c ∘ F.toCopy.mapEdgeSet) : ℝ) ≤ usedColors c :=
    Nat.cast_le.mpr (usedColors_comap_le c F.toCopy)
  have hhn : (Fintype.card W : ℝ) ≤ n := by
    exact_mod_cast (show Fintype.card W ≤ n by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective F F.injective)
  have hretained : peelingBound n (ε / 12) - (ε / 2) * (Fintype.card W : ℝ) ^ 2 ≤
      (usedColors (c ∘ F.toCopy.mapEdgeSet) : ℝ) := by
    linarith only [hpotential, hterminalH]
  exact (peeling_terminal_absorption hε hεle hnlarge (Nat.cast_nonneg _) hhn hretained).trans hpalette

/-- This implication is conditional on the explicitly quantified terminal
source theorem; it does not discharge the finite weighted CP hypothesis. -/
theorem asymptoticLowerBound_of_terminal
    (hterminal : ∀ γ t : ℝ, 0 < γ → γ ≤ 1 / 48 → 0 < t → TerminalPotentialBound γ t) :
    AsymptoticLowerBound := by
  intro ε hε
  let e := min ε (1 / 16)
  have he : 0 < e := lt_min hε (by norm_num)
  have hele : e ≤ 1 / 16 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨N, hN⟩ := lowerBoundAt_of_terminal he hele
    (hterminal (e / 12) (e / 2) (by positivity) (by linarith) (by positivity))
  refine ⟨N, ?_⟩
  intro n hn G K c heG hc
  have hbound := hN n hn G K c heG hc
  exact (mul_le_mul_of_nonneg_right (by linarith : 1 / 8 - ε ≤ 1 / 8 - e)
    (sq_nonneg (n : ℝ))).trans hbound

/-- Complete source-side implication, retaining the sole finite weighted
obligation as a named argument. This theorem makes no unconditional claim
that `WeightedStableCP` has been established. -/
theorem asymptoticLowerBound_of_weightedStableCP (hCP : WeightedStableCP) :
    AsymptoticLowerBound :=
  asymptoticLowerBound_of_terminal
    (fun _ _ hγ _ ht => terminalPotentialBound_of_weightedStableCP hCP hγ ht)

end Erdos809.Source
