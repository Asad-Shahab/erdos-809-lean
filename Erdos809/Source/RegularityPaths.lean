import Erdos809.Source.RobustPaths
import Mathlib.Tactic.Positivity

/-!
# Regular-pair typicality into a large subset

The standard degree-counting argument is made explicit, including the case
where the target set is a large subset of its regularity cluster.
-/

noncomputable section

namespace Erdos809.Source

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Vertices of A with less than the prescribed number of neighbors in Y. -/
def lowNeighbors (A Y : Finset V) (d : ℝ) : Finset V := by
  classical
  exact {x ∈ A | ((Y.filter (G.Adj x)).card : ℝ) < d * Y.card}

private lemma card_interedges_lowNeighbors_le {A Y : Finset V} {d : ℝ} :
    ((G.interedges (lowNeighbors (G := G) A Y d) Y).card : ℝ) ≤
      (lowNeighbors (G := G) A Y d).card * Y.card * d := by
  classical
  refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (Y.card : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx => (mem_filter.mp hx).2.le

/-- At most ε|A| vertices fail the regular-pair expected degree into a large Y. -/
lemma card_lowNeighbors_le {A B Y : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε A B) (hdense : ε ≤ G.edgeDensity A B)
    (hY : Y ⊆ B) (hYsize : (B.card : ℝ) * ε ≤ Y.card) :
    ((lowNeighbors (G := G) A Y (G.edgeDensity A B - ε)).card : ℝ) ≤ A.card * ε := by
  classical
  let Bad := lowNeighbors (G := G) A Y (G.edgeDensity A B - ε)
  have hden : (G.edgeDensity Bad Y : ℝ) ≤ G.edgeDensity A B - ε := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    apply div_le_of_le_mul₀ (by positivity) (sub_nonneg.mpr hdense)
    rw [mul_comm]
    exact card_interedges_lowNeighbors_le
  by_contra! hbad
  have hsub : Bad ⊆ A := filter_subset _ _
  have hr := (abs_lt.mp (hreg hsub hY hbad.le hYsize)).1
  linarith


/-- A large regular pair has an edge after removing an arbitrary finite set. -/
lemma exists_adj_outside_of_uniform [DecidableEq V]
    {A B Y Z E : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε A B) (hdense : ε ≤ G.edgeDensity A B)
    (hY : Y ⊆ A) (hZ : Z ⊆ B)
    (hYs : (A.card : ℝ) * ε + E.card ≤ Y.card)
    (hZs : (B.card : ℝ) * ε + E.card ≤ Z.card) :
    ∃ y ∈ Y, ∃ z ∈ Z, G.Adj y z ∧ y ∉ E ∧ z ∉ E := by
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_adj_of_uniform hreg hdense
    (Finset.sdiff_subset.trans hY) (Finset.sdiff_subset.trans hZ)
    (card_sdiff_lower Y E hYs) (card_sdiff_lower Z E hZs)
  exact ⟨y, (mem_sdiff.mp hy).1, z, (mem_sdiff.mp hz).1,
    hyz, (mem_sdiff.mp hy).2, (mem_sdiff.mp hz).2⟩

private lemma card_union_list_le [DecidableEq V] (F : Finset V) (L : List V) :
    (F ∪ L.toFinset).card ≤ F.card + L.length :=
  (card_union_le _ _).trans (Nat.add_le_add_left L.toFinset_card_le _)

/-- Local five-path construction. The two middle vertices are chosen from
large subsets of a regular pair; their endpoint-neighbor sets are large enough
to exclude every actual vertex already chosen. No disjoint-cluster assumption
is made, so repeated nonconsecutive clusters are allowed. -/
lemma hasAvoidingPath_five_of_uniform [DecidableEq V]
    {u v : V} {A B X Y Z W F : Finset V} {ε : ℝ}
    (huv : u ≠ v) (hu : u ∉ F) (hv : v ∉ F)
    (hreg : G.IsUniform ε A B) (hdense : ε ≤ G.edgeDensity A B)
    (hY : Y ⊆ A) (hZ : Z ⊆ B)
    (hYs : (A.card : ℝ) * ε + F.card + 2 ≤ Y.card)
    (hZs : (B.card : ℝ) * ε + F.card + 2 ≤ Z.card)
    (hXu : ∀ x ∈ X, G.Adj u x) (hWv : ∀ w ∈ W, G.Adj w v)
    (hXlarge : ∀ y ∈ Y, F.card + 5 < (X.filter (G.Adj y)).card)
    (hWlarge : ∀ z ∈ Z, F.card + 5 < (W.filter (G.Adj z)).card) :
    HasAvoidingPath G u v 5 F := by
  let E := F ∪ [u, v].toFinset
  have hE : E.card ≤ F.card + 2 := by simpa [E] using card_union_list_le F [u, v]
  have hER : (E.card : ℝ) ≤ F.card + 2 := by exact_mod_cast hE
  obtain ⟨y, hy, z, hz, hyz, hyE, hzE⟩ := exists_adj_outside_of_uniform hreg hdense hY hZ
    (show (A.card : ℝ) * ε + E.card ≤ Y.card by linarith)
    (show (B.card : ℝ) * ε + E.card ≤ Z.card by linarith)
  let Ex := F ∪ [u, v, y, z].toFinset
  have hEx : Ex.card < (X.filter (G.Adj y)).card := by
    have hbound := card_union_list_le F [u, v, y, z]
    have hlarge := hXlarge y hy
    simp only [List.length_cons, List.length_nil] at hbound
    dsimp [Ex]
    omega
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty_of_card_lt_card hEx
  obtain ⟨hxX, hyx⟩ := mem_filter.mp (mem_sdiff.mp hx).1
  have hxEx := (mem_sdiff.mp hx).2
  let Ew := F ∪ [u, v, x, y, z].toFinset
  have hEw : Ew.card < (W.filter (G.Adj z)).card := by
    exact (card_union_list_le F [u, v, x, y, z]).trans_lt (hWlarge z hz)
  obtain ⟨w, hw⟩ := Finset.sdiff_nonempty_of_card_lt_card hEw
  obtain ⟨hwW, hzw⟩ := mem_filter.mp (mem_sdiff.mp hw).1
  have hwEw := (mem_sdiff.mp hw).2
  simp only [E, Ex, Ew, mem_union, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hyE hzE hxEx hwEw
  refine ⟨.cons (hXu x hxX) (.cons hyx.symm (.cons hyz (.cons hzw (.cons (hWv w hwW) .nil)))),
    ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    have hyzNe := hyz.ne
    constructor
    · exact ⟨Ne.symm hxEx.2.1, Ne.symm hyE.2.1, Ne.symm hzE.2.1,
        Ne.symm hwEw.2.1, huv⟩
    constructor
    · exact ⟨hxEx.2.2.2.1, hxEx.2.2.2.2, Ne.symm hwEw.2.2.2.1, hxEx.2.2.1⟩
    constructor
    · exact ⟨hyzNe, Ne.symm hwEw.2.2.2.2.1, hyE.2.2⟩
    constructor
    · exact ⟨Ne.symm hwEw.2.2.2.2.2, hzE.2.2⟩
    · exact ⟨hwEw.2.2.1, not_false⟩
  · intro a ha
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu
    · exact hxEx.1
    · exact hyE.1
    · exact hzE.1
    · exact hwEw.1
    · exact hv


/-- Full local regularity deduction for a five-walk cluster pattern. The
three consecutive cluster pairs are regular, endpoint neighbors are large,
and all rounding/forbidden-vertex losses are explicit hypotheses. -/
lemma hasAvoidingPath_five_of_regular_chain [DecidableEq V]
    {u v : V} {C₁ C₂ C₃ C₄ X W F : Finset V} {ε : ℝ}
    (huv : u ≠ v) (hu : u ∉ F) (hv : v ∉ F)
    (h21 : G.IsUniform ε C₂ C₁) (h23 : G.IsUniform ε C₂ C₃)
    (h34 : G.IsUniform ε C₃ C₄)
    (hd21 : ε ≤ G.edgeDensity C₂ C₁) (hd23 : ε ≤ G.edgeDensity C₂ C₃)
    (hd34 : ε ≤ G.edgeDensity C₃ C₄)
    (hX : X ⊆ C₁) (hW : W ⊆ C₄)
    (hXu : ∀ x ∈ X, G.Adj u x) (hWv : ∀ w ∈ W, G.Adj w v)
    (hXs : (C₁.card : ℝ) * ε ≤ X.card)
    (hWs : (C₄.card : ℝ) * ε ≤ W.card)
    (hC₂ : (F.card : ℝ) + 2 ≤ C₂.card * (1 - 2 * ε))
    (hC₃ : (F.card : ℝ) + 2 ≤ C₃.card * (1 - 2 * ε))
    (hXmany : (F.card : ℝ) + 5 < (G.edgeDensity C₂ C₁ - ε) * X.card)
    (hWmany : (F.card : ℝ) + 5 < (G.edgeDensity C₃ C₄ - ε) * W.card) :
    HasAvoidingPath G u v 5 F := by
  classical
  let BadY := lowNeighbors (G := G) C₂ X (G.edgeDensity C₂ C₁ - ε)
  let BadZ := lowNeighbors (G := G) C₃ W (G.edgeDensity C₃ C₄ - ε)
  have hBadY : (BadY.card : ℝ) ≤ C₂.card * ε := card_lowNeighbors_le h21 hd21 hX hXs
  have hBadZ : (BadZ.card : ℝ) ≤ C₃.card * ε := card_lowNeighbors_le h34 hd34 hW hWs
  have hYs : (C₂.card : ℝ) * ε + F.card + 2 ≤ (C₂ \ BadY).card := by
    apply card_sdiff_lower C₂ BadY
    nlinarith
  have hZs : (C₃.card : ℝ) * ε + F.card + 2 ≤ (C₃ \ BadZ).card := by
    apply card_sdiff_lower C₃ BadZ
    nlinarith
  apply hasAvoidingPath_five_of_uniform huv hu hv h23 hd23 sdiff_subset sdiff_subset
    hYs hZs hXu hWv
  · intro y hy
    have hyBad := (mem_sdiff.mp hy).2
    have hdeg : (G.edgeDensity C₂ C₁ - ε) * X.card ≤ ((X.filter (G.Adj y)).card : ℝ) := by
      apply le_of_not_gt
      intro hbad
      exact hyBad (mem_filter.mpr ⟨(mem_sdiff.mp hy).1, hbad⟩)
    have hlt := hXmany.trans_le hdeg
    exact_mod_cast hlt
  · intro z hz
    have hzBad := (mem_sdiff.mp hz).2
    have hdeg : (G.edgeDensity C₃ C₄ - ε) * W.card ≤ ((W.filter (G.Adj z)).card : ℝ) := by
      apply le_of_not_gt
      intro hbad
      exact hzBad (mem_filter.mpr ⟨(mem_sdiff.mp hz).1, hbad⟩)
    have hlt := hWmany.trans_le hdeg
    exact_mod_cast hlt

end Erdos809.Source
