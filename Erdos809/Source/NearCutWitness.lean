import Erdos809.Source.NearCut
import Erdos809.Source.NearCutParameters
import Erdos809.Source.NearCutCounting

/-!
# From an internal trigger to the near-cut palette lower bound

The maximum-cut argument supplies a trigger. Every remaining step is proved
here: the selected sets satisfy the simple-seven-cycle witness, their crossing
edge count has the required size, and the original coloring separates them.
-/

namespace Erdos809.Source

open SimpleGraph Finset

variable {V K : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {P Q T : Finset V} {τ n : ℝ} {u v : V}

private lemma nearCutS_typical
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    {x : V} (hx : x ∈ nearCutS G P T u v) :
    (crossDefect G Q x : ℝ) ≤ τ * n := by
  obtain ⟨hxP, hxT⟩ := mem_sdiff.mp hx
  exact htypP x (mem_filter.mp hxP).1 hxT

private lemma nearCutR_typical
    (htypQ : ∀ y ∈ Q, y ∉ T → (crossDefect G P y : ℝ) ≤ τ * n)
    {y : V} (hy : y ∈ nearCutR Q T u v) :
    (crossDefect G P y : ℝ) ≤ τ * n := by
  obtain ⟨hyQ, hyT⟩ := mem_sdiff.mp hy
  exact htypQ y hyQ (fun hy ↦ hyT (mem_union_left _ hy))

/-- A trigger with the numerical margins supplies every neighborhood and
actual-vertex exclusion used in the explicit seven-cycle constructions. -/
theorem nearCut_witness_of_endpoints
    (hPQ : Disjoint P Q)
    (hpar : NearCutParameters τ n P.card Q.card T.card)
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    (htypQ : ∀ y ∈ Q, y ∉ T → (crossDefect G P y : ℝ) ≤ τ * n)
    (huQ : u ∈ Q) (hvQ : v ∈ Q) (huv : G.Adj u v)
    (hu : (crossDefect G P u : ℝ) ≤ τ * n)
    (hv : (P.card : ℝ) / 2 - T.card < (P.filter (G.Adj v)).card) :
    NearCutCliqueWitness G P Q (nearCutS G P T u v) (nearCutR Q T u v) u v := by
  refine {
    disjoint := hPQ
    left_subset := nearCutS_subset G P T u v
    right_subset := nearCutR_subset Q T u v
    trigger_left_mem := huQ
    trigger_right_mem := hvQ
    trigger_adj := huv
    trigger_left_not := by simp [nearCutR]
    trigger_right_not := by simp [nearCutR]
    endpoints := ?_
    common_right := ?_
    common_trigger_left := ?_
    common_trigger_right := ?_
    row := ?_
  }
  · intro x hx
    exact (mem_filter.mp (mem_sdiff.mp hx).1).2
  · intro y hy w hw
    have hygood := nearCutR_typical htypQ hy
    have hwgood := nearCutR_typical htypQ hw
    have hcommon := common_neighbors_lower G P y w
    have hmargin := hpar.typical_common
    have hreal : (2 : ℝ) < (P.filter (fun b ↦ G.Adj y b ∧ G.Adj w b)).card := by
      linarith only [hygood, hwgood, hcommon, hmargin]
    exact_mod_cast hreal
  · intro y hy
    have hygood := nearCutR_typical htypQ hy
    have hcommon := common_neighbors_lower G P u y
    have hmargin := hpar.typical_common
    have hreal : (2 : ℝ) < (P.filter (fun b ↦ G.Adj u b ∧ G.Adj y b)).card := by
      linarith only [hu, hygood, hcommon, hmargin]
    exact_mod_cast hreal
  · intro y hy
    have hygood := nearCutR_typical htypQ hy
    have hcommon : ((P.filter (G.Adj v)).card : ℝ) - crossDefect G P y ≤
        (P.filter (fun b ↦ G.Adj v b ∧ G.Adj y b)).card := by
      simpa only [and_comm] using common_neighbors_from_degree G P y v
    have hmargin := hpar.trigger_common
    have hreal : (2 : ℝ) < (P.filter (fun b ↦ G.Adj v b ∧ G.Adj y b)).card := by
      linarith only [hv, hygood, hcommon, hmargin]
    exact_mod_cast hreal
  · intro z hz
    have hzgood := nearCutS_typical htypP hz
    have hdegree := degree_into_subset_lower G (nearCutR_subset Q T u v) z hzgood
    have hmargin := (hpar.selected_right (nearCutR_card_lower Q T u v)).2
    have hreal : (1 : ℝ) < ((nearCutR Q T u v).filter (G.Adj z)).card :=
      hmargin.trans_le hdegree
    exact_mod_cast hreal

/-- The selected crossing edges have the required quantitative size. This
counting statement uses no coloring assumption. -/
theorem nearCut_selected_card_lower
    (hpar : NearCutParameters τ n P.card Q.card T.card)
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    (hu : (crossDefect G P u : ℝ) ≤ τ * n)
    (hv : (P.card : ℝ) / 2 - T.card < (P.filter (G.Adj v)).card) :
    (1 / 8 - 9 * τ / 8) * n ^ 2 ≤
      (G.interedges (nearCutS G P T u v) (nearCutR Q T u v)).card := by
  have hs := hpar.selected_left (nearCutS_card_lower G hu hv)
  have hr := (hpar.selected_right (nearCutR_card_lower Q T u v)).1
  have hprod := near_cut_product_lower hpar.order_pos.le hpar.tau_pos.le hpar.tau_le hs hr
  apply hprod.trans
  exact selected_edges_lower G (nearCutR_subset Q T u v)
    (fun _ hx ↦ nearCutS_typical htypP hx)

/-- The original valid coloring pays the selected-edge bound from a trigger. -/
theorem nearCut_palette_lower_of_endpoints [Fintype V]
    (hPQ : Disjoint P Q)
    (hpar : NearCutParameters τ n P.card Q.card T.card)
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    (htypQ : ∀ y ∈ Q, y ∉ T → (crossDefect G P y : ℝ) ≤ τ * n)
    (huQ : u ∈ Q) (hvQ : v ∈ Q) (huv : G.Adj u v)
    (hu : (crossDefect G P u : ℝ) ≤ τ * n)
    (hv : (P.card : ℝ) / 2 - T.card < (P.filter (G.Adj v)).card)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (1 / 8 - 9 * τ / 8) * n ^ 2 ≤ (usedColors c : ℝ) := by
  have hW := nearCut_witness_of_endpoints hPQ hpar htypP htypQ huQ hvQ huv hu hv
  have hcolors : ((G.interedges (nearCutS G P T u v) (nearCutR Q T u v)).card : ℝ) ≤
      usedColors c := Nat.cast_le.mpr (nearCut_card_le_usedColors hW c hc)
  exact (nearCut_selected_card_lower hpar htypP hu hv).trans hcolors

/-- Package the endpoint hypotheses using the counting module's trigger. -/
theorem nearCut_palette_lower_of_trigger [Fintype V]
    (hPQ : Disjoint P Q)
    (hpar : NearCutParameters τ n P.card Q.card T.card)
    (htypP : ∀ x ∈ P, x ∉ T → (crossDefect G Q x : ℝ) ≤ τ * n)
    (htypQ : ∀ y ∈ Q, y ∉ T → (crossDefect G P y : ℝ) ≤ τ * n)
    (htrigger : NearCutTrigger G Q P T)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (1 / 8 - 9 * τ / 8) * n ^ 2 ≤ (usedColors c : ℝ) := by
  obtain ⟨u, huQ, huT, v, hvQ, huv, hv⟩ := htrigger
  exact nearCut_palette_lower_of_endpoints hPQ hpar htypP htypQ huQ hvQ huv
    (htypQ u huQ huT) hv c hc

end Erdos809.Source
