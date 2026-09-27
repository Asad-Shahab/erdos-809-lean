import Erdos809.LongOddCycles.FarCase
import Erdos809.LongOddCycles.ScalarCutoff
import Erdos809.LongOddCycles.NearCase
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Universal finite-host induction for the BCM potential. The induction fixes
its error tolerance and constant before quantifying over hosts and colorings.
Vertex deletion preserves actual used colors only monotonically, and the
smaller host is used only after checking its own strict-density eligibility. -/

noncomputable section
namespace Erdos809.LongOddCycles
open SimpleGraph Finset
universe u v

/-- The near terminal estimate, separated only to make the induction independent
of the implementation of the near-cycle construction. -/
def NearTerminalBound (k : ℕ) (ε : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Type v) (c : G.edgeSet → K),
    ValidCycleColoring (2 * k + 1) c →
    ScalarScale (k : ℝ) ε (Fintype.card V) →
    (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card →
    (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 <
      ε ^ 6 * (Fintype.card V : ℝ) ^ 2 →
    (∀ w, (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2 <
      (G.degree w : ℝ)) →
    bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 ≤
      (usedColors c : ℝ)

/-- Complete strong induction given the separately formalized near terminal
estimate. The far terminal estimate is already discharged internally. -/
theorem finiteLower_of_nearTerminal (k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hnearTerminal : NearTerminalBound.{u,v} k ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (K : Type v) (c : G.edgeSet → K),
        ValidCycleColoring (2 * k + 1) c →
        (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card →
        bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 - C ≤
          (usedColors c : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := exists_scalarScale_cutoff k hk ε hε hεsmall
  let C : ℝ := (M : ℝ) ^ 2 / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨C, hC, ?_⟩
  have hmain : ∀ n : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (K : Type v) (c : G.edgeSet → K), Fintype.card V = n →
        ValidCycleColoring (2 * k + 1) c →
        (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card →
        bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 - C ≤
          (usedColors c : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V instV instEq G instAdj K c hn hc hm
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      have hmupper := edgeCount_le_half_order_sq G
      by_cases hsmall : n < M
      · have hnM : (Fintype.card V : ℝ) ≤ M := by exact_mod_cast (show Fintype.card V ≤ M by omega)
        have hbase := bcmPotential_base (Fintype.card V) G.edgeFinset.card M ε
          hn0 hnM hε.le hmupper
        exact le_trans hbase (Nat.cast_nonneg _)
      have hscale := hM (Fintype.card V) (by exact_mod_cast (show M ≤ Fintype.card V by omega))
      have hVpos : 0 < Fintype.card V := by
        have ho := hscale.order
        have : (0 : ℝ) < Fintype.card V := by linarith
        exact_mod_cast this
      letI : Nonempty V := Fintype.card_pos_iff.mp hVpos
      obtain ⟨w, hw⟩ := G.exists_minimal_degree_vertex
      have hmin : ∀ z, (G.degree w : ℝ) ≤ (G.degree z : ℝ) := by
        intro z
        exact_mod_cast (show G.degree w ≤ G.degree z by rw [← hw]; exact G.minDegree_le_degree z)
      let W : Type u := ({w}ᶜ : Set V)
      let H : SimpleGraph W := G.induce {w}ᶜ
      let I : Copy H G := (Embedding.induce {w}ᶜ).toCopy
      let c' : H.edgeSet → K := c ∘ I.mapEdgeSet
      have hcard : Fintype.card W = Fintype.card V - 1 := by
        calc
          Fintype.card W = (univ.erase w).card :=
            Fintype.card_of_subtype _ (by intro z; simp)
          _ = Fintype.card V - 1 := by simp
      have hcardR : (Fintype.card W : ℝ) = (Fintype.card V : ℝ) - 1 := by
        rw [hcard, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
        norm_num
      have hedges : H.edgeFinset.card = G.edgeFinset.card - G.degree w := by
        simpa only [H, SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card] using
          (G.card_edgeFinset_induce_compl_singleton w).trans (G.card_edgeFinset_deleteIncidenceSet w)
      have hedgesR : (H.edgeFinset.card : ℝ) = (G.edgeFinset.card : ℝ) - G.degree w := by
        rw [hedges, Nat.cast_sub (G.degree_le_card_edgeFinset (v := w))]
      have hvalid : ValidCycleColoring (2 * k + 1) c' := hc.comap I
      have hpalette : (usedColors c' : ℝ) ≤ (usedColors c : ℝ) := by
        exact_mod_cast usedColors_comap_le c I
      by_contra! hfail
      have hterminal :
          (G.edgeFinset.card : ℝ) - G.degree w ≤ ((Fintype.card V : ℝ) - 1) ^ 2 / 4 ∨
          bcmPotential ((Fintype.card V : ℝ) - 1) ((G.edgeFinset.card : ℝ) - G.degree w) -
              ε * ((Fintype.card V : ℝ) - 1) ^ 2 - C <
            bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 - C := by
        by_cases hdel : (G.edgeFinset.card : ℝ) - G.degree w ≤
            ((Fintype.card V : ℝ) - 1) ^ 2 / 4
        · exact Or.inl hdel
        apply Or.inr
        by_contra! hcompare
        have hHeligible : (Fintype.card W : ℝ) ^ 2 / 4 < H.edgeFinset.card := by
          rw [hcardR, hedgesR]
          exact lt_of_not_ge hdel
        have hIH := ih (Fintype.card W) (by omega) W H K c' rfl hvalid hHeligible
        rw [hcardR, hedgesR] at hIH
        linarith
      by_cases hfar : ε ^ 6 * (Fintype.card V : ℝ) ^ 2 ≤
          (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4
      · have hsurplusgt := hscale.far_surplus_gt_order (k : ℝ) ε (Fintype.card V)
          ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4) hkR hfar
        have hdegreeupper : (G.degree w : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
          have hd : G.degree w + 1 ≤ Fintype.card V := G.degree_lt_card_verts w
          have hdR : (G.degree w : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast hd
          linarith
        have heligible := deleted_eligible_of_large_surplus (Fintype.card V)
          G.edgeFinset.card (G.degree w) hsurplusgt.le hdegreeupper hn0
        have hcompare := hterminal.resolve_left (not_le_of_gt heligible)
        obtain ⟨hsurplus, hdegree, _⟩ := far_degree_of_comparison (k : ℝ)
          (Fintype.card V) G.edgeFinset.card (G.degree w) ε C hkR hε hεsmall hscale
          hm hmupper hfar hcompare
        have hfarBound := farPaletteLower G k hk c hc hsurplus
          (fun z => hdegree.trans (hmin z))
        have hεn : 0 ≤ ε * (Fintype.card V : ℝ) ^ 2 := by positivity
        linarith
      · have hnear := lt_of_not_ge hfar
        have hdegree := near_degree_of_terminal_split (k : ℝ) (Fintype.card V)
          G.edgeFinset.card (G.degree w) ε C hkR hε hεsmall hscale hm hmupper hnear hterminal
        have hnearBound := hnearTerminal V G K c hc hscale hm hnear
          (fun z => hdegree.trans_le (hmin z))
        linarith
  intro V instV instEq G instAdj K c hc hm
  exact hmain (Fintype.card V) V G K c rfl hc hm

/-- The unconditional one-sided finite BCM lower bound for every fixed longer
odd cycle. The constant depends only on `k` and `ε`, and is chosen before the
arbitrary finite host and the unrestricted palette type. -/
theorem longOddCycle_finiteLower (k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (K : Type v) (c : G.edgeSet → K),
        ValidCycleColoring (2 * k + 1) c →
        (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card →
        bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 - C ≤
          (usedColors c : ℝ) := by
  apply finiteLower_of_nearTerminal k hk ε hε hεsmall
  intro V instV instEq G instAdj K c hc hscale hm hnear hdegree
  exact nearPaletteLower G k hk ε hε hscale hm hnear hdegree c hc

end Erdos809.LongOddCycles
