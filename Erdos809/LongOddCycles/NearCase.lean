import Erdos809.LongOddCycles.NearConnectivity
import Erdos809.LongOddCycles.NearCycles
import Erdos809.LongOddCycles.WeakBook

/-! The near-density terminal palette estimate. Robust connectivity is obtained
only after the alternative palette estimate has been excluded. -/
namespace Erdos809.LongOddCycles
open SimpleGraph Finset

variable {V K : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma near_book_cover (ε : ℝ) (hε : 0 < ε) (p q : V)
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2 <
      (G.degree v : ℝ))
    (hbook : (Fintype.card V : ℝ) / 8 ≤
      ((G.neighborFinset p ∩ G.neighborFinset q).card : ℝ))
    (hselection : 2 * ε ^ 3 * Fintype.card V + 9 < (Fintype.card V : ℝ) / 8) :
    ∀ y w : V, (G.neighborFinset y ∩ G.neighborFinset w).card ≤ 4 →
      (univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card + 4 <
        (G.neighborFinset p ∩ G.neighborFinset q).card := by
  intro y w hcodeg
  have hi := card_union_add_card_inter (G.neighborFinset y) (G.neighborFinset w)
  have hc := card_sdiff_add_card_eq_card (subset_univ (G.neighborFinset y ∪ G.neighborFinset w))
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hi
  rw [card_univ] at hc
  have hiR : ((G.neighborFinset y ∪ G.neighborFinset w).card : ℝ) +
      (G.neighborFinset y ∩ G.neighborFinset w).card = (G.degree y : ℝ) + G.degree w := by
    exact_mod_cast hi
  have hcR : ((univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card : ℝ) +
      (G.neighborFinset y ∪ G.neighborFinset w).card = Fintype.card V := by exact_mod_cast hc
  have hcdR : ((G.neighborFinset y ∩ G.neighborFinset w).card : ℝ) ≤ 4 := by
    exact_mod_cast hcodeg
  have h : ((univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card : ℝ) + 4 <
      (G.neighborFinset p ∩ G.neighborFinset q).card := by
    linarith [hdegree y, hdegree w]
  exact_mod_cast h

/-- Near-density terminal case of the one-sided BCM finite induction. -/
theorem nearPaletteLower (k : ℕ) (hk : 4 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hscale : ScalarScale (k : ℝ) ε (Fintype.card V))
    (hm : (Fintype.card V : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ))
    (hnear : (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 <
      ε ^ 6 * (Fintype.card V : ℝ) ^ 2)
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2 <
      (G.degree v : ℝ))
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 ≤
      (usedColors c : ℝ) := by
  classical
  rcases nearConnectivity_or_palette G k hk ε hε hscale hnear hdegree c hc with h | hrob
  · exact h
  let d : ℝ := (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2
  have hd : ∀ v, d ≤ (G.degree v : ℝ) := fun v => (hdegree v).le
  obtain ⟨p, q, hpq, hb⟩ := weakBook G d hm hd
  have hbook : (Fintype.card V : ℝ) / 8 ≤
      ((G.neighborFinset p ∩ G.neighborFinset q).card : ℝ) := by
    have hs := hscale.book_degree
    dsimp [d] at hb
    linarith
  have hbook5 : 5 < (G.neighborFinset p ∩ G.neighborFinset q).card := by
    have han : 0 ≤ ε ^ 3 * (Fintype.card V : ℝ) := by positivity
    have hs := hscale.book_selection
    have h : (5 : ℝ) < (G.neighborFinset p ∩ G.neighborFinset q).card := by linarith
    exact_mod_cast h
  have hcover := near_book_cover G ε hε p q hdegree hbook hscale.book_selection
  have hn : 0 < Fintype.card V := by
    have h : (0 : ℝ) < Fintype.card V := by linarith [hscale.order]
    exact_mod_cast h
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  have hmin : 2 * k - 1 ≤ G.minDegree := by
    apply G.le_minDegree_of_forall_le_degree
    intro v
    have h : (2 * k : ℝ) ≤ (G.degree v : ℝ) := (hscale.greedy.trans (hdegree v).le)
    exact (Nat.sub_le _ _).trans (by exact_mod_cast h)
  have hinj := near_color_injOn (G := G) hk hmin hrob hpq hbook5 hcover c hc
  let A := (G.neighborFinset p).erase q
  let H := touchingGraph G A {p, q}
  let I := Copy.ofLE H G (touchingGraph_le G A {p, q})
  have hgood (e : H.edgeSet) :
      (∃ x ∈ (G.neighborFinset p).erase q, x ∈ (I.mapEdgeSet e).val) ∧
        p ∉ (I.mapEdgeSet e).val ∧ q ∉ (I.mapEdgeSet e).val := by
    rcases e with ⟨⟨u, v⟩, he⟩
    change G.Adj u v ∧ (u ∈ A ∨ v ∈ A) ∧ u ∉ ({p, q} : Finset V) ∧
      v ∉ ({p, q} : Finset V) at he
    change (∃ x ∈ (G.neighborFinset p).erase q, x ∈ s(u, v)) ∧
      p ∉ s(u, v) ∧ q ∉ s(u, v)
    obtain ⟨_, huvA, hu, hv⟩ := he
    constructor
    · rcases huvA with huA | hvA
      · exact ⟨u, huA, by simp⟩
      · exact ⟨v, hvA, by simp⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
      simp [Sym2.mem_iff, Ne.symm hu.1, Ne.symm hu.2, Ne.symm hv.1, Ne.symm hv.2]
  have hcI : Function.Injective (c ∘ I.mapEdgeSet) := by
    intro e f hef
    exact I.mapEdgeSet.injective (hinj (hgood e) (hgood f) hef)
  have hpalette := edgeCount_le_usedColors_of_restrict_injective
    (touchingGraph_le G A {p, q}) c hcI
  have hd2 : 2 ≤ d := by
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hs := hscale.greedy
    dsimp [d]
    linarith
  have hcount := good_edge_count G p q hpq d hd hd2
  have hpaletteR : (EdgeCount H : ℝ) ≤ usedColors c := Nat.cast_le.mpr hpalette
  have hprod := near_good_edge_product (Fintype.card V) k (ε ^ 3) d
    (Nat.cast_nonneg _) (by exact_mod_cast hk) (by positivity) hd2 (by rfl)
  apply near_palette_absorption (Fintype.card V) G.edgeFinset.card (ε ^ 3) k ε (usedColors c)
    (Nat.cast_nonneg _) (by positivity)
  · nlinarith only [hnear]
  · exact hscale.absorption
  · exact hprod.trans (hcount.trans hpaletteR)

end Erdos809.LongOddCycles
