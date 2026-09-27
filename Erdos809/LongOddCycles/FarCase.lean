import Erdos809.LongOddCycles.ShortCore
import Erdos809.LongOddCycles.FourPath
import Erdos809.LongOddCycles.FarCycles
import Erdos809.LongOddCycles.Counting

/-! The far terminal estimate. All structural and cycle-extension inputs are
instantiated by their proved graph theorems; the palette is the actual range of
the original host coloring. -/

noncomputable section
namespace Erdos809.LongOddCycles
open SimpleGraph Finset

private lemma touching_edge_maps_to_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (e : (touchingGraph G A ∅).edgeSet) :
    ∃ x ∈ (A : Set V), x ∈ ((Copy.ofLE _ _ (touchingGraph_le G A ∅)).mapEdgeSet e).val := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    change G.Adj x y ∧ (x ∈ A ∨ y ∈ A) ∧ x ∉ (∅ : Finset V) ∧ y ∉ (∅ : Finset V) at he
    rcases he.2.1 with hx | hy
    · exact ⟨x, hx, by change x ∈ s(x, y); simp⟩
    · exact ⟨y, hy, by change y ∈ s(x, y); simp⟩

/-- Far terminal bound under exactly the robust-four-path surplus and degree
conditions. In particular no short-core, four-path or co-cyclic-edge theorem
is retained as an assumption. -/
theorem farPaletteLower {V K : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 4 ≤ k)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c)
    (hsurplus : 4 ≤ (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 -
      2 * (k : ℝ) * Fintype.card V)
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 -
      Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 -
        2 * (k : ℝ) * Fintype.card V) + 2 * (k : ℝ) ≤ (G.degree v : ℝ)) :
    bcmPotential (Fintype.card V) G.edgeFinset.card ≤ (usedColors c : ℝ) := by
  classical
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hmupper := edgeCount_le_half_order_sq G
  have hkn0 : 0 ≤ 2 * (k : ℝ) * Fintype.card V := by positivity
  have hm : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card := by linarith
  have hnNat : 0 < Fintype.card V := by
    by_contra! hz
    have hz' : (Fintype.card V : ℝ) = 0 := by exact_mod_cast (show Fintype.card V = 0 by omega)
    rw [hz'] at hmupper hm
    nlinarith
  letI : Nonempty V := Fintype.card_pos_iff.mp hnNat
  have hsqrt : Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 -
      2 * (k : ℝ) * Fintype.card V) ≤ (Fintype.card V : ℝ) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have hmin : 2 * k ≤ G.minDegree := by
    apply G.le_minDegree_of_forall_le_degree
    intro v
    have hd : 2 * (k : ℝ) ≤ (G.degree v : ℝ) := by linarith [hdegree v]
    exact_mod_cast hd
  have hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → Source.HasAvoidingPath G x y 4 S := by
    intro x y hxy S hS hx hy
    apply bcm_four_path_avoiding (G := G) (2 * k) S (by omega) hx hy hxy
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsurplus
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdegree
  obtain ⟨A, hA, hcore⟩ := shortCore G hm
  have hcolors := far_color_injOn hk (by omega : 2 * k - 3 ≤ G.minDegree)
    hrobust (A : Set V) hcore c hc
  let F : Copy (touchingGraph G A ∅) G := Copy.ofLE _ _ (touchingGraph_le G A ∅)
  have hi : Function.Injective (c ∘ F.mapEdgeSet) := by
    intro e f hef
    apply F.mapEdgeSet.injective
    exact hcolors (touching_edge_maps_to_core G A e) (touching_edge_maps_to_core G A f) hef
  have hpalette := edgeCount_le_usedColors_of_restrict_injective (touchingGraph_le G A ∅) c hi
  have hcount := incident_edge_count G A
  have hpot := incident_edge_potential (Fintype.card V) G.edgeFinset.card A.card
    (EdgeCount (touchingGraph G A ∅)) hn0 hm.le hA
    (by exact_mod_cast card_le_univ A) hcount
  exact hpot.trans (by exact_mod_cast hpalette)

end Erdos809.LongOddCycles
