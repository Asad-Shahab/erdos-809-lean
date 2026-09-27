import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-!
# Exact-length paths avoiding forbidden vertices

A retained walk is allowed to repeat vertices. A lifted path must be simple,
have exactly the same length, and lie in the original source graph.
-/

namespace Erdos809.Source

variable {V : Type*} {G H : SimpleGraph V} {u v : V}

/-- A simple path of an exact length, with every vertex outside the forbidden set. -/
def HasAvoidingPath (G : SimpleGraph V) (u v : V) (ℓ : ℕ) (F : Finset V) : Prop :=
  ∃ p : G.Walk u v, p.IsPath ∧ p.length = ℓ ∧ ∀ w ∈ p.support, w ∉ F

/-- The robust lifting assertion keeps the source graph and retained graph separate.
The forbidden vertices must be other than the endpoints. -/
def RobustAtLength (G H : SimpleGraph V) (ℓ k : ℕ) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → (∃ p : H.Walk u v, p.length = ℓ) →
    ∀ F : Finset V, F.card ≤ k → u ∉ F → v ∉ F → HasAvoidingPath G u v ℓ F

/-- Robust lifting survives further deletion in the retained graph. -/
lemma RobustAtLength.mono {J : SimpleGraph V} {ℓ k : ℕ}
    (h : RobustAtLength G H ℓ k) (hJ : J ≤ H) : RobustAtLength G J ℓ k := by
  intro u v huv hp F hF hu hv
  obtain ⟨p, hp⟩ := hp
  apply h huv ⟨p.map (.ofLE hJ), by simpa using hp⟩ F hF hu hv

lemma HasAvoidingPath.mono_forbidden [DecidableEq V] {ℓ : ℕ} {F F' : Finset V}
    (h : HasAvoidingPath G u v ℓ F) (hF : F' ⊆ F) : HasAvoidingPath G u v ℓ F' := by
  obtain ⟨p, hp, hlen, hav⟩ := h
  exact ⟨p, hp, hlen, fun w hw hwF' => hav w hw (hF hwF')⟩

/-- A common neighbor outside the forbidden set gives an actual simple two-path.
Endpoint exclusion follows from graph irreflexivity; it is not an extra assumption. -/
lemma hasAvoidingPath_two_of_commonNeighbor [DecidableEq V] {w : V} {F : Finset V}
    (huv : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hu : u ∉ F) (hv : v ∉ F) (hw : w ∉ F) : HasAvoidingPath G u v 2 F := by
  refine ⟨.cons huw (.cons hvw.symm .nil), ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp [huv, huw.ne, Ne.symm hvw.ne]
  · intro a ha
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> assumption

/-- More common neighbors than forbidden vertices is sufficient for robust length two. -/
lemma hasAvoidingPath_two_of_codegree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {F : Finset V} (huv : u ≠ v)
    (hcard : F.card < (G.neighborFinset u ∩ G.neighborFinset v).card)
    (hu : u ∉ F) (hv : v ∉ F) : HasAvoidingPath G u v 2 F := by
  have hnot : ¬G.neighborFinset u ∩ G.neighborFinset v ⊆ F := by
    intro h
    exact (Finset.card_le_card h).not_gt hcard
  obtain ⟨w, hw, hwF⟩ := Finset.not_subset.mp hnot
  obtain ⟨huw, hvw⟩ := Finset.mem_inter.mp hw
  exact hasAvoidingPath_two_of_commonNeighbor huv
    ((G.mem_neighborFinset u w).mp huw) ((G.mem_neighborFinset v w).mp hvw) hu hv hwF

lemma robustAtLength_two_of_codegree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ}
    (hcodegree : ∀ ⦃u v : V⦄, u ≠ v → (∃ p : H.Walk u v, p.length = 2) →
      k < (G.neighborFinset u ∩ G.neighborFinset v).card) :
    RobustAtLength G H 2 k := by
  intro u v huv hp F hF hu hv
  exact hasAvoidingPath_two_of_codegree huv (lt_of_le_of_lt hF (hcodegree huv hp)) hu hv

/-- A positive-density regular pair contains an edge between every pair of
subsets meeting the regularity size thresholds. -/
lemma exists_adj_of_uniform [DecidableEq V] [DecidableRel G.Adj]
    {A B X Y : Finset V} {ε : ℝ}
    (hreg : G.IsUniform ε A B) (hdense : ε ≤ G.edgeDensity A B)
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (hXsize : (A.card : ℝ) * ε ≤ X.card)
    (hYsize : (B.card : ℝ) * ε ≤ Y.card) :
    ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
  have hden : (0 : ℝ) < G.edgeDensity X Y := by
    have hr := (abs_lt.mp (hreg hX hY hXsize hYsize)).1
    linarith
  by_contra! h
  have hempty : G.interedges X Y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro xy hxy
    have hxy' := G.mem_interedges_iff.mp hxy
    exact h xy.1 hxy'.1 xy.2 hxy'.2.1 hxy'.2.2
  simp [SimpleGraph.edgeDensity_def, hempty] at hden


/-- Three explicit consecutive edges give a simple three-path once the
four actual vertices are pairwise distinct and avoid the forbidden set. -/
lemma hasAvoidingPath_three [DecidableEq V] {x y : V} {F : Finset V}
    (hux : G.Adj u x) (hxy : G.Adj x y) (hyv : G.Adj y v)
    (huy : u ≠ y) (huv : u ≠ v) (hxv : x ≠ v)
    (hu : u ∉ F) (hx : x ∉ F) (hy : y ∉ F) (hv : v ∉ F) :
    HasAvoidingPath G u v 3 F := by
  refine ⟨.cons hux (.cons hxy (.cons hyv .nil)), ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp [hux.ne, hxy.ne, hyv.ne, huy, huv, hxv]
  · intro a ha
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption

/-- Removing a finite forbidden set costs at most its cardinality. -/
lemma card_sdiff_lower [DecidableEq V] (X F : Finset V) {a : ℝ}
    (h : a + F.card ≤ X.card) : a ≤ (X \ F).card := by
  have hc : (X.card : ℝ) ≤ (X \ F).card + (F.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := X) (t := F))
  linarith

/-- The length-three regular-pair construction. Neighborhood-size hypotheses
include the complete cost of deleting the forbidden set and both endpoints. -/
lemma hasAvoidingPath_three_of_uniform [DecidableEq V] [DecidableRel G.Adj]
    {A B X Y F : Finset V} {ε : ℝ}
    (huv : u ≠ v) (hu : u ∉ F) (hv : v ∉ F)
    (hreg : G.IsUniform ε A B) (hdense : ε ≤ G.edgeDensity A B)
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (hXu : ∀ x ∈ X, G.Adj u x) (hYv : ∀ y ∈ Y, G.Adj y v)
    (hXsize : (A.card : ℝ) * ε + F.card + 2 ≤ X.card)
    (hYsize : (B.card : ℝ) * ε + F.card + 2 ≤ Y.card) :
    HasAvoidingPath G u v 3 F := by
  let E := F ∪ {u, v}
  have hEcard : E.card ≤ F.card + 2 := by
    calc
      E.card ≤ F.card + ({u, v} : Finset V).card := Finset.card_union_le _ _
      _ ≤ F.card + 2 := by simp [huv]
  have hEcardR : (E.card : ℝ) ≤ F.card + 2 := by exact_mod_cast hEcard
  have hXs : (A.card : ℝ) * ε ≤ (X \ E).card :=
    card_sdiff_lower X E (by linarith)
  have hYs : (B.card : ℝ) * ε ≤ (Y \ E).card :=
    card_sdiff_lower Y E (by linarith)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj_of_uniform hreg hdense
    (Finset.sdiff_subset.trans hX) (Finset.sdiff_subset.trans hY) hXs hYs
  obtain ⟨hxX, hxE⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyY, hyE⟩ := Finset.mem_sdiff.mp hy
  have hxf : x ∉ F := fun h => hxE (Finset.mem_union_left _ h)
  have hyf : y ∉ F := fun h => hyE (Finset.mem_union_left _ h)
  have huy : u ≠ y := by
    intro h
    apply hyE
    simp [E, ← h]
  have hxv : x ≠ v := by
    intro h
    apply hxE
    simp [E, h]
  exact hasAvoidingPath_three (hXu x hxX) hxy (hYv y hyY) huy huv hxv hu hxf hyf hv

end Erdos809.Source
