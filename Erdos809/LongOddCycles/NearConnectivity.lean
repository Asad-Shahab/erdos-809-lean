module
public import Erdos809.LongOddCycles.Counting
public import Erdos809.LongOddCycles.DenseCycles
public import Erdos809.LongOddCycles.ScalarCutoff
public import Erdos809.Source.DegreePruning
public import Mathlib.Tactic

@[expose] public section

/-! The graph partition behind the near-density alternative. All absent-edge
claims concern the neighborhoods after removal of the forbidden set. -/
namespace Erdos809.LongOddCycles
open SimpleGraph Finset
open Erdos809.Source

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors available for a connector, excluding the other endpoint. -/
def availableNeighbors (S : Finset V) (x y : V) : Finset V :=
  G.neighborFinset x \ insert y S

lemma mem_availableNeighbors {S : Finset V} {x y z : V} :
    z ∈ availableNeighbors G S x y ↔ G.Adj x z ∧ z ≠ y ∧ z ∉ S := by
  simp [availableNeighbors, and_assoc]

lemma card_availableNeighbors (S : Finset V) (x y : V) :
    G.degree x ≤ (availableNeighbors G S x y).card + S.card + 1 := by
  have h := card_le_card_sdiff_add_card (s := G.neighborFinset x) (t := insert y S)
  have hi := card_insert_le y S
  rw [card_neighborFinset_eq_degree] at h
  change G.degree x ≤ (G.neighborFinset x \ insert y S).card + S.card + 1
  omega

lemma availableNeighbors_disjoint {S : Finset V} {x y : V}
    (hxy : x ≠ y) (hx : x ∉ S) (hy : y ∉ S)
    (hno : ¬ HasAvoidingPath G x y 2 S) :
    Disjoint (availableNeighbors G S x y) (availableNeighbors G S y x) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨hxz, _, hzS⟩ := (mem_availableNeighbors G).mp hz
  obtain ⟨hyz, _, _⟩ := (mem_availableNeighbors G).mp hz'
  exact hno (hasAvoidingPath_two_of_commonNeighbor hxy hxz hyz hx hy hzS)

lemma availableNeighbors_no_cross {S : Finset V} {x y : V}
    (hxy : x ≠ y) (hx : x ∉ S) (hy : y ∉ S)
    (hno : ¬ HasAvoidingPath G x y 3 S)
    {a b : V} (ha : a ∈ availableNeighbors G S x y)
    (hb : b ∈ availableNeighbors G S y x) : ¬ G.Adj a b := by
  obtain ⟨hxa, hay, haS⟩ := (mem_availableNeighbors G).mp ha
  obtain ⟨hyb, hbx, hbS⟩ := (mem_availableNeighbors G).mp hb
  intro hab
  exact hno (hasAvoidingPath_three hxa hab hyb.symm hbx.symm hxy hay hx haS hbS hy)

lemma availableNeighbors_not_adj_start {S : Finset V} {x y : V}
    (hxy : x ≠ y) (hx : x ∉ S) (hy : y ∉ S)
    (hno : ¬ HasAvoidingPath G x y 2 S)
    {z : V} (hz : z ∈ availableNeighbors G S y x) : ¬ G.Adj x z := by
  obtain ⟨hyz, _, hzS⟩ := (mem_availableNeighbors G).mp hz
  intro hxz
  exact hno (hasAvoidingPath_two_of_commonNeighbor hxy hxz hyz hx hy hzS)

/-- A nonneighbor set outside Y improves the induced-degree deletion estimate. -/
lemma degree_induce_lower_of_nonadj (X Y : Finset V) (x : V)
    (hXY : Disjoint X Y) (hxX : x ∉ X) (hxY : x ∉ Y)
    (z : (Y : Set V))
    (hnX : ∀ w ∈ X, ¬ G.Adj z.val w) (hnx : ¬G.Adj z.val x) :
    G.degree z.val + X.card + Y.card + 1 ≤
      (G.induce (Y : Set V)).degree z + Fintype.card V := by
  classical
  let N := G.neighborFinset z.val
  have hNX : Disjoint (N \ Y) X := by
    apply Finset.disjoint_left.mpr
    intro w hw hwX
    exact hnX w hwX ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hw).1)
  have hNY : Disjoint (N \ Y) Y := by
    exact disjoint_left.mpr (fun w hw hwY => (mem_sdiff.mp hw).2 hwY)
  have hxN : x ∉ N \ Y := by
    intro hx
    exact hnx ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1)
  have hu : ((N \ Y) ∪ X ∪ Y).card + 1 ≤ Fintype.card V := by
    have hx : x ∉ (N \ Y) ∪ X ∪ Y := by simp [hxN, hxX, hxY]
    have h := card_le_card (subset_univ (insert x ((N \ Y) ∪ X ∪ Y)))
    rw [card_insert_of_notMem hx, card_univ] at h
    exact h
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hNY, hXY⟩),
    card_union_of_disjoint hNX] at hu
  have hp := card_sdiff_add_card_inter N Y
  have hmap := congrArg Finset.card (G.map_neighborFinset_induce z)
  simp only [card_map, card_neighborFinset_eq_degree, Finset.toFinset_coe] at hmap
  have hN : N.card = G.degree z.val := G.card_neighborFinset_eq_degree _
  have hmap' : (G.induce (Y : Set V)).degree z = (N ∩ Y).card := by
    simpa only [N, SimpleGraph.degree, SimpleGraph.neighborFinset,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] using hmap
  omega

/-- Failure of one short connector forces a sufficiently large palette. -/
theorem palette_of_failed_connector {K : Type*} (k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hscale : ScalarScale (k : ℝ) ε (Fintype.card V))
    (hnear : (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 <
      ε ^ 6 * (Fintype.card V : ℝ) ^ 2)
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2 <
      (G.degree v : ℝ))
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c)
    (S : Finset V) (hS : S.card ≤ 5 * k) (x y : V) (hxy : x ≠ y)
    (hx : x ∉ S) (hy : y ∉ S)
    (hno2 : ¬HasAvoidingPath G x y 2 S) (hno3 : ¬HasAvoidingPath G x y 3 S)
    (hsize : (availableNeighbors G S y x).card ≤ (availableNeighbors G S x y).card) :
    bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 ≤
      (usedColors c : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  let X := availableNeighbors G S x y
  let Y := availableNeighbors G S y x
  let H := G.induce (Y : Set V)
  let R : ℝ := n / 2 - 3 * ε ^ 3 * n - 10 * k - 5 / 2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : 0 ≤ ε ^ 3 := by positivity
  have han : 0 ≤ ε ^ 3 * n := mul_nonneg ha hn
  have hXY : Disjoint X Y := availableNeighbors_disjoint G hxy hx hy hno2
  have hxX : x ∉ X := by simp [X, availableNeighbors]
  have hxY : x ∉ Y := by simp [Y, availableNeighbors]
  have hYsmall : (Y.card : ℝ) ≤ n / 2 := by
    have h := card_le_univ (X ∪ Y)
    rw [card_union_of_disjoint hXY] at h
    have hR : (X.card : ℝ) + Y.card ≤ n := by
      dsimp [n]
      exact_mod_cast h
    have hsR : (Y.card : ℝ) ≤ X.card := by exact_mod_cast hsize
    linarith
  have hSreal : (S.card : ℝ) ≤ 5 * (k : ℝ) := by exact_mod_cast hS
  have hYlower : n / 2 - ε ^ 3 * n - 3 / 2 - 5 * k ≤ (Y.card : ℝ) := by
    have h := card_availableNeighbors G S y x
    have hR : (G.degree y : ℝ) ≤ Y.card + (S.card : ℝ) + 1 := by exact_mod_cast h
    linarith [hdegree y]
  have hXlower : n / 2 - ε ^ 3 * n - 3 / 2 - 5 * k ≤ (X.card : ℝ) :=
    hYlower.trans (Nat.cast_le.mpr hsize)
  have hdegr : ∀ z : (Y : Set V), R ≤ (H.degree z : ℝ) := by
    intro z
    have h := degree_induce_lower_of_nonadj G X Y x hXY hxX hxY z
      (fun w hw hzw => availableNeighbors_no_cross G hxy hx hy hno3 hw z.property hzw.symm)
      (fun hzx => availableNeighbors_not_adj_start G hxy hx hy hno2 z.property hzx.symm)
    have hR : (G.degree z.val : ℝ) + X.card + Y.card + 1 ≤ (H.degree z : ℝ) + n := by
      dsimp [n, H]
      exact_mod_cast h
    dsimp [R]
    linarith [hdegree z.val]
  have hYpos : 0 < Y.card := by
    have hs := hscale.near_common
    have ho := hscale.order
    have hYR : (0 : ℝ) < Y.card := by dsimp [n] at *; nlinarith
    exact_mod_cast hYR
  letI : Nonempty (Y : Set V) := (Finset.nonempty_coe_sort.mpr (card_pos.mp hYpos))
  have horder : Fintype.card (Y : Set V) = Y.card := Fintype.card_coe Y
  have hdense : ∀ z : (Y : Set V), (Y.card : ℝ) / 2 + 5 * k ≤ (H.degree z : ℝ) := by
    intro z
    have hz := hdegr z
    have hs := hscale.near_common
    dsimp [R, n] at *
    linarith
  have hmin : 2 * k - 1 ≤ H.minDegree := by
    apply H.le_minDegree_of_forall_le_degree
    intro z
    have hz := hdense z
    have hy0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    have ht : (2 * k - 1 : ℝ) ≤ (H.degree z : ℝ) := by linarith
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_sub (by omega : 1 ≤ 2 * k), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using ht
  have hcommon : ∀ z w : (Y : Set V), z ≠ w →
      2 * k - 1 ≤ (H.neighborFinset z ∩ H.neighborFinset w).card := by
    intro z w _
    have h := commonNeighbors_lower_of_degree H ((Y.card : ℝ) / 2 + 5 * k) hdense z w
    rw [horder] at h
    have ht : (2 * k - 1 : ℝ) ≤ ((H.neighborFinset z ∩ H.neighborFinset w).card : ℝ) := by
      linarith
    apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_sub (by omega : 1 ≤ 2 * k), Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using ht
  let I : Copy H G := (Embedding.induce (Y : Set V)).toCopy
  let cY := c ∘ I.mapEdgeSet
  have hci : Function.Injective cY :=
    color_injective_of_codegree (by omega : 3 ≤ k) hmin hcommon cY (hc.comap I)
  have hpalette : (H.edgeFinset.card : ℝ) ≤ (usedColors c : ℝ) := by
    have he : H.edgeFinset.card = EdgeCount H := by
      simp [EdgeCount, Nat.card_eq_fintype_card, edgeFinset_card]
    rw [he, ← usedColors_injective hci]
    exact Nat.cast_le.mpr (usedColors_comap_le c I)
  have hcount := degree_count_lower H R hdegr
  rw [horder] at hcount
  have hL0 : 0 ≤ n / 2 - ε ^ 3 * n - 6 * k := by
    have hs := hscale.near_common
    dsimp [n] at *
    linarith
  have hR0 : 0 ≤ n / 2 - 3 * ε ^ 3 * n - 11 * k := by
    have hs := hscale.near_common
    dsimp [n] at *
    linarith
  have hprod := near_neighborhood_product n k (ε ^ 3) Y.card R hn hkR ha
    hYlower (by rfl) hL0 hR0
  have hq : n ^ 2 / 8 - 2 * ε ^ 3 * n ^ 2 - 10 * k * n ≤ (usedColors c : ℝ) :=
    hprod.trans (hcount.trans hpalette)
  apply near_palette_absorption n G.edgeFinset.card (ε ^ 3) k ε (usedColors c) hn ha
  · nlinarith only [hnear]
  · exact hscale.absorption
  · exact hq

private lemma avoidingPath_reverse {x y : V} {L : ℕ} {S : Finset V}
    (h : HasAvoidingPath G x y L S) : HasAvoidingPath G y x L S := by
  obtain ⟨p, hp, hl, hav⟩ := h
  exact ⟨p.reverse, hp.reverse, by simpa using hl, fun w hw => hav w (by simpa using hw)⟩

/-- The near case gives robust connectivity or the required palette already.
This is deliberately a disjunction, not an unconditional connectivity claim. -/
theorem nearConnectivity_or_palette {K : Type*} (k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hscale : ScalarScale (k : ℝ) ε (Fintype.card V))
    (hnear : (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4 <
      ε ^ 6 * (Fintype.card V : ℝ) ^ 2)
    (hdegree : ∀ v, (Fintype.card V : ℝ) / 2 - ε ^ 3 * Fintype.card V - 1 / 2 <
      (G.degree v : ℝ))
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    (bcmPotential (Fintype.card V) G.edgeFinset.card - ε * (Fintype.card V : ℝ) ^ 2 ≤
      (usedColors c : ℝ)) ∨
    (∀ S : Finset V, S.card ≤ 5 * k → ∀ x y : V, x ≠ y → x ∉ S → y ∉ S →
      HasAvoidingPath G x y 2 S ∨ HasAvoidingPath G x y 3 S) := by
  classical
  by_cases hrob : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x y : V, x ≠ y → x ∉ S → y ∉ S →
      HasAvoidingPath G x y 2 S ∨ HasAvoidingPath G x y 3 S
  · exact Or.inr hrob
  left
  push_neg at hrob
  obtain ⟨S, hS, x, y, hxy, hx, hy, hno2, hno3⟩ := hrob
  by_cases hsize : (availableNeighbors G S y x).card ≤ (availableNeighbors G S x y).card
  · exact palette_of_failed_connector G k hk ε hε hscale hnear hdegree c hc
      S hS x y hxy hx hy hno2 hno3 hsize
  · exact palette_of_failed_connector G k hk ε hε hscale hnear hdegree c hc
      S hS y x hxy.symm hy hx
      (fun h => hno2 (avoidingPath_reverse G h))
      (fun h => hno3 (avoidingPath_reverse G h)) (le_of_not_ge hsize)

end Erdos809.LongOddCycles
