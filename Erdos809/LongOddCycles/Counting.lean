module
public import Erdos809.LongOddCycles.Definitions
public import Erdos809.Source.DegreePruning
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

@[expose] public section

/-! Palette and incident-edge counting, with actual used colors and original
host edges. Selected graphs are only used via adjacency-preserving copies. -/
namespace Erdos809.LongOddCycles
open SimpleGraph Finset

lemma card_le_usedColors_of_injOn {V K : Type*} [Finite V] {G : SimpleGraph V}
    (c : G.edgeSet → K) (S : Finset G.edgeSet) (hc : Set.InjOn c S) :
    S.card ≤ usedColors c := by
  calc
    S.card = (c '' (S : Set G.edgeSet)).ncard := by
      rw [hc.ncard_image, Set.ncard_coe_finset]
    _ ≤ (Set.range c).ncard :=
      Set.ncard_le_ncard (Set.image_subset_range _ _) (Set.finite_range c)

lemma edgeCount_le_usedColors_of_restrict_injective {V K : Type*} [Finite V]
    {G H : SimpleGraph V} (hHG : H ≤ G) (c : G.edgeSet → K)
    (hi : Function.Injective (c ∘ (Copy.ofLE H G hHG).mapEdgeSet)) :
    EdgeCount H ≤ usedColors c := by
  rw [← usedColors_injective hi]
  exact usedColors_comap_le c _

/-- Keep precisely the edges touching A whose endpoints both avoid B. -/
def touchingGraph {V : Type*} (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∈ A ∨ y ∈ A) ∧ x ∉ B ∧ y ∉ B
  symm := ⟨by tauto⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

instance touchingGraph_decidable {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    DecidableRel (touchingGraph G A B).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ (x ∈ A ∨ y ∈ A) ∧ x ∉ B ∧ y ∉ B))

@[simp] lemma touchingGraph_adj {V : Type*} (G : SimpleGraph V) (A B : Finset V) (x y : V) :
    (touchingGraph G A B).Adj x y ↔ G.Adj x y ∧ (x ∈ A ∨ y ∈ A) ∧ x ∉ B ∧ y ∉ B :=
  Iff.rfl

lemma touchingGraph_le {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    touchingGraph G A B ≤ G := fun _ _ h => h.1

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma touchingGraph_degree_lower (A B : Finset V) {v : V} (hvA : v ∈ A) (hvB : v ∉ B) :
    G.degree v ≤ (touchingGraph G A B).degree v + B.card := by
  classical
  have he : (touchingGraph G A B).neighborFinset v = G.neighborFinset v \ B := by
    ext w
    simp [mem_neighborFinset, touchingGraph_adj, hvA, hvB]
  have h := card_le_card_sdiff_add_card (s := G.neighborFinset v) (t := B)
  rw [← he, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h
  exact h

lemma touchingGraph_count (A B : Finset V) (hAB : Disjoint A B) (d : ℝ)
    (hd : ∀ v ∈ A, d ≤ (G.degree v : ℝ)) (hBd : (B.card : ℝ) ≤ d) :
    (A.card : ℝ) * (d - B.card) / 2 ≤ (EdgeCount (touchingGraph G A B) : ℝ) := by
  classical
  let H := touchingGraph G A B
  have hl : (A.card : ℝ) * (d - B.card) ≤ ∑ v ∈ A, (H.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ A, (d - B.card) := by simp [mul_sub]
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        have hb : v ∉ B := fun hb => Finset.disjoint_left.mp hAB hv hb
        have hg := touchingGraph_degree_lower G A B hv hb
        have hgR : (G.degree v : ℝ) ≤ (H.degree v : ℝ) + B.card := by exact_mod_cast hg
        linarith [hd v hv]
  have hs : (∑ v ∈ A, (H.degree v : ℝ)) ≤ ∑ v, (H.degree v : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hh := congrArg (fun a : ℕ => (a : ℝ)) H.sum_degrees_eq_twice_card_edges
  have he : EdgeCount H = H.edgeFinset.card := by
    simp [EdgeCount, Nat.card_eq_fintype_card, edgeFinset_card]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hh
  rw [show touchingGraph G A B = H from rfl, he]
  linarith

lemma card_edgeFinset_induce_eq_filter (A : Finset V) :
    (G.induce (A : Set V)).edgeFinset.card =
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ A)).card := by
  classical
  have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (A : Set V)))
  have heq : G.edgeFinset.filter (fun e => e.toFinset ⊆ A) = G.edgeFinset ∩ A.sym2 := by
    simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]
  rw [heq]
  simpa only [card_map, Finset.toFinset_coe, edgeFinset_card,
    ← Nat.card_eq_fintype_card] using h

lemma edgeCount_le_half_order_sq :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  have h := G.card_edgeFinset_le_card_choose_two
  have hc : (G.edgeFinset.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℝ) :=
    Nat.cast_le.mpr h
  rw [Nat.cast_choose_two] at hc
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]

lemma incident_edge_partition (A : Finset V) :
    G.edgeFinset.card = (touchingGraph G A ∅).edgeFinset.card +
      (G.induce ((univ \ A : Finset V) : Set V)).edgeFinset.card := by
  classical
  have he : (touchingGraph G A ∅).edgeFinset =
      G.edgeFinset.filter (fun e => ¬e.toFinset ⊆ univ \ A) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [mem_edgeFinset, touchingGraph_adj, Finset.subset_iff,
        Sym2.mem_toFinset, not_and_or]
  rw [he, card_edgeFinset_induce_eq_filter]
  exact (card_filter_add_card_filter_not (s := G.edgeFinset)
    (p := fun e => e.toFinset ⊆ univ \ A)).symm.trans (by omega)

lemma incident_edge_count (A : Finset V) :
    (G.edgeFinset.card : ℝ) -
      ((Fintype.card V : ℝ) - A.card) ^ 2 / 2 ≤
      (EdgeCount (touchingGraph G A ∅) : ℝ) := by
  classical
  have hp := incident_edge_partition G A
  have ho := edgeCount_le_half_order_sq (G.induce ((univ \ A : Finset V) : Set V))
  have horder : Fintype.card ((univ \ A : Finset V) : Set V) =
      Fintype.card V - A.card := by
    have he : Fintype.card ((univ \ A : Finset V) : Set V) = (univ \ A : Finset V).card :=
      @Fintype.card_coe V (univ \ A) _
    rw [he, card_sdiff_of_subset (subset_univ _), card_univ]
  rw [horder] at ho
  have hA : A.card ≤ Fintype.card V := card_le_univ _
  rw [Nat.cast_sub hA] at ho
  have hpR : (G.edgeFinset.card : ℝ) =
      ((touchingGraph G A ∅).edgeFinset.card : ℝ) +
        (G.induce ((univ \ A : Finset V) : Set V)).edgeFinset.card := by exact_mod_cast hp
  have he : EdgeCount (touchingGraph G A ∅) = (touchingGraph G A ∅).edgeFinset.card := by
    simp [EdgeCount, Nat.card_eq_fintype_card, edgeFinset_card]
  rw [he]
  linarith

lemma good_edge_count (p q : V) (hpq : G.Adj p q) (d : ℝ)
    (hd : ∀ v, d ≤ (G.degree v : ℝ)) (hd2 : 2 ≤ d) :
    (d - 1) * (d - 2) / 2 ≤
      (EdgeCount (touchingGraph G ((G.neighborFinset p).erase q) {p, q}) : ℝ) := by
  classical
  let A := (G.neighborFinset p).erase q
  have hAB : Disjoint A {p, q} := by
    apply Finset.disjoint_left.mpr
    intro v hv hvpq
    obtain ⟨hvq, hvp⟩ := mem_erase.mp hv
    rcases (show v = p ∨ v = q by simpa using hvpq) with rfl | rfl
    · exact G.irrefl ((G.mem_neighborFinset _ _).mp hvp)
    · exact hvq rfl
  have hcardB : ({p, q} : Finset V).card = 2 := by simp [hpq.ne]
  have ha : A.card + 1 = G.degree p := by
    simpa [A] using card_erase_add_one ((G.mem_neighborFinset _ _).mpr hpq)
  have haR : (A.card : ℝ) + 1 = G.degree p := by exact_mod_cast ha
  have hA : d - 1 ≤ (A.card : ℝ) := by linarith [hd p]
  have h := touchingGraph_count G A {p, q} hAB d (fun v _ => hd v) (by simpa [hcardB])
  rw [hcardB] at h
  have hm := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ d - 2)
  norm_num at h
  linarith

lemma degree_count_lower (d : ℝ) (hd : ∀ v, d ≤ (G.degree v : ℝ)) :
    (Fintype.card V : ℝ) * d / 2 ≤ (G.edgeFinset.card : ℝ) := by
  have h : (Fintype.card V : ℝ) * d ≤ ∑ v, (G.degree v : ℝ) := by
    calc
      _ = ∑ _v : V, d := by simp
      _ ≤ _ := sum_le_sum (fun v _ => hd v)
  have hs := congrArg (fun a : ℕ => (a : ℝ)) G.sum_degrees_eq_twice_card_edges
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hs
  linarith

lemma commonNeighbors_lower_of_degree (d : ℝ) (hd : ∀ v, d ≤ (G.degree v : ℝ))
    (x y : V) : 2 * d - Fintype.card V ≤
      ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) := by
  have h := card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  have hu := card_le_univ (G.neighborFinset x ∪ G.neighborFinset y)
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h
  have hR : ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) +
      (G.neighborFinset x ∩ G.neighborFinset y).card = (G.degree x : ℝ) + G.degree y := by
    exact_mod_cast h
  have huR : ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hu
  linarith [hd x, hd y]

end Erdos809.LongOddCycles
