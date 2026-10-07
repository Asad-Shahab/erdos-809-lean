module
public import Erdos809.Source.RobustPaths
public import Erdos809.Source.NearCutParameters
public import Mathlib.Data.Finset.Max
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Counting for the near-cut branch

All neighborhoods and missing edges refer to the original graph. The selected
sets below are intended for the explicit seven-cycle construction; no coloring
or properness assumption is used by these counting lemmas.
-/

noncomputable section

namespace Erdos809.Source

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Missing neighbors in a specified opposite side. -/
def crossDefect (B : Finset V) (v : V) : ℕ :=
  (B.filter fun w => ¬ G.Adj v w).card

omit [DecidableEq V] in
lemma cross_degree_add_defect (B : Finset V) (v : V) :
    (B.filter (G.Adj v)).card + crossDefect G B v = B.card :=
  card_filter_add_card_filter_not _

omit [DecidableEq V] in
lemma crossDefect_mono {A B : Finset V} (hAB : A ⊆ B) (v : V) :
    crossDefect G A v ≤ crossDefect G B v :=
  card_le_card (filter_subset_filter _ hAB)

omit [DecidableEq V] in
/-- Count a relation by its first-coordinate fibers. -/
lemma card_rel_interedges_eq_sum (r : V → V → Prop) [DecidableRel r]
    (A B : Finset V) :
    (Rel.interedges r A B).card = ∑ v ∈ A, (B.filter (r v)).card := by
  simp only [Rel.interedges, card_eq_sum_ones, sum_filter, sum_product]

lemma card_interedges_eq_sum (A B : Finset V) :
    (G.interedges A B).card = ∑ v ∈ A, (B.filter (G.Adj v)).card :=
  card_rel_interedges_eq_sum G.Adj A B

lemma sum_crossDefect (A B : Finset V) :
    (∑ v ∈ A, crossDefect G B v) =
      (Rel.interedges (fun u v => ¬ G.Adj u v) A B).card :=
  (card_rel_interedges_eq_sum (fun u v => ¬ G.Adj u v) A B).symm

omit [DecidableEq V] in
lemma missing_cross_edges_comm (A B : Finset V) :
    (Rel.interedges (fun u v => ¬ G.Adj u v) A B).card =
      (Rel.interedges (fun u v => ¬ G.Adj u v) B A).card :=
  letI : Std.Symm (fun u v => ¬ G.Adj u v) :=
    ⟨fun _ _ h hab => h hab.symm⟩
  Rel.card_interedges_comm A B

/-- Exceptional vertices on both sides of the cut. -/
def cutBad (P Q : Finset V) (d : ℝ) : Finset V := by
  classical
  exact (P.filter fun v => d < crossDefect G Q v) ∪
    (Q.filter fun v => d < crossDefect G P v)

lemma bad_side_mass_le (A B : Finset V) (d : ℝ) :
    ((A.filter fun v => d < crossDefect G B v).card : ℝ) * d ≤
      (Rel.interedges (fun u v => ¬ G.Adj u v) A B).card := by
  classical
  calc
    _ = ∑ _v ∈ A.filter (fun v => d < crossDefect G B v), d := by simp
    _ ≤ ∑ v ∈ A.filter (fun v => d < crossDefect G B v), (crossDefect G B v : ℝ) :=
      sum_le_sum fun v hv => (mem_filter.mp hv).2.le
    _ ≤ ∑ v ∈ A, (crossDefect G B v : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [← Nat.cast_sum, sum_crossDefect]

/-- Each missing cross edge pays for at most two exceptional incidences. -/
lemma cutBad_mass_le (P Q : Finset V) {d : ℝ} (hd : 0 ≤ d) :
    ((cutBad G P Q d).card : ℝ) * d ≤
      2 * (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card := by
  classical
  have hc : ((cutBad G P Q d).card : ℝ) ≤
      (P.filter (fun v => d < crossDefect G Q v)).card +
        (Q.filter (fun v => d < crossDefect G P v)).card := by
    exact_mod_cast card_union_le
      (P.filter fun v => d < crossDefect G Q v)
      (Q.filter fun v => d < crossDefect G P v)
  have hp := bad_side_mass_le G P Q d
  have hq := bad_side_mass_le G Q P d
  rw [← missing_cross_edges_comm G P Q] at hq
  have hm := mul_le_mul_of_nonneg_right hc hd
  nlinarith only [hm, hp, hq]

lemma cutBad_card_le {P Q : Finset V} {τ n : ℝ}
    (hτ : 0 < τ) (hn : 0 < n)
    (hmiss : ((Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card : ℝ) ≤
      τ ^ 3 * n ^ 2) :
    ((cutBad G P Q (τ * n)).card : ℝ) ≤ 2 * τ ^ 2 * n := by
  apply (mul_le_mul_iff_left₀ (mul_pos hτ hn)).mp
  calc
    _ ≤ (2 : ℝ) * (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card :=
      cutBad_mass_le G P Q (mul_pos hτ hn).le
    _ ≤ 2 * (τ ^ 3 * n ^ 2) := by linarith only [hmiss]
    _ = _ := by ring

lemma typical_of_not_cutBad_left {P Q : Finset V} {d : ℝ} {v : V}
    (hvP : v ∈ P) (hv : v ∉ cutBad G P Q d) : (crossDefect G Q v : ℝ) ≤ d := by
  classical
  by_contra h
  exact hv (mem_union_left _ (mem_filter.mpr ⟨hvP, lt_of_not_ge h⟩))

lemma typical_of_not_cutBad_right {P Q : Finset V} {d : ℝ} {v : V}
    (hvQ : v ∈ Q) (hv : v ∉ cutBad G P Q d) : (crossDefect G P v : ℝ) ≤ d := by
  classical
  by_contra h
  exact hv (mem_union_right _ (mem_filter.mpr ⟨hvQ, lt_of_not_ge h⟩))

/-- Common neighbors lose at most the sum of the two defects. -/
lemma common_neighbors_lower (B : Finset V) (u v : V) :
    (B.card : ℝ) - crossDefect G B u - crossDefect G B v ≤
      (B.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
  let A := B.filter (G.Adj u)
  let C := B.filter (G.Adj v)
  have hsub : A ∪ C ⊆ B := union_subset (filter_subset _ _) (filter_subset _ _)
  have hcard := card_union_add_card_inter A C
  have hbound := card_le_card hsub
  have hdu := cross_degree_add_defect G B u
  have hdv := cross_degree_add_defect G B v
  have hi : A ∩ C = B.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    ext w
    simp [A, C, and_assoc, and_left_comm]
  rw [hi] at hcard
  have hcardR : ((A ∪ C).card : ℝ) +
      (B.filter fun w => G.Adj u w ∧ G.Adj v w).card = A.card + C.card := by
    exact_mod_cast hcard
  have hboundR : ((A ∪ C).card : ℝ) ≤ B.card := by exact_mod_cast hbound
  have hduR : (A.card : ℝ) + crossDefect G B u = B.card := by exact_mod_cast hdu
  have hdvR : (C.card : ℝ) + crossDefect G B v = B.card := by exact_mod_cast hdv
  linarith

lemma common_neighbors_from_degree (B : Finset V) (u v : V) :
    ((B.filter (G.Adj v)).card : ℝ) - crossDefect G B u ≤
      (B.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
  have h := common_neighbors_lower G B u v
  have hd : ((B.filter (G.Adj v)).card : ℝ) + crossDefect G B v = B.card := by
    exact_mod_cast cross_degree_add_defect G B v
  linarith

/-- Left endpoints of the selected edge clique. -/
def nearCutS (P T : Finset V) (u v : V) : Finset V :=
  (P.filter fun x => G.Adj u x ∧ G.Adj v x) \ T

/-- Right endpoints exclude both trigger vertices and every exceptional vertex. -/
def nearCutR (Q T : Finset V) (u v : V) : Finset V := Q \ (T ∪ {u, v})

lemma nearCutS_subset (P T : Finset V) (u v : V) : nearCutS G P T u v ⊆ P :=
  sdiff_subset.trans (filter_subset _ _)

lemma nearCutR_subset (Q T : Finset V) (u v : V) : nearCutR Q T u v ⊆ Q :=
  sdiff_subset

lemma nearCutS_card_lower {P T : Finset V} {u v : V} {d : ℝ}
    (hu : (crossDefect G P u : ℝ) ≤ d)
    (hv : (P.card : ℝ) / 2 - T.card < (P.filter (G.Adj v)).card) :
    (P.card : ℝ) / 2 - d - 2 * T.card < (nearCutS G P T u v).card := by
  have hcommon := common_neighbors_from_degree G P u v
  have hdelete : ((P.filter fun x => G.Adj u x ∧ G.Adj v x).card : ℝ) ≤
      (nearCutS G P T u v).card + (T.card : ℝ) := by
    exact_mod_cast card_le_card_sdiff_add_card
      (s := P.filter fun x => G.Adj u x ∧ G.Adj v x) (t := T)
  linarith

lemma nearCutR_card_lower (Q T : Finset V) (u v : V) :
    (Q.card : ℝ) - T.card - 2 ≤ (nearCutR Q T u v).card := by
  have hunion : (T ∪ {u, v}).card ≤ T.card + 2 :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_le_two _)
  have hdelete : Q.card ≤ (nearCutR Q T u v).card + (T ∪ {u, v}).card :=
    card_le_card_sdiff_add_card
  have hdeleteR : (Q.card : ℝ) ≤ (nearCutR Q T u v).card + (T ∪ {u, v}).card := by
    exact_mod_cast hdelete
  have hunionR : ((T ∪ {u, v}).card : ℝ) ≤ T.card + 2 := by exact_mod_cast hunion
  linarith

lemma degree_into_subset_lower {Q R : Finset V} (hRQ : R ⊆ Q) (v : V) {d : ℝ}
    (hv : (crossDefect G Q v : ℝ) ≤ d) :
    (R.card : ℝ) - d ≤ (R.filter (G.Adj v)).card := by
  have hm : (crossDefect G R v : ℝ) ≤ crossDefect G Q v := by
    exact_mod_cast crossDefect_mono G hRQ v
  have hd : ((R.filter (G.Adj v)).card : ℝ) + crossDefect G R v = R.card := by
    exact_mod_cast cross_degree_add_defect G R v
  linarith

/-- All selected left vertices are typical, so each pays the same lower degree. -/
lemma selected_edges_lower {S Q R : Finset V} {d : ℝ}
    (hRQ : R ⊆ Q) (htyp : ∀ v ∈ S, (crossDefect G Q v : ℝ) ≤ d) :
    (S.card : ℝ) * ((R.card : ℝ) - d) ≤ (G.interedges S R).card := by
  rw [card_interedges_eq_sum]
  push_cast
  calc
    _ = ∑ _v ∈ S, ((R.card : ℝ) - d) := by simp; ring
    _ ≤ _ := sum_le_sum fun v hv => degree_into_subset_lower G hRQ v (htyp v hv)

/-- A finite maximum cut exists, uniformly over the graph. -/
lemma exists_maximum_cut [Fintype V] :
    ∃ P : Finset V, ∀ A : Finset V,
      (G.interedges A Aᶜ).card ≤ (G.interedges P Pᶜ).card := by
  classical
  obtain ⟨P, _, hP⟩ := (univ : Finset (Finset V)).exists_max_image
    (fun A => (G.interedges A Aᶜ).card) (by simp)
  exact ⟨P, fun A => hP A (mem_univ _)⟩

omit [DecidableEq V] in
lemma card_interedges_comm (A B : Finset V) :
    (G.interedges A B).card = (G.interedges B A).card :=
  letI : Std.Symm G.Adj := ⟨fun _ _ h => h.symm⟩
  Rel.card_interedges_comm A B

lemma interedges_insert_left (A B : Finset V) (v : V) :
    G.interedges (insert v A) B = G.interedges {v} B ∪ G.interedges A B := by
  ext p
  simp only [mem_interedges_iff, mem_insert, mem_singleton, mem_union]
  tauto

lemma card_interedges_insert_left {A B : Finset V} {v : V} (hv : v ∉ A) :
    (G.interedges (insert v A) B).card =
      (B.filter (G.Adj v)).card + (G.interedges A B).card := by
  rw [interedges_insert_left, card_union_of_disjoint]
  · rw [card_interedges_eq_sum]
    simp
  · apply G.interedges_disjoint_left
    simpa using hv

lemma card_interedges_insert_right {A B : Finset V} {v : V} (hv : v ∉ B) :
    (G.interedges A (insert v B)).card =
      (A.filter (G.Adj v)).card + (G.interedges A B).card := by
  rw [card_interedges_comm G A (insert v B), card_interedges_insert_left G hv,
    card_interedges_comm G B A]

/-- Exact change in crossing edges when one vertex changes sides. -/
lemma cut_switch_identity {P Q : Finset V} {v : V} (hvP : v ∈ P) (hvQ : v ∉ Q) :
    (G.interedges (P.erase v) (insert v Q)).card + (Q.filter (G.Adj v)).card =
      (G.interedges P Q).card + (P.filter (G.Adj v)).card := by
  have hself : (P.erase v).filter (G.Adj v) = P.filter (G.Adj v) := by
    ext w
    simp only [mem_filter, mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · exact fun h => ⟨⟨Ne.symm h.2.ne, h.1⟩, h.2⟩
  have hold := card_interedges_insert_left G (B := Q) (notMem_erase v P)
  rw [insert_erase hvP] at hold
  rw [card_interedges_insert_right G hvQ, hself]
  omega

/-- Local optimality follows from the full finite maximum-cut property. -/
lemma maximum_cut_local_left [Fintype V] {P : Finset V}
    (hmax : ∀ A : Finset V, (G.interedges A Aᶜ).card ≤ (G.interedges P Pᶜ).card)
    {v : V} (hv : v ∈ P) :
    (P.filter (G.Adj v)).card ≤ (Pᶜ.filter (G.Adj v)).card := by
  have hswitch := cut_switch_identity G hv (show v ∉ Pᶜ by simpa)
  have hcomp : (P.erase v)ᶜ = insert v Pᶜ := by
    ext w
    simp only [mem_compl, mem_erase, mem_insert]
    tauto
  have h := hmax (P.erase v)
  rw [hcomp] at h
  omega

lemma maximum_cut_local_right [Fintype V] {P : Finset V}
    (hmax : ∀ A : Finset V, (G.interedges A Aᶜ).card ≤ (G.interedges P Pᶜ).card)
    {v : V} (hv : v ∈ Pᶜ) :
    (Pᶜ.filter (G.Adj v)).card ≤ (P.filter (G.Adj v)).card := by
  have hmax' : ∀ A : Finset V,
      (G.interedges A Aᶜ).card ≤ (G.interedges Pᶜ Pᶜᶜ).card := by
    intro A
    simpa only [compl_compl, card_interedges_comm G Pᶜ P] using hmax A
  simpa only [compl_compl] using maximum_cut_local_left G hmax' hv

/-- An internal edge with a typical first endpoint and a large opposite degree
at the second endpoint. The latter endpoint is allowed to be exceptional. -/
def NearCutTrigger (A B T : Finset V) : Prop :=
  ∃ u ∈ A, u ∉ T ∧ ∃ v ∈ A, G.Adj u v ∧
    (B.card : ℝ) / 2 - T.card < (B.filter (G.Adj v)).card

lemma no_trigger_internal_covered {A B T : Finset V}
    (hno : ¬ NearCutTrigger G A B T)
    (hgood : ∀ v ∈ A, v ∉ T →
      (B.card : ℝ) / 2 - T.card < (B.filter (G.Adj v)).card)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (huv : G.Adj u v) :
    u ∈ T ∨ v ∈ T := by
  by_cases hut : u ∈ T
  · exact Or.inl hut
  · exact Or.inr (by
      by_contra hvt
      exact hno ⟨u, hu, hut, v, hv, huv, hgood v hv hvt⟩)

/-- If every internal edge meets T, its unordered count is at most the
internal-degree sum over T. This form keeps the factor two explicit. -/
lemma internal_incidence_cover {A T : Finset V}
    (hcover : ∀ u ∈ A, ∀ v ∈ A, G.Adj u v → u ∈ T ∨ v ∈ T) :
    (G.interedges A A).card ≤ 2 * ∑ v ∈ A ∩ T, (A.filter (G.Adj v)).card := by
  have hsub : G.interedges A A ⊆
      G.interedges (A ∩ T) A ∪ G.interedges A (A ∩ T) := by
    intro p hp
    obtain ⟨hu, hv, huv⟩ := G.mem_interedges_iff.mp hp
    rcases hcover _ hu _ hv huv with hut | hvt
    · exact mem_union_left _ (G.mem_interedges_iff.mpr ⟨mem_inter.mpr ⟨hu, hut⟩, hv, huv⟩)
    · exact mem_union_right _ (G.mem_interedges_iff.mpr ⟨hu, mem_inter.mpr ⟨hv, hvt⟩, huv⟩)
  calc
    _ ≤ (G.interedges (A ∩ T) A ∪ G.interedges A (A ∩ T)).card := card_le_card hsub
    _ ≤ (G.interedges (A ∩ T) A).card + (G.interedges A (A ∩ T)).card := card_union_le _ _
    _ = _ := by rw [card_interedges_comm G A (A ∩ T), card_interedges_eq_sum]; omega

/-- Missing incidences at exceptional vertices count each missing edge once,
apart from edges with both endpoints exceptional. -/
lemma missing_incidence_bound (P Q T : Finset V) :
    (∑ v ∈ P ∩ T, crossDefect G Q v) + (∑ v ∈ Q ∩ T, crossDefect G P v) ≤
      (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card +
        (P ∩ T).card * (Q ∩ T).card := by
  let A := Rel.interedges (fun u v => ¬ G.Adj u v) (P ∩ T) Q
  let B := Rel.interedges (fun u v => ¬ G.Adj u v) P (Q ∩ T)
  let M := Rel.interedges (fun u v => ¬ G.Adj u v) P Q
  have hunion : A ∪ B ⊆ M := union_subset
    (Rel.interedges_mono inter_subset_left Subset.rfl)
    (Rel.interedges_mono Subset.rfl inter_subset_left)
  have hinter : A ∩ B ⊆ (P ∩ T) ×ˢ (Q ∩ T) := by
    intro p hp
    obtain ⟨ha, hb⟩ := mem_inter.mp hp
    exact mem_product.mpr ⟨(Rel.mem_interedges_iff.mp ha).1,
      (Rel.mem_interedges_iff.mp hb).2.1⟩
  rw [sum_crossDefect, sum_crossDefect, missing_cross_edges_comm G (Q ∩ T) P]
  change A.card + B.card ≤ M.card + (P ∩ T).card * (Q ∩ T).card
  calc
    _ = (A ∪ B).card + (A ∩ B).card := (card_union_add_card_inter A B).symm
    _ ≤ M.card + ((P ∩ T) ×ˢ (Q ∩ T)).card :=
      Nat.add_le_add (card_le_card hunion) (card_le_card hinter)
    _ = _ := by rw [card_product]

/-- An exceptional vertex pays at least twice |T| more missing edges than
internal edges if the trigger is absent. Both cases are explicit. -/
lemma no_trigger_defect_surplus {A B T : Finset V} {d : ℝ}
    (hno : ¬ NearCutTrigger G A B T)
    (hlocal : ∀ v ∈ A, (A.filter (G.Adj v)).card ≤ (B.filter (G.Adj v)).card)
    (hbad : ∀ v ∈ A ∩ T, d < (crossDefect G B v : ℝ))
    (hd : 3 * (T.card : ℝ) ≤ d) {v : V} (hv : v ∈ A ∩ T) :
    ((A.filter (G.Adj v)).card : ℝ) + 2 * T.card ≤ crossDefect G B v := by
  have hvA := (mem_inter.mp hv).1
  by_cases hex : ∃ u ∈ A, u ∉ T ∧ G.Adj u v
  · obtain ⟨u, huA, huT, huv⟩ := hex
    have hc : ((B.filter (G.Adj v)).card : ℝ) ≤ (B.card : ℝ) / 2 - T.card := by
      apply le_of_not_gt
      exact fun h => hno ⟨u, huA, huT, v, hvA, huv, h⟩
    have hi : ((A.filter (G.Adj v)).card : ℝ) ≤ (B.filter (G.Adj v)).card := by
      exact_mod_cast hlocal v hvA
    have hdef : ((B.filter (G.Adj v)).card : ℝ) + crossDefect G B v = B.card := by
      exact_mod_cast cross_degree_add_defect G B v
    linarith
  · have hsub : A.filter (G.Adj v) ⊆ T := by
      intro u hu
      by_contra huT
      obtain ⟨huA, hvu⟩ := mem_filter.mp hu
      exact hex ⟨u, huA, huT, hvu.symm⟩
    have hi : ((A.filter (G.Adj v)).card : ℝ) ≤ T.card := by
      exact_mod_cast card_le_card hsub
    have hdef := hbad v hv
    linarith

/-- The trigger follows from local optimality and the exact missing-incidence
account, including the case when the exceptional set is empty. -/
theorem exists_trigger_of_internal_excess [Fintype V] {P Q T : Finset V} {d : ℝ}
    (hPQ : Disjoint P Q) (hpartition : P ∪ Q = univ)
    (hlocalP : ∀ v ∈ P, (P.filter (G.Adj v)).card ≤ (Q.filter (G.Adj v)).card)
    (hlocalQ : ∀ v ∈ Q, (Q.filter (G.Adj v)).card ≤ (P.filter (G.Adj v)).card)
    (hgoodP : ∀ v ∈ P, v ∉ T → (Q.card : ℝ) / 2 - T.card < (Q.filter (G.Adj v)).card)
    (hgoodQ : ∀ v ∈ Q, v ∉ T → (P.card : ℝ) / 2 - T.card < (P.filter (G.Adj v)).card)
    (hbadP : ∀ v ∈ P ∩ T, d < (crossDefect G Q v : ℝ))
    (hbadQ : ∀ v ∈ Q ∩ T, d < (crossDefect G P v : ℝ))
    (hd : 3 * (T.card : ℝ) ≤ d)
    (hexcess : ((Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card : ℝ) <
      ((G.interedges P P).card + (G.interedges Q Q).card : ℝ) / 2) :
    NearCutTrigger G P Q T ∨ NearCutTrigger G Q P T := by
  by_contra hno
  obtain ⟨hnoP, hnoQ⟩ := not_or.mp hno
  have hcoverP := internal_incidence_cover G
    (fun u hu v hv huv => no_trigger_internal_covered G hnoP hgoodP hu hv huv)
  have hcoverQ := internal_incidence_cover G
    (fun u hu v hv huv => no_trigger_internal_covered G hnoQ hgoodQ hu hv huv)
  have hcoverPR : ((G.interedges P P).card : ℝ) ≤
      2 * ∑ v ∈ P ∩ T, ((P.filter (G.Adj v)).card : ℝ) := by exact_mod_cast hcoverP
  have hcoverQR : ((G.interedges Q Q).card : ℝ) ≤
      2 * ∑ v ∈ Q ∩ T, ((Q.filter (G.Adj v)).card : ℝ) := by exact_mod_cast hcoverQ
  have hsurplusP : (∑ v ∈ P ∩ T, ((P.filter (G.Adj v)).card : ℝ)) +
      (P ∩ T).card * (2 * (T.card : ℝ)) ≤ ∑ v ∈ P ∩ T, (crossDefect G Q v : ℝ) := by
    have h := sum_le_sum (s := P ∩ T)
      (fun v hv => no_trigger_defect_surplus G hnoP hlocalP hbadP hd hv)
    simpa only [sum_add_distrib, sum_const, nsmul_eq_mul] using h
  have hsurplusQ : (∑ v ∈ Q ∩ T, ((Q.filter (G.Adj v)).card : ℝ)) +
      (Q ∩ T).card * (2 * (T.card : ℝ)) ≤ ∑ v ∈ Q ∩ T, (crossDefect G P v : ℝ) := by
    have h := sum_le_sum (s := Q ∩ T)
      (fun v hv => no_trigger_defect_surplus G hnoQ hlocalQ hbadQ hd hv)
    simpa only [sum_add_distrib, sum_const, nsmul_eq_mul] using h
  have hmissing : (∑ v ∈ P ∩ T, (crossDefect G Q v : ℝ)) +
      (∑ v ∈ Q ∩ T, (crossDefect G P v : ℝ)) ≤
      (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card +
        ((P ∩ T).card : ℝ) * (Q ∩ T).card := by
    exact_mod_cast missing_incidence_bound G P Q T
  have hparts : (P ∩ T).card + (Q ∩ T).card = T.card := by
    rw [← card_union_of_disjoint (hPQ.mono inter_subset_left inter_subset_left),
      ← union_inter_distrib_right, hpartition, univ_inter]
  have hpartsR : ((P ∩ T).card : ℝ) + (Q ∩ T).card = T.card := by exact_mod_cast hparts
  have hcharge := congrArg (fun x : ℝ => x * (2 * (T.card : ℝ))) hpartsR
  have hpT : ((P ∩ T).card : ℝ) ≤ T.card := by exact_mod_cast card_le_card inter_subset_right
  have hqT : ((Q ∩ T).card : ℝ) ≤ T.card := by exact_mod_cast card_le_card inter_subset_right
  have hprod := mul_le_mul hpT hqT (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  nlinarith only [hexcess, hcoverPR, hcoverQR, hsurplusP, hsurplusQ, hmissing,
    hcharge, hprod, sq_nonneg (T.card : ℝ)]

lemma interedges_union_left (A B C : Finset V) :
    G.interedges (A ∪ B) C = G.interedges A C ∪ G.interedges B C := by
  ext p
  simp only [mem_interedges_iff, mem_union]
  tauto

lemma card_interedges_union_left {A B : Finset V} (hAB : Disjoint A B) (C : Finset V) :
    (G.interedges (A ∪ B) C).card = (G.interedges A C).card + (G.interedges B C).card := by
  rw [interedges_union_left, card_union_of_disjoint (G.interedges_disjoint_left hAB C)]

lemma card_interedges_union_right (A : Finset V) {B C : Finset V} (hBC : Disjoint B C) :
    (G.interedges A (B ∪ C)).card = (G.interedges A B).card + (G.interedges A C).card := by
  rw [card_interedges_comm G A (B ∪ C), card_interedges_union_left G hBC A,
    card_interedges_comm G B A, card_interedges_comm G C A]

/-- Ordered internal incidences plus twice the cut count equal twice the
original unordered edge count. -/
lemma internal_cross_edge_account [Fintype V] {P Q : Finset V}
    (hPQ : Disjoint P Q) (hpartition : P ∪ Q = univ) :
    (G.interedges P P).card + (G.interedges Q Q).card +
      2 * (G.interedges P Q).card = 2 * G.edgeFinset.card := by
  have htwice : 2 * G.edgeFinset.card = (G.interedges univ univ).card := by
    simpa [interedges_def] using G.two_mul_card_edgeFinset
  rw [← hpartition, card_interedges_union_left G hPQ,
    card_interedges_union_right G P hPQ, card_interedges_union_right G Q hPQ,
    card_interedges_comm G Q P] at htwice
  omega

/-- The single-edge excess above n squared over four is stronger than the
missing-cross-edge count, for every complete bipartition. -/
lemma internal_excess_of_eligible [Fintype V] {P Q : Finset V}
    (hPQ : Disjoint P Q) (hpartition : P ∪ Q = univ)
    (helig : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card) :
    ((Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card : ℝ) <
      ((G.interedges P P).card + (G.interedges Q Q).card : ℝ) / 2 := by
  have hparts : P.card + Q.card = Fintype.card V := by
    rw [← card_union_of_disjoint hPQ, hpartition, card_univ]
  have hpartsR : (P.card : ℝ) + Q.card = Fintype.card V := by exact_mod_cast hparts
  have hcap : (P.card : ℝ) * Q.card ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
    rw [← hpartsR]
    nlinarith only [sq_nonneg ((P.card : ℝ) - Q.card)]
  have hmissing : ((G.interedges P Q).card : ℝ) +
      (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card = (P.card : ℝ) * Q.card := by
    exact_mod_cast Rel.card_interedges_add_card_interedges_compl G.Adj P Q
  have haccount : ((G.interedges P P).card : ℝ) + (G.interedges Q Q).card +
      2 * (G.interedges P Q).card = 2 * G.edgeFinset.card := by
    exact_mod_cast internal_cross_edge_account G hPQ hpartition
  linarith

/-- Balance is obtained directly from a square bound, without a square root. -/
lemma cut_balance_of_deficit {p q n M δ : ℝ} (hδ : 0 ≤ δ)
    (hpq : p + q = n) (hcap : M ≤ p * q) (hcut : n ^ 2 / 4 - δ ^ 2 ≤ M) :
    n / 2 - δ ≤ p ∧ n / 2 - δ ≤ q := by
  have hq : q = n - p := by linarith
  rw [hq] at hcap
  have hs : (p - n / 2) ^ 2 ≤ δ ^ 2 := by nlinarith only [hcap, hcut]
  have hb := abs_le_of_sq_le_sq' hs hδ
  constructor <;> linarith

/-- The final edge count absorbs the positive quadratic correction. -/
lemma near_cut_product_lower {τ n s r : ℝ} (hn : 0 ≤ n)
    (_hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 32)
    (hs : (1 / 4 - 3 * τ / 2) * n ≤ s)
    (hr : (1 / 2 - 3 * τ / 2) * n ≤ r) :
    (1 / 8 - 9 * τ / 8) * n ^ 2 ≤ s * r := by
  have ha : 0 ≤ (1 / 4 - 3 * τ / 2) * n := mul_nonneg (by linarith) hn
  have hb : 0 ≤ (1 / 2 - 3 * τ / 2) * n := mul_nonneg (by linarith) hn
  have hp := mul_le_mul hs hr hb (ha.trans hs)
  have hsq : 0 ≤ (τ * n) ^ 2 := sq_nonneg _
  nlinarith only [hp, hsq]

lemma cutBad_comm (P Q : Finset V) (d : ℝ) : cutBad G P Q d = cutBad G Q P d := by
  classical
  exact union_comm _ _

lemma bad_of_mem_cutBad_left {P Q : Finset V} {d : ℝ} {v : V}
    (hPQ : Disjoint P Q) (hvP : v ∈ P) (hv : v ∈ cutBad G P Q d) :
    d < (crossDefect G Q v : ℝ) := by
  classical
  rcases mem_union.mp hv with hv | hv
  · exact (mem_filter.mp hv).2
  · exact False.elim (disjoint_left.mp hPQ hvP (mem_filter.mp hv).1)

lemma bad_of_mem_cutBad_right {P Q : Finset V} {d : ℝ} {v : V}
    (hPQ : Disjoint P Q) (hvQ : v ∈ Q) (hv : v ∈ cutBad G P Q d) :
    d < (crossDefect G P v : ℝ) := by
  rw [cutBad_comm] at hv
  exact bad_of_mem_cutBad_left G hPQ.symm hvQ hv

/-- Every sufficiently large cut supplies all numerical parameters used by
the trigger and the explicit seven-cycle clique. -/
theorem parameters_of_large_cut [Fintype V] {P Q : Finset V} {τ : ℝ}
    (hPQ : Disjoint P Q) (hpartition : P ∪ Q = univ)
    (hτpos : 0 < τ) (hτle : τ ≤ 1 / 32)
    (hnlarge : 8 / τ ^ 3 ≤ (Fintype.card V : ℝ))
    (hcut : (1 / 4 - τ ^ 3) * (Fintype.card V : ℝ) ^ 2 ≤ (G.interedges P Q).card) :
    NearCutParameters τ (Fintype.card V) P.card Q.card
      (cutBad G P Q (τ * Fintype.card V)).card := by
  have hn : (0 : ℝ) < Fintype.card V :=
    lt_of_lt_of_le (div_pos (by norm_num) (pow_pos hτpos 3)) hnlarge
  have hparts : P.card + Q.card = Fintype.card V := by
    rw [← card_union_of_disjoint hPQ, hpartition, card_univ]
  have hpartsR : (P.card : ℝ) + Q.card = Fintype.card V := by exact_mod_cast hparts
  have hcap : (P.card : ℝ) * Q.card ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
    rw [← hpartsR]
    nlinarith only [sq_nonneg ((P.card : ℝ) - Q.card)]
  have hM : ((G.interedges P Q).card : ℝ) ≤ (P.card : ℝ) * Q.card := by
    exact_mod_cast G.card_interedges_le_mul P Q
  have hcoeff := mul_le_mul_of_nonneg_right
    (hτle.trans (show (1 : ℝ) / 32 ≤ 1 / 16 by norm_num)) (sq_nonneg τ)
  have hscaled := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Fintype.card V : ℝ))
  have hquad : τ ^ 3 * (Fintype.card V : ℝ) ^ 2 ≤
      (τ * Fintype.card V / 4) ^ 2 := by nlinarith only [hscaled]
  obtain ⟨hp, hq⟩ := cut_balance_of_deficit
    (show 0 ≤ τ * (Fintype.card V : ℝ) / 4 by positivity) hpartsR hM
    (show (Fintype.card V : ℝ) ^ 2 / 4 - (τ * Fintype.card V / 4) ^ 2 ≤
      (G.interedges P Q).card by nlinarith only [hcut, hquad])
  have hmissing : ((G.interedges P Q).card : ℝ) +
      (Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card = (P.card : ℝ) * Q.card := by
    exact_mod_cast Rel.card_interedges_add_card_interedges_compl G.Adj P Q
  have hmiss : ((Rel.interedges (fun u v => ¬ G.Adj u v) P Q).card : ℝ) ≤
      τ ^ 3 * (Fintype.card V : ℝ) ^ 2 := by nlinarith only [hmissing, hcap, hcut]
  refine ⟨hτpos, hτle, hnlarge, ?_, ?_, Nat.cast_nonneg _, cutBad_card_le G hτpos hn hmiss⟩
  · nlinarith only [hp]
  · nlinarith only [hq]

/-- A maximum cut in an eligible graph has a trigger on at least one side.
The exceptional set is the actual set defined by missing opposite neighbors. -/
theorem maximum_cut_has_trigger [Fintype V] {P : Finset V} {τ : ℝ}
    (hmax : ∀ A : Finset V, (G.interedges A Aᶜ).card ≤ (G.interedges P Pᶜ).card)
    (helig : (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card)
    (hpar : NearCutParameters τ (Fintype.card V) P.card Pᶜ.card
      (cutBad G P Pᶜ (τ * Fintype.card V)).card) :
    NearCutTrigger G P Pᶜ (cutBad G P Pᶜ (τ * Fintype.card V)) ∨
      NearCutTrigger G Pᶜ P (cutBad G P Pᶜ (τ * Fintype.card V)) := by
  have hPQ : Disjoint P Pᶜ := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (mem_compl.mp hv') hv
  have hpartition : P ∪ Pᶜ = univ := by simp
  apply exists_trigger_of_internal_excess G hPQ hpartition
    (fun v hv => maximum_cut_local_left G hmax hv)
    (fun v hv => maximum_cut_local_right G hmax hv)
    ?_ ?_ ?_ ?_ hpar.three_bad_le (internal_excess_of_eligible G hPQ hpartition helig)
  · intro v hv hvt
    have hd := typical_of_not_cutBad_left G hv hvt
    have heq : ((Pᶜ.filter (G.Adj v)).card : ℝ) + crossDefect G Pᶜ v = Pᶜ.card := by
      exact_mod_cast cross_degree_add_defect G Pᶜ v
    have hmargin := hpar.symm.typical_cross_degree
    linarith
  · intro v hv hvt
    have hd := typical_of_not_cutBad_right G hv hvt
    have heq : ((P.filter (G.Adj v)).card : ℝ) + crossDefect G P v = P.card := by
      exact_mod_cast cross_degree_add_defect G P v
    have hmargin := hpar.typical_cross_degree
    linarith
  · intro v hv
    exact bad_of_mem_cutBad_left G hPQ (mem_inter.mp hv).1 (mem_inter.mp hv).2
  · intro v hv
    exact bad_of_mem_cutBad_right G hPQ (mem_inter.mp hv).1 (mem_inter.mp hv).2

end Erdos809.Source
