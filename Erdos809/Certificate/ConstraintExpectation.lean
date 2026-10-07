module
public import Erdos809.Certificate.TargetExpectation
public import Erdos809.Certificate.ProductDisjoint

@[expose] public section

/-! Fresh-extension moments for the degree, matching-root, and selected-union
constraints. Arbitrary nonnegative events on the old sampled positions may
weight these identities. Their classifiers are not assumed canonical. -/

noncomputable section
namespace Erdos809.Certificate

open Finset VertexWeights
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
  {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)
  (hinj : Function.Injective (fun i => s(y.left i, y.right i)))

/-- One fresh type and its independently sampled root-edge color. -/
def degreeFreshMoment (w : V) : ℝ :=
  ∑ a, x.weight a * ∑ c, (y.colorKernel hinj).prob w a c * (edgeFlag c - 1 / 3)

theorem degreeFreshMoment_eq (w : V) :
    degreeFreshMoment y hinj w = x.degree G w - 1 / 3 := by
  unfold degreeFreshMoment
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, ColorKernel.total, one_mul,
    kernel_edge_moment]
  simp only [x.total, one_mul]
  rw [sum_weight_adj]

/-- Two fresh types with the selected-edge marginal from the same matching. -/
def rootFreshMoment (w : V) : ℝ :=
  ∑ a, x.weight a * ∑ b, x.weight b * y.markProbability a b *
    (1 - adjIndicator G w a - adjIndicator G w b)

include hinj in
theorem rootFreshMoment_eq (w : V) :
    rootFreshMoment y w = 2 * (y.mass - y.rootLoad w) := by
  classical
  have hsecond : (∑ a, x.weight a * ∑ b, x.weight b * y.markProbability a b *
      adjIndicator G w b) = y.rootLoad w := by
    calc
      _ = ∑ b, x.weight b * y.markedDegree b * adjIndicator G w b := by
        simp only [TriangularMatching.markedDegree, mul_sum, sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro b _
        apply sum_congr rfl
        intro a _
        ring
      _ = _ := y.markedDegree_rootLoad hinj w
  have hfirst : (∑ a, x.weight a * ∑ b, x.weight b * y.markProbability a b *
      adjIndicator G w a) = y.rootLoad w := by
    rw [← hsecond]
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [y.markProbability_symm b a]
    ring
  have htotal : (∑ a, x.weight a * ∑ b, x.weight b * y.markProbability a b) = 2 * y.mass := by
    simpa only [mul_sum, mul_assoc] using y.markProbability_ordered_total hinj
  unfold rootFreshMoment
  simp only [mul_sub, mul_one, sum_sub_distrib]
  rw [htotal, hfirst, hsecond]
  ring

include hinj in
/-- The selected-root column has the additional coefficient two. -/
theorem twice_rootFreshMoment_eq (w : V) :
    2 * rootFreshMoment y w = 4 * (y.mass - y.rootLoad w) := by
  rw [rootFreshMoment_eq y hinj]
  ring

/-- A root-edge union indicator uses inclusion-exclusion, even if the root
vertices have equal host types. -/
def unionIndicator (u v a : V) : ℝ :=
  adjIndicator G u a + adjIndicator G v a - adjIndicator G u a * adjIndicator G v a

lemma sum_weight_union [DecidableEq V] (u v : V) :
    (∑ a, x.weight a * unionIndicator (G := G) u v a) =
      x.mass (neighbors G u ∪ neighbors G v) := by
  classical
  have he (a : V) : x.weight a * unionIndicator (G := G) u v a =
      if a ∈ neighbors G u ∪ neighbors G v then x.weight a else 0 := by
    by_cases hu : G.Adj u a <;> by_cases hv : G.Adj v a <;>
      simp [unionIndicator, adjIndicator, mem_union, mem_neighbors, hu, hv]
  simp only [he, Finset.sum_ite_mem_eq, mass]

def unionFreshMoment (u v : V) : ℝ :=
  ∑ a, x.weight a * (2 / 3 - unionIndicator (G := G) u v a)

lemma unionFreshMoment_eq [DecidableEq V] (u v : V) :
    unionFreshMoment (x := x) (G := G) u v =
      2 / 3 - x.mass (neighbors G u ∪ neighbors G v) := by
  unfold unionFreshMoment
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, x.total, one_mul]
  rw [sum_weight_union]

/-- The union margin is needed only for a root pair that can actually be
selected. Zero mark probabilities impose no unsupported geometric bound. -/
theorem unionFreshMoment_nonneg_of_selected [DecidableEq V]
    {δ : ℝ} (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) {u v : V}
    (hpos : 0 < (y.colorKernel hinj).prob u v 3) :
    0 ≤ unionFreshMoment (x := x) (G := G) u v := by
  classical
  rw [unionFreshMoment_eq]
  exact y.selected_union_margin hinj hδ hmin hpos

/-- Positive full sample mass forces every sampled pair color to have positive
conditional probability. This includes samples with repeated vertex types. -/
theorem pairProbability_pos_of_sampleWeight_pos {n : ℕ} (κ : ColorKernel V)
    (v : Fin n → V) (c : PairPosition n → Fin 4) (e : PairPosition n)
    (h : 0 < sampleWeight x κ v c) : 0 < κ.prob (v e.1.1) (v e.1.2) (c e) := by
  have hmark : markWeight κ v c ≠ 0 := by
    intro hz
    simp only [sampleWeight, hz, mul_zero, lt_self_iff_false] at h
  have hne : κ.prob (v e.1.1) (v e.1.2) (c e) ≠ 0 := by
    intro hz
    apply hmark
    exact Finset.prod_eq_zero (mem_univ e) hz
  exact lt_of_le_of_ne (κ.nonneg _ _ _) hne.symm

/-- Finite averaging over the old positions and their marks. -/
def oldSampleAverage {n : ℕ} (κ : ColorKernel V)
    (f : (Fin n → V) → (PairPosition n → Fin 4) → ℝ) : ℝ :=
  ∑ v, ∑ c, sampleWeight x κ v c * f v c

lemma oldSampleAverage_nonneg {n : ℕ} (κ : ColorKernel V)
    (f : (Fin n → V) → (PairPosition n → Fin 4) → ℝ) (hf : ∀ v c, 0 ≤ f v c) :
    0 ≤ oldSampleAverage (x := x) κ f := by
  apply sum_nonneg
  intro v _
  apply sum_nonneg
  intro c _
  exact mul_nonneg (sampleWeight_nonnegative x κ v c) (hf v c)

/-- Any nonnegative event on the old sample can weight the fresh degree
constraint. The classifier for the old event is entirely arbitrary. -/
theorem degree_event_nonnegative {n : ℕ} (r : Fin n)
    (event : (Fin n → V) → (PairPosition n → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) {δ : ℝ}
    (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj)
      (fun v c => event v c * degreeFreshMoment y hinj (v r)) := by
  apply oldSampleAverage_nonneg
  intro v c
  apply mul_nonneg (hevent v c)
  rw [degreeFreshMoment_eq]
  exact sub_nonneg.mpr (hδ.trans (hmin (v r)))

/-- Any nonnegative old event can weight the root constraint for the very same
matching that generated the marks. -/
theorem root_event_nonnegative {n : ℕ} (r : Fin n)
    (event : (Fin n → V) → (PairPosition n → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj)
      (fun v c => event v c * (2 * rootFreshMoment y (v r))) := by
  apply oldSampleAverage_nonneg
  intro v c
  apply mul_nonneg (hevent v c)
  rw [twice_rootFreshMoment_eq y hinj]
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (y.rootLoad_le_mass (v r)))

/-- A selected old root pair carries the union constraint. Impossible selected
roots have zero sample mass, so this does not require a geometric bound there. -/
theorem union_event_nonnegative [DecidableEq V] {n : ℕ} (e : PairPosition n)
    (event : (Fin n → V) → (PairPosition n → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) {δ : ℝ}
    (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj)
      (fun v c => event v c * selectedFlag (c e) *
        unionFreshMoment (x := x) (G := G) (v e.1.1) (v e.1.2)) := by
  classical
  apply sum_nonneg
  intro v _
  apply sum_nonneg
  intro c _
  by_cases hs : c e = 3
  · by_cases hw : sampleWeight x (y.colorKernel hinj) v c = 0
    · simp only [hw, zero_mul, le_refl]
    · have hpos := lt_of_le_of_ne (sampleWeight_nonnegative x (y.colorKernel hinj) v c) (Ne.symm hw)
      have hp := pairProbability_pos_of_sampleWeight_pos (y.colorKernel hinj) v c e hpos
      rw [hs] at hp
      have hu := unionFreshMoment_nonneg_of_selected y hinj hδ hmin hp
      simp only [selectedFlag, hs, if_true, mul_one]
      exact mul_nonneg hpos.le (mul_nonneg (hevent v c) hu)
  · simp only [selectedFlag, hs, if_false, mul_zero, zero_mul, le_refl]

/-- Three distinct pairs of positions for a root and two fresh extensions. -/
def triplePair : Fin 3 → PairPosition 3 :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]

def triplePairEmbedding : Fin 3 ↪ PairPosition 3 := ⟨triplePair, by decide⟩

omit [Fintype V] in
lemma markWeight_threePair_moment (κ : ColorKernel V) (v : Fin 3 → V) (f g h : Fin 4 → ℝ) :
    markExpectation κ v (fun c => f (c (triplePair 0)) * g (c (triplePair 1)) * h (c (triplePair 2))) =
      (∑ a, κ.prob (v 0) (v 1) a * f a) * (∑ a, κ.prob (v 0) (v 2) a * g a) *
        (∑ a, κ.prob (v 1) (v 2) a * h a) := by
  have hm := markWeight_product_moment κ v triplePairEmbedding ![f, g, h]
  simpa [markExpectation, triplePairEmbedding, triplePair, Fin.prod_univ_succ, mul_assoc] using hm

/-- The selected fresh edge, minus its two old-root incidences. -/
def rootExtensionTarget (c : PairPosition 3 → Fin 4) : ℝ :=
  1 * 1 * selectedFlag (c (triplePair 2)) -
    edgeFlag (c (triplePair 0)) * 1 * selectedFlag (c (triplePair 2)) -
    1 * edgeFlag (c (triplePair 1)) * selectedFlag (c (triplePair 2))

theorem markExpectation_rootExtensionTarget (v : Fin 3 → V) :
    markExpectation (y.colorKernel hinj) v rootExtensionTarget =
      y.markProbability (v 1) (v 2) * (1 - adjIndicator G (v 0) (v 1) - adjIndicator G (v 0) (v 2)) := by
  change markExpectation (y.colorKernel hinj) v (fun c =>
    1 * 1 * selectedFlag (c (triplePair 2)) -
      edgeFlag (c (triplePair 0)) * 1 * selectedFlag (c (triplePair 2)) -
      1 * edgeFlag (c (triplePair 1)) * selectedFlag (c (triplePair 2))) = _
  rw [markExpectation_sub, markExpectation_sub,
    markWeight_threePair_moment (y.colorKernel hinj) v (fun _ => 1) (fun _ => 1) selectedFlag,
    markWeight_threePair_moment (y.colorKernel hinj) v edgeFlag (fun _ => 1) selectedFlag,
    markWeight_threePair_moment (y.colorKernel hinj) v (fun _ => 1) edgeFlag selectedFlag]
  simp only [mul_one, ColorKernel.total, kernel_edge_moment, kernel_selected_moment]
  ring

/-- Actual color sampling on the three fresh pairs realizes the root moment.
The old root is held fixed; the other two host types are independent draws. -/
theorem sampled_rootExtension_eq (w : V) :
    (∑ a, x.weight a * ∑ b, x.weight b *
      markExpectation (y.colorKernel hinj) ![w, a, b] rootExtensionTarget) =
      2 * (y.mass - y.rootLoad w) := by
  simp only [markExpectation_rootExtensionTarget, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simpa only [rootFreshMoment, mul_assoc] using rootFreshMoment_eq y hinj w

/-- Fresh marks from each root endpoint to one new position are independent.
Their inclusion-exclusion target gives the exact host neighborhood union. -/
theorem sampled_unionExtension_eq (u v a : V) :
    (∑ c : Fin 4, ∑ d : Fin 4,
      (y.colorKernel hinj).prob u a c * (y.colorKernel hinj).prob v a d *
        (2 / 3 - edgeFlag c - edgeFlag d + edgeFlag c * edgeFlag d)) =
      2 / 3 - unionIndicator (G := G) u v a := by
  have hfactor (f g : Fin 4 → ℝ) :
      (∑ c, ∑ d, (y.colorKernel hinj).prob u a c * (y.colorKernel hinj).prob v a d * (f c * g d)) =
      (∑ c, (y.colorKernel hinj).prob u a c * f c) *
        (∑ d, (y.colorKernel hinj).prob v a d * g d) := by
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    ring
  have hconst := hfactor (fun _ => (2 / 3 : ℝ)) (fun _ => 1)
  have hleft := hfactor edgeFlag (fun _ => 1)
  have hright := hfactor (fun _ => 1) edgeFlag
  have hboth := hfactor edgeFlag edgeFlag
  simp only [mul_one, ← sum_mul, ColorKernel.total, one_mul, kernel_edge_moment] at hconst hleft hright hboth
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  simp only [sum_mul] at hconst hleft
  rw [hconst, hleft, hright, hboth]
  unfold unionIndicator
  ring

/-- Averaging the new host type gives the full fresh union margin. -/
theorem sampled_unionFresh_eq [DecidableEq V] (u v : V) :
    (∑ a, x.weight a * ∑ c : Fin 4, ∑ d : Fin 4,
      (y.colorKernel hinj).prob u a c * (y.colorKernel hinj).prob v a d *
        (2 / 3 - edgeFlag c - edgeFlag d + edgeFlag c * edgeFlag d)) =
      2 / 3 - x.mass (neighbors G u ∪ neighbors G v) := by
  simp only [sampled_unionExtension_eq]
  exact unionFreshMoment_eq u v

/-- A strictly increasing map of positions induces an injection of pair
coordinates, without identifying pairs that share a host type. -/
def positionPairEmbedding {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) :
    PairPosition m ↪ PairPosition n where
  toFun p := ⟨(f p.1.1, f p.1.2), hf p.2⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (hf.injective (congrArg (fun e => e.1.1) h))
      (hf.injective (congrArg (fun e => e.1.2) h))

def initialPairEmbedding {m n : ℕ} (h : m ≤ n) : PairPosition m ↪ PairPosition n :=
  positionPairEmbedding (Fin.castLE h) (fun _ _ hij => hij)

def initialTypes {m n : ℕ} (h : m ≤ n) (v : Fin n → V) : Fin m → V :=
  fun i => v (Fin.castLE h i)

def rootFreshPositions : Fin 3 → Fin 5 := ![0, 3, 4]

def rootFreshPairs : PairPosition 3 ↪ PairPosition 5 :=
  positionPairEmbedding rootFreshPositions (by decide)

def rootFreshTypes (v : Fin 5 → V) : Fin 3 → V := fun i => v (rootFreshPositions i)

lemma rootPairFamilies_disjoint : ∀ p q,
    initialPairEmbedding (by decide : 3 ≤ 5) p ≠ rootFreshPairs q := by decide

omit [Fintype V] in
/-- Conditional independence of the old marks and all three fresh root marks.
The old event may be an arbitrary function of its complete old color pattern. -/
theorem markExpectation_root_factor (κ : ColorKernel V) (v : Fin 5 → V)
    (event : (PairPosition 3 → Fin 4) → ℝ) :
    markExpectation κ v (fun c =>
      event (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
        rootExtensionTarget (fun p => c (rootFreshPairs p))) =
      markExpectation κ (initialTypes (by decide : 3 ≤ 5) v) event *
        markExpectation κ (rootFreshTypes v) rootExtensionTarget := by
  have h := product_law_disjoint (I := PairPosition 5) (J := PairPosition 3)
    (K := PairPosition 3) (V := Fin 4) (R := ℝ)
    (fun p a => κ.prob (v p.1.1) (v p.1.2) a) (fun p => κ.total _ _)
    (initialPairEmbedding (by decide : 3 ≤ 5)) rootFreshPairs
    rootPairFamilies_disjoint event rootExtensionTarget
  simp only [markExpectation, markWeight, mul_assoc] at h ⊢
  exact h

lemma oldSampleAverage_type_sum {n : ℕ} (κ : ColorKernel V)
    (f : (Fin n → V) → (PairPosition n → Fin 4) → ℝ) :
    oldSampleAverage (x := x) κ f =
      ∑ v, typeWeight x v * markExpectation κ v (f v) := by
  simp only [oldSampleAverage, sampleWeight, markExpectation, mul_assoc, mul_sum]

private lemma cons_as_vec {A : Type*} {n : ℕ} (a : A) (v : Fin n → A) :
    Fin.cons a v = Matrix.vecCons a v := rfl

private lemma elim0_as_vec {A : Type*} : (Fin.elim0 : Fin 0 → A) = ![] := rfl

omit [Fintype V] in
private lemma initial_three_vec (a b c d e : V) :
    initialTypes (by decide : 3 ≤ 5) ![a,b,c,d,e] = ![a,b,c] := by
  funext i
  fin_cases i <;> rfl

omit [Fintype V] in
private lemma rootFresh_vec (a b c d e : V) :
    rootFreshTypes ![a,b,c,d,e] = ![a,d,e] := by
  funext i
  fin_cases i <;> rfl

/-- Actual five-position root column before its coefficient two. The old
three-position classifier remains arbitrary; the marks connecting the old root
to the two fresh positions are independent of every old flag mark. -/
theorem root_column_expectation
    (event : (Fin 3 → V) → (PairPosition 3 → Fin 4) → ℝ) :
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 3 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
      rootExtensionTarget (fun p => c (rootFreshPairs p))) =
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 3 → V) c =>
      event v c * rootFreshMoment y (v 0)) := by
  rw [oldSampleAverage_type_sum]
  simp only [markExpectation_root_factor]
  rw [oldSampleAverage_type_sum]
  have hmul (v : Fin 3 → V) :
      markExpectation (y.colorKernel hinj) v (fun c => event v c * rootFreshMoment y (v 0)) =
      markExpectation (y.colorKernel hinj) v (event v) * rootFreshMoment y (v 0) := by
    simp only [markExpectation, sum_mul, mul_assoc]
  simp only [hmul, sum_typeWeight_succ, sum_typeWeight_zero, cons_as_vec, elim0_as_vec,
    initial_three_vec, rootFresh_vec, Matrix.cons_val_zero]
  change (∑ a, x.weight a * ∑ b, x.weight b * ∑ d, x.weight d *
      ∑ e, x.weight e * ∑ f, x.weight f *
        (markExpectation (y.colorKernel hinj) ![a,b,d] (event ![a,b,d]) *
          markExpectation (y.colorKernel hinj) ![a,e,f] rootExtensionTarget)) =
    ∑ a, x.weight a * ∑ b, x.weight b * ∑ d, x.weight d *
      (markExpectation (y.colorKernel hinj) ![a,b,d] (event ![a,b,d]) * rootFreshMoment y a)
  apply sum_congr rfl
  intro a _
  congr 1
  apply sum_congr rfl
  intro b _
  congr 1
  apply sum_congr rfl
  intro d _
  congr 1
  rw [rootFreshMoment_eq y hinj, ← sampled_rootExtension_eq y hinj a]
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  ring

/-- Nonnegativity of the actual five-position root column for every nonnegative
old flag event. Scaling this statement by two gives the stored root-column law. -/
theorem root_column_nonnegative
    (event : (Fin 3 → V) → (PairPosition 3 → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 3 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
      rootExtensionTarget (fun p => c (rootFreshPairs p))) := by
  rw [root_column_expectation]
  apply oldSampleAverage_nonneg
  intro v c
  apply mul_nonneg (hevent v c)
  rw [rootFreshMoment_eq y hinj]
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (y.rootLoad_le_mass (v 0)))

private lemma sum_fin_fun_succ {A : Type*} [Fintype A] {n : ℕ}
    (f : (Fin (n + 1) → A) → ℝ) :
    (∑ v, f v) = ∑ a, ∑ v : Fin n → A, f (Fin.cons a v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).sum_comp, Fintype.sum_prod_type]
  rfl

private lemma sum_fin_fun_zero {A : Type*} [Fintype A] (f : (Fin 0 → A) → ℝ) :
    (∑ v, f v) = f Fin.elim0 := by
  simp [Finset.univ_unique, Subsingleton.elim (default : Fin 0 → A) Fin.elim0]

def degreeFreshPair : Fin 1 ↪ PairPosition 5 :=
  ⟨fun _ => ⟨(0,4), by decide⟩, by decide⟩

lemma degreePairFamilies_disjoint : ∀ p q,
    initialPairEmbedding (by decide : 4 ≤ 5) p ≠ degreeFreshPair q := by decide

omit [Fintype V] in
lemma markExpectation_degree_factor (κ : ColorKernel V) (v : Fin 5 → V)
    (event : (PairPosition 4 → Fin 4) → ℝ) :
    markExpectation κ v (fun c =>
      event (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
        (edgeFlag (c (degreeFreshPair 0)) - 1 / 3)) =
      markExpectation κ (initialTypes (by decide : 4 ≤ 5) v) event *
        (∑ a, κ.prob (v 0) (v 4) a * (edgeFlag a - 1 / 3)) := by
  have h := product_law_disjoint (I := PairPosition 5) (J := PairPosition 4)
    (K := Fin 1) (V := Fin 4) (R := ℝ)
    (fun p a => κ.prob (v p.1.1) (v p.1.2) a) (fun p => κ.total _ _)
    (initialPairEmbedding (by decide : 4 ≤ 5)) degreeFreshPair
    degreePairFamilies_disjoint event (fun d => edgeFlag (d 0) - 1 / 3)
  have hm : (∑ d : Fin 1 → Fin 4,
      (∏ i, κ.prob (v (degreeFreshPair i).1.1) (v (degreeFreshPair i).1.2) (d i)) *
        (edgeFlag (d 0) - 1 / 3)) =
      ∑ a, κ.prob (v 0) (v 4) a * (edgeFlag a - 1 / 3) := by
    simp only [sum_fin_fun_succ, sum_fin_fun_zero, Fin.prod_univ_one, degreeFreshPair,
      Function.Embedding.coeFn_mk, Fin.cons_zero]
  rw [hm] at h
  simp only [markExpectation, markWeight, mul_assoc] at h ⊢
  exact h

omit [Fintype V] in
private lemma initial_four_vec (a b c d e : V) :
    initialTypes (by decide : 4 ≤ 5) ![a,b,c,d,e] = ![a,b,c,d] := by
  funext i
  fin_cases i <;> rfl

/-- Actual five-position degree column: an arbitrary old four-position event
multiplies the centered fresh root-edge indicator. -/
theorem degree_column_expectation
    (event : (Fin 4 → V) → (PairPosition 4 → Fin 4) → ℝ) :
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 4 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
      (edgeFlag (c (degreeFreshPair 0)) - 1 / 3)) =
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 4 → V) c =>
      event v c * degreeFreshMoment y hinj (v 0)) := by
  rw [oldSampleAverage_type_sum]
  simp only [markExpectation_degree_factor]
  rw [oldSampleAverage_type_sum]
  have hmul (v : Fin 4 → V) :
      markExpectation (y.colorKernel hinj) v (fun c => event v c * degreeFreshMoment y hinj (v 0)) =
      markExpectation (y.colorKernel hinj) v (event v) * degreeFreshMoment y hinj (v 0) := by
    simp only [markExpectation, sum_mul, mul_assoc]
  simp only [hmul, sum_typeWeight_succ, sum_typeWeight_zero, cons_as_vec, elim0_as_vec,
    initial_four_vec, Matrix.cons_val_zero, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  apply sum_congr rfl
  intro a _
  congr 1
  apply sum_congr rfl
  intro b _
  congr 1
  apply sum_congr rfl
  intro c _
  congr 1
  apply sum_congr rfl
  intro d _
  congr 1
  unfold degreeFreshMoment
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro q _
  ring

theorem degree_column_nonnegative
    (event : (Fin 4 → V) → (PairPosition 4 → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) {δ : ℝ}
    (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 4 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
      (edgeFlag (c (degreeFreshPair 0)) - 1 / 3)) := by
  rw [degree_column_expectation]
  exact degree_event_nonnegative y hinj 0 event hevent hδ hmin

/-- Old selected root pair and the two fresh root-to-extension pairs. -/
def unionOldPair : PairPosition 4 := ⟨(0,1), by decide⟩

def unionFreshPairs : Fin 2 ↪ PairPosition 5 :=
  ⟨![⟨(0,4), by decide⟩, ⟨(1,4), by decide⟩], by decide⟩

lemma unionPairFamilies_disjoint : ∀ p q,
    initialPairEmbedding (by decide : 4 ≤ 5) p ≠ unionFreshPairs q := by decide

def unionExtensionTarget (d : Fin 2 → Fin 4) : ℝ :=
  2 / 3 - edgeFlag (d 0) - edgeFlag (d 1) + edgeFlag (d 0) * edgeFlag (d 1)

lemma markExpectation_union_factor (v : Fin 5 → V)
    (event : (PairPosition 4 → Fin 4) → ℝ) :
    markExpectation (y.colorKernel hinj) v (fun c =>
      event (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
        selectedFlag (c (initialPairEmbedding (by decide : 4 ≤ 5) unionOldPair)) *
        unionExtensionTarget (fun i => c (unionFreshPairs i))) =
      markExpectation (y.colorKernel hinj) (initialTypes (by decide : 4 ≤ 5) v)
        (fun c => event c * selectedFlag (c unionOldPair)) *
        (2 / 3 - unionIndicator (G := G) (v 0) (v 1) (v 4)) := by
  let κ := y.colorKernel hinj
  have h := product_law_disjoint (I := PairPosition 5) (J := PairPosition 4)
    (K := Fin 2) (V := Fin 4) (R := ℝ)
    (fun p a => κ.prob (v p.1.1) (v p.1.2) a) (fun p => κ.total _ _)
    (initialPairEmbedding (by decide : 4 ≤ 5)) unionFreshPairs
    unionPairFamilies_disjoint (fun c => event c * selectedFlag (c unionOldPair)) unionExtensionTarget
  have hm : (∑ d : Fin 2 → Fin 4,
      (∏ i, κ.prob (v (unionFreshPairs i).1.1) (v (unionFreshPairs i).1.2) (d i)) *
        unionExtensionTarget d) = 2 / 3 - unionIndicator (G := G) (v 0) (v 1) (v 4) := by
    simp only [sum_fin_fun_succ, sum_fin_fun_zero, Fin.prod_univ_two, unionFreshPairs,
      Function.Embedding.coeFn_mk, unionExtensionTarget, Fin.cons_zero, Fin.cons_one,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact sampled_unionExtension_eq y hinj (v 0) (v 1) (v 4)
  rw [hm] at h
  simp only [markExpectation, markWeight, mul_assoc] at h ⊢
  exact h

/-- Actual five-position selected-union column, with its arbitrary old event
and the selected old root-edge indicator retained inside the old sample law. -/
theorem union_column_expectation
    (event : (Fin 4 → V) → (PairPosition 4 → Fin 4) → ℝ) :
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 4 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
      selectedFlag (c (initialPairEmbedding (by decide : 4 ≤ 5) unionOldPair)) *
      unionExtensionTarget (fun i => c (unionFreshPairs i))) =
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 4 → V) c =>
      event v c * selectedFlag (c unionOldPair) *
        unionFreshMoment (x := x) (G := G) (v 0) (v 1)) := by
  rw [oldSampleAverage_type_sum]
  simp only [markExpectation_union_factor]
  rw [oldSampleAverage_type_sum]
  have hmul (v : Fin 4 → V) :
      markExpectation (y.colorKernel hinj) v (fun c => event v c * selectedFlag (c unionOldPair) *
          unionFreshMoment (x := x) (G := G) (v 0) (v 1)) =
      markExpectation (y.colorKernel hinj) v (fun c => event v c * selectedFlag (c unionOldPair)) *
        unionFreshMoment (x := x) (G := G) (v 0) (v 1) := by
    simp only [markExpectation, sum_mul, mul_assoc]
  simp only [hmul, sum_typeWeight_succ, sum_typeWeight_zero, cons_as_vec, elim0_as_vec,
    initial_four_vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  apply sum_congr rfl
  intro a _
  congr 1
  apply sum_congr rfl
  intro b _
  congr 1
  apply sum_congr rfl
  intro c _
  congr 1
  apply sum_congr rfl
  intro d _
  congr 1
  unfold unionFreshMoment
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  ring

theorem union_column_nonnegative [DecidableEq V]
    (event : (Fin 4 → V) → (PairPosition 4 → Fin 4) → ℝ)
    (hevent : ∀ v c, 0 ≤ event v c) {δ : ℝ}
    (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 4 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
      selectedFlag (c (initialPairEmbedding (by decide : 4 ≤ 5) unionOldPair)) *
      unionExtensionTarget (fun i => c (unionFreshPairs i))) := by
  rw [union_column_expectation]
  exact union_event_nonnegative y hinj unionOldPair event hevent hδ hmin

def densityFreshPair : Fin 1 ↪ PairPosition 5 :=
  ⟨fun _ => ⟨(3,4), by decide⟩, by decide⟩

lemma densityPairFamilies_disjoint : ∀ p q,
    initialPairEmbedding (by decide : 3 ≤ 5) p ≠ densityFreshPair q := by decide

lemma markExpectation_density_factor (v : Fin 5 → V)
    (event : (PairPosition 3 → Fin 4) → ℝ) :
    markExpectation (y.colorKernel hinj) v (fun c =>
      event (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
        (2 * edgeFlag (c (densityFreshPair 0)) - 1)) =
      markExpectation (y.colorKernel hinj) (initialTypes (by decide : 3 ≤ 5) v) event *
        (2 * adjIndicator G (v 3) (v 4) - 1) := by
  let κ := y.colorKernel hinj
  have h := product_law_disjoint (I := PairPosition 5) (J := PairPosition 3)
    (K := Fin 1) (V := Fin 4) (R := ℝ)
    (fun p a => κ.prob (v p.1.1) (v p.1.2) a) (fun p => κ.total _ _)
    (initialPairEmbedding (by decide : 3 ≤ 5)) densityFreshPair
    densityPairFamilies_disjoint event (fun d => 2 * edgeFlag (d 0) - 1)
  have hm : (∑ d : Fin 1 → Fin 4,
      (∏ i, κ.prob (v (densityFreshPair i).1.1) (v (densityFreshPair i).1.2) (d i)) *
        (2 * edgeFlag (d 0) - 1)) = 2 * adjIndicator G (v 3) (v 4) - 1 := by
    simp only [sum_fin_fun_succ, sum_fin_fun_zero, Fin.prod_univ_one, densityFreshPair,
      Function.Embedding.coeFn_mk, Fin.cons_zero]
    have he := kernel_edge_moment y hinj (v 3) (v 4)
    simp only [mul_sub, sum_sub_distrib, mul_one, κ.total]
    rw [show (∑ a, κ.prob (v 3) (v 4) a * (2 * edgeFlag a)) =
        2 * ∑ a, κ.prob (v 3) (v 4) a * edgeFlag a by
      rw [mul_sum]; apply sum_congr rfl; intro a _; ring]
    rw [he]
  rw [hm] at h
  simp only [markExpectation, markWeight, mul_assoc] at h ⊢
  exact h

lemma densityFreshMoment_eq :
    (∑ a, x.weight a * ∑ b, x.weight b * (2 * adjIndicator G a b - 1)) =
      4 * x.edgeMass G - 1 := by
  have h := sum_weighted_adj x G
  have hd : (∑ a, x.weight a * ∑ b, x.weight b * (2 * adjIndicator G a b)) =
      2 * (∑ a, x.weight a * ∑ b, x.weight b * adjIndicator G a b) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  simp only [mul_sub, sum_sub_distrib, mul_one, x.total]
  rw [hd, h]
  ring

/-- Actual density column. The fresh edge lies entirely outside the old flag,
so its mean factors from the arbitrary old three-position event. -/
theorem density_column_expectation
    (event : (Fin 3 → V) → (PairPosition 3 → Fin 4) → ℝ) :
    oldSampleAverage (x := x) (y.colorKernel hinj) (fun (v : Fin 5 → V) c =>
      event (initialTypes (by decide : 3 ≤ 5) v)
        (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
      (2 * edgeFlag (c (densityFreshPair 0)) - 1)) =
    oldSampleAverage (x := x) (y.colorKernel hinj) event * (4 * x.edgeMass G - 1) := by
  rw [oldSampleAverage_type_sum]
  simp only [markExpectation_density_factor]
  rw [oldSampleAverage_type_sum]
  simp only [sum_typeWeight_succ, sum_typeWeight_zero, cons_as_vec, elim0_as_vec,
    initial_three_vec, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hroot (a b c : V) :
      (∑ d, x.weight d * ∑ e, x.weight e *
        (markExpectation (y.colorKernel hinj) ![a,b,c] (event ![a,b,c]) *
          (2 * adjIndicator G d e - 1))) =
      markExpectation (y.colorKernel hinj) ![a,b,c] (event ![a,b,c]) * (4 * x.edgeMass G - 1) := by
    rw [← densityFreshMoment_eq (x := x) (G := G)]
    simp only [mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    ring
  simp only [hroot, sum_mul, mul_assoc]

lemma oldSampleAverage_const {n : ℕ} (κ : ColorKernel V) (a : ℝ) :
    oldSampleAverage (x := x) κ (fun (_ : Fin n → V) _ => a) = a := by
  simp only [oldSampleAverage, ← sum_mul, sampleWeight_total, one_mul]

lemma oldSampleAverage_le_const {n : ℕ} (κ : ColorKernel V)
    (event : (Fin n → V) → (PairPosition n → Fin 4) → ℝ) {A : ℝ}
    (hevent : ∀ v c, event v c ≤ A) : oldSampleAverage (x := x) κ event ≤ A := by
  rw [← oldSampleAverage_const (x := x) (n := n) κ A]
  apply sum_le_sum
  intro v _
  apply sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_left (hevent v c) (sampleWeight_nonnegative x κ v c)

/-- The complete density loss is at most four times the event upper bound
and the sub-quarter error. No sum of all density multipliers is paid. -/
theorem density_column_lower_bound
    (event : (Fin 3 → V) → (PairPosition 3 → Fin 4) → ℝ) {A ξ : ℝ}
    (hevent : ∀ v c, 0 ≤ event v c) (hupper : ∀ v c, event v c ≤ A)
    (hξ : 0 ≤ ξ) (hdensity : 1 / 4 - ξ ≤ x.edgeMass G) :
    -(4 * A * ξ) ≤ oldSampleAverage (x := x) (y.colorKernel hinj)
      (fun (v : Fin 5 → V) c =>
        event (initialTypes (by decide : 3 ≤ 5) v)
          (fun p => c (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
        (2 * edgeFlag (c (densityFreshPair 0)) - 1)) := by
  rw [density_column_expectation]
  have hnonneg := oldSampleAverage_nonneg (x := x) (y.colorKernel hinj) event hevent
  have hle := oldSampleAverage_le_const (x := x) (y.colorKernel hinj) event hupper
  have hm : -(4 * ξ) ≤ 4 * x.edgeMass G - 1 := by linarith only [hdensity]
  have hmul := mul_le_mul_of_nonneg_left hm hnonneg
  have hscale := mul_le_mul_of_nonneg_right hle (show 0 ≤ 4 * ξ by positivity)
  nlinarith only [hmul, hscale]

end Erdos809.Certificate
