import Erdos809.WeightedPolynomial
import Erdos809.Certificate.ProductMarginal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! The ordered five-position target and its expectation under the actual
matching's auxiliary sampling law. Vertex types may repeat. -/

noncomputable section
namespace Erdos809.Certificate

open Finset VertexWeights
open scoped BigOperators

variable {V : Type*} [Fintype V]

open Classical in
def adjIndicator (G : SimpleGraph V) (u v : V) : ℝ := if G.Adj u v then 1 else 0

open Classical in
def triangleIndicator (G : SimpleGraph V) (u v w : V) : ℝ :=
  if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w then 1 else 0

lemma sum_weight_adj (x : VertexWeights V) (G : SimpleGraph V) (u : V) :
    (∑ v, x.weight v * adjIndicator G u v) = x.degree G u := by
  classical
  rw [x.degree_eq_sum]
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v <;> simp [adjIndicator, h]

lemma sum_weighted_adj (x : VertexWeights V) (G : SimpleGraph V) :
    (∑ u, x.weight u * ∑ v, x.weight v * adjIndicator G u v) = 2 * x.edgeMass G := by
  simp only [sum_weight_adj, edgeMass]
  ring

lemma sum_weight_triangle (x : VertexWeights V) (G : SimpleGraph V) (u : V) :
    (∑ v, x.weight v * ∑ w, x.weight w * triangleIndicator G u v w) =
      2 * x.triangleRootMass G u := by
  classical
  unfold triangleRootMass
  rw [show (2 : ℝ) * (x.edgeSum G (fun v w =>
    if G.Adj u v ∧ G.Adj u w then 1 else 0) / 2) =
    x.edgeSum G (fun v w => if G.Adj u v ∧ G.Adj u w then 1 else 0) by ring]
  unfold edgeSum
  simp only [mul_sum]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  by_cases huv : G.Adj u v <;> by_cases huw : G.Adj u w <;>
    by_cases hvw : G.Adj v w <;> simp [triangleIndicator, huv, huw, hvw]

lemma sum_weight_resource (x : VertexWeights V) (G : SimpleGraph V) (u : V) :
    (∑ v, x.weight v * ∑ w, x.weight w *
      (adjIndicator (triangularSector G) u v * adjIndicator (nontriangularSector G) v w)) =
      x.resourceObjective G u := by
  classical
  unfold resourceObjective
  apply sum_congr rfl
  intro v _
  rw [show (∑ w, x.weight w * (adjIndicator (triangularSector G) u v *
      adjIndicator (nontriangularSector G) v w)) =
    adjIndicator (triangularSector G) u v *
      ∑ w, x.weight w * adjIndicator (nontriangularSector G) v w by
      simp only [mul_sum]; apply sum_congr rfl; intro w _; ring]
  rw [sum_weight_adj]
  change x.weight v * ((if Triangular G u v then 1 else 0) * _) = _
  ring

variable {E : Type*} [Fintype E] {G : SimpleGraph V} {x : VertexWeights V}
  (y : TriangularMatching G x E)

/-- Conditional expectation of the ordered target after the pair marks have
been summed out, for a specified five-tuple of host types. -/
def typeTarget (v : Fin 5 → V) : ℝ :=
  triangleIndicator G (v 0) (v 1) (v 2) *
    (4 * adjIndicator (triangularSector G) (v 0) (v 3) *
       adjIndicator (nontriangularSector G) (v 3) (v 4) + 1 -
      adjIndicator G (v 3) (v 4) -
      2 * adjIndicator (nontriangularSector G) (v 3) (v 4) -
      y.markProbability (v 3) (v 4))

lemma sum_typeWeight_succ (x : VertexWeights V) {n : ℕ} (f : (Fin (n + 1) → V) → ℝ) :
    (∑ v, typeWeight x v * f v) =
      ∑ a, x.weight a * ∑ v : Fin n → V, typeWeight x v * f (Fin.cons a v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => V)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, typeWeight, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, mul_assoc, ← mul_sum]
  rfl

lemma sum_typeWeight_zero (x : VertexWeights V) (f : (Fin 0 → V) → ℝ) :
    (∑ v, typeWeight x v * f v) = f Fin.elim0 := by
  simp [typeWeight, Finset.univ_unique, Subsingleton.elim (default : Fin 0 → V) Fin.elim0]

lemma target_tail_expectation
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u : V) :
    (∑ v, x.weight v * ∑ w, x.weight w *
      (4 * adjIndicator (triangularSector G) u v * adjIndicator (nontriangularSector G) v w +
        1 - adjIndicator G v w - 2 * adjIndicator (nontriangularSector G) v w -
        y.markProbability v w)) =
      4 * x.resourceObjective G u + 1 - 2 * x.edgeMass G -
        4 * x.edgeMass (nontriangularSector G) - 2 * y.mass := by
  classical
  have hr : (∑ v, x.weight v * ∑ w, x.weight w *
      (4 * adjIndicator (triangularSector G) u v * adjIndicator (nontriangularSector G) v w)) =
      4 * x.resourceObjective G u := by
    rw [← sum_weight_resource x G u]
    simp only [mul_sum]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro w _
    ring
  have hF : (∑ v, x.weight v * ∑ w, x.weight w *
      (2 * adjIndicator (nontriangularSector G) v w)) =
      4 * x.edgeMass (nontriangularSector G) := by
    calc
      _ = 2 * (∑ v, x.weight v * ∑ w, x.weight w * adjIndicator (nontriangularSector G) v w) := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro v _
        apply sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [sum_weighted_adj]; ring
  have hmark : (∑ v, x.weight v * ∑ w, x.weight w * y.markProbability v w) = 2 * y.mass := by
    simpa only [mul_sum, mul_assoc] using y.markProbability_ordered_total hinj
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_one, x.total]
  rw [hr, hF, hmark, sum_weighted_adj]

/-- The five independent vertex-type draws produce exactly four times the
weighted graph polynomial. No distinctness of the sampled types is imposed. -/
theorem sum_typeTarget
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) :
    (∑ v : Fin 5 → V, typeWeight x v * typeTarget y v) = 4 * y.polynomial := by
  simp only [sum_typeWeight_succ, sum_typeWeight_zero, typeTarget]
  simp only [Fin.cons_zero, Fin.cons_one]
  change (∑ u, x.weight u * ∑ v, x.weight v * ∑ w, x.weight w *
    ∑ d, x.weight d * ∑ e, x.weight e *
      (triangleIndicator G u v w * (4 * adjIndicator (triangularSector G) u d *
      adjIndicator (nontriangularSector G) d e + 1 - adjIndicator G d e -
      2 * adjIndicator (nontriangularSector G) d e - y.markProbability d e))) = _
  have heq (u v w : V) :
      (∑ d, x.weight d * ∑ e, x.weight e *
        (triangleIndicator G u v w *
          (4 * adjIndicator (triangularSector G) u d * adjIndicator (nontriangularSector G) d e +
            1 - adjIndicator G d e - 2 * adjIndicator (nontriangularSector G) d e -
            y.markProbability d e))) =
      triangleIndicator G u v w *
        (4 * x.resourceObjective G u + 1 - 2 * x.edgeMass G -
          4 * x.edgeMass (nontriangularSector G) - 2 * y.mass) := by
    rw [← target_tail_expectation y hinj u]
    simp only [mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    ring
  simp_rw [heq]
  have hroot (u : V) :
      (∑ v, x.weight v * ∑ w, x.weight w *
        (triangleIndicator G u v w *
          (4 * x.resourceObjective G u + 1 - 2 * x.edgeMass G -
            4 * x.edgeMass (nontriangularSector G) - 2 * y.mass))) =
      2 * x.triangleRootMass G u *
        (4 * x.resourceObjective G u + 1 - 2 * x.edgeMass G -
          4 * x.edgeMass (nontriangularSector G) - 2 * y.mass) := by
    rw [← sum_weight_triangle x G u]
    simp only [sum_mul, mul_sum]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro w _
    ring
  simp_rw [hroot]
  unfold TriangularMatching.polynomial triangleResourceMass triangleMass
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  ring

omit [Fintype V] in
/-- Moments of separate pair coordinates factor even when their sampled host
endpoints coincide. The injection concerns sample positions only. -/
theorem markWeight_product_moment {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (κ : ColorKernel V) (v : Fin n → V) (e : I ↪ PairPosition n)
    (f : I → Fin 4 → ℝ) :
    (∑ c, markWeight κ v c * ∏ i, f i (c (e i))) =
      ∏ i, ∑ a, κ.prob (v (e i).1.1) (v (e i).1.2) a * f i a := by
  classical
  rw [show (∑ c, markWeight κ v c * ∏ i, f i (c (e i))) =
      ∑ d : I → Fin 4, (∏ i, κ.prob (v (e i).1.1) (v (e i).1.2) (d i)) *
        ∏ i, f i (d i) from
    product_law_marginal (I := PairPosition n) (J := I) (V := Fin 4) (R := ℝ)
      (fun (p : PairPosition n) (a : Fin 4) => κ.prob (v p.1.1) (v p.1.2) a)
      (fun p => κ.total _ _) e (fun d => ∏ i, f i (d i))]
  simp only [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => κ.prob (v (e i).1.1) (v (e i).1.2) a * f i a)).symm

/-- The target's five relevant position pairs, in fixed order. -/
def targetPair : Fin 5 → PairPosition 5 :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩,
    ⟨(0, 3), by decide⟩, ⟨(3, 4), by decide⟩]

def targetPairEmbedding : Fin 5 ↪ PairPosition 5 :=
  ⟨targetPair, by decide⟩

def edgeFlag (c : Fin 4) : ℝ := if c = 0 then 0 else 1

def triangularFlag (c : Fin 4) : ℝ := if c = 2 ∨ c = 3 then 1 else 0

def nontriangularFlag (c : Fin 4) : ℝ := if c = 1 then 1 else 0

def selectedFlag (c : Fin 4) : ℝ := if c = 3 then 1 else 0

def coloredTriangle (c : PairPosition 5 → Fin 4) : ℝ :=
  edgeFlag (c (targetPair 0)) * edgeFlag (c (targetPair 1)) * edgeFlag (c (targetPair 2))

/-- Equation (5) of the campaign proof for the ordering 0,1,2,3,4. -/
def orderedTarget (c : PairPosition 5 → Fin 4) : ℝ :=
  4 * (coloredTriangle c * triangularFlag (c (targetPair 3)) * nontriangularFlag (c (targetPair 4))) +
    coloredTriangle c * 1 * 1 - coloredTriangle c * 1 * edgeFlag (c (targetPair 4)) -
    2 * (coloredTriangle c * 1 * nontriangularFlag (c (targetPair 4))) -
    coloredTriangle c * 1 * selectedFlag (c (targetPair 4))

def markExpectation {n : ℕ} (κ : ColorKernel V) (v : Fin n → V)
    (f : (PairPosition n → Fin 4) → ℝ) : ℝ := ∑ c, markWeight κ v c * f c

omit [Fintype V] in
lemma markExpectation_add {n : ℕ} (κ : ColorKernel V) (v : Fin n → V) (f g) :
    markExpectation κ v (fun c => f c + g c) = markExpectation κ v f + markExpectation κ v g := by
  simp only [markExpectation, mul_add, sum_add_distrib]

omit [Fintype V] in
lemma markExpectation_sub {n : ℕ} (κ : ColorKernel V) (v : Fin n → V) (f g) :
    markExpectation κ v (fun c => f c - g c) = markExpectation κ v f - markExpectation κ v g := by
  simp only [markExpectation, mul_sub, sum_sub_distrib]

omit [Fintype V] in
lemma markExpectation_smul {n : ℕ} (κ : ColorKernel V) (v : Fin n → V) (a : ℝ) (f) :
    markExpectation κ v (fun c => a * f c) = a * markExpectation κ v f := by
  simp only [markExpectation, mul_sum]
  apply sum_congr rfl
  intro c _
  ring

omit [Fintype V] in
lemma markWeight_triangle_tail_moment (κ : ColorKernel V) (v : Fin 5 → V) (f g : Fin 4 → ℝ) :
    markExpectation κ v (fun c => coloredTriangle c * f (c (targetPair 3)) * g (c (targetPair 4))) =
      (∑ a, κ.prob (v 0) (v 1) a * edgeFlag a) *
      (∑ a, κ.prob (v 0) (v 2) a * edgeFlag a) *
      (∑ a, κ.prob (v 1) (v 2) a * edgeFlag a) *
      (∑ a, κ.prob (v 0) (v 3) a * f a) *
      (∑ a, κ.prob (v 3) (v 4) a * g a) := by
  have h := markWeight_product_moment κ v targetPairEmbedding ![edgeFlag, edgeFlag, edgeFlag, f, g]
  simpa [markExpectation, targetPairEmbedding, targetPair, coloredTriangle, Fin.prod_univ_succ,
    mul_assoc] using h

lemma kernel_edge_moment
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    (∑ a, (y.colorKernel hinj).prob u v a * edgeFlag a) = adjIndicator G u v := by
  classical
  by_cases hg : G.Adj u v <;> by_cases hw : Walk2 G u v <;>
    simp [edgeFlag, Fin.sum_univ_four, TriangularMatching.colorKernel, markedHostKernel,
      markedProbability, nontriangularSector, hg, hw, adjIndicator]

lemma kernel_triangular_moment
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    (∑ a, (y.colorKernel hinj).prob u v a * triangularFlag a) =
      adjIndicator (triangularSector G) u v := by
  classical
  by_cases hg : G.Adj u v <;> by_cases hw : Walk2 G u v <;>
    simp [triangularFlag, Fin.sum_univ_four, TriangularMatching.colorKernel, markedHostKernel,
      markedProbability, nontriangularSector, triangularSector, Triangular, hg, hw, adjIndicator]

lemma kernel_nontriangular_moment
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    (∑ a, (y.colorKernel hinj).prob u v a * nontriangularFlag a) =
      adjIndicator (nontriangularSector G) u v := by
  classical
  by_cases hg : G.Adj u v <;> by_cases hw : Walk2 G u v <;>
    simp [nontriangularFlag, TriangularMatching.colorKernel, markedHostKernel,
      markedProbability, nontriangularSector, hg, hw, adjIndicator]

lemma kernel_selected_moment
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    (∑ a, (y.colorKernel hinj).prob u v a * selectedFlag a) = y.markProbability u v := by
  simp only [selectedFlag, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  exact y.colorKernel_selected hinj u v

omit [Fintype V] in
lemma triangleIndicator_eq_product (u v w : V) :
    triangleIndicator G u v w = adjIndicator G u v * adjIndicator G u w * adjIndicator G v w := by
  classical
  by_cases huv : G.Adj u v <;> by_cases huw : G.Adj u w <;> by_cases hvw : G.Adj v w <;>
    simp [triangleIndicator, adjIndicator, huv, huw, hvw]

/-- Summing the auxiliary independent pair marks gives the exact conditional
vertex-type target, including all four edge-color interpretations. -/
theorem markExpectation_orderedTarget
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (v : Fin 5 → V) :
    markExpectation (y.colorKernel hinj) v orderedTarget = typeTarget y v := by
  change markExpectation (y.colorKernel hinj) v (fun c =>
    4 * (coloredTriangle c * triangularFlag (c (targetPair 3)) * nontriangularFlag (c (targetPair 4))) +
      coloredTriangle c * 1 * 1 - coloredTriangle c * 1 * edgeFlag (c (targetPair 4)) -
      2 * (coloredTriangle c * 1 * nontriangularFlag (c (targetPair 4))) -
      coloredTriangle c * 1 * selectedFlag (c (targetPair 4))) = _
  rw [markExpectation_sub, markExpectation_sub, markExpectation_sub, markExpectation_add,
    markExpectation_smul, markExpectation_smul]
  rw [markWeight_triangle_tail_moment,
    markWeight_triangle_tail_moment (y.colorKernel hinj) v (fun _ => 1) (fun _ => 1),
    markWeight_triangle_tail_moment (y.colorKernel hinj) v (fun _ => 1) edgeFlag,
    markWeight_triangle_tail_moment (y.colorKernel hinj) v (fun _ => 1) nontriangularFlag,
    markWeight_triangle_tail_moment (y.colorKernel hinj) v (fun _ => 1) selectedFlag]
  simp only [kernel_edge_moment, kernel_triangular_moment, kernel_nontriangular_moment,
    kernel_selected_moment, mul_one, ColorKernel.total]
  rw [typeTarget, triangleIndicator_eq_product]
  ring

/-- Full finite sample expectation of the ordered target: four times the same
matching polynomial. This is an equality, independent of certificate positivity. -/
theorem sampleWeight_orderedTarget
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) :
    (∑ v : Fin 5 → V, ∑ c : PairPosition 5 → Fin 4,
      sampleWeight x (y.colorKernel hinj) v c * orderedTarget c) = 4 * y.polynomial := by
  simp only [sampleWeight, mul_assoc, ← mul_sum]
  change (∑ v : Fin 5 → V, typeWeight x v * markExpectation (y.colorKernel hinj) v orderedTarget) = _
  simp only [markExpectation_orderedTarget]
  exact sum_typeTarget y hinj

/-- The certificate normalization divides the ordered contribution by four. -/
theorem sampleWeight_normalizedTarget
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) :
    (∑ v : Fin 5 → V, ∑ c : PairPosition 5 → Fin 4,
      sampleWeight x (y.colorKernel hinj) v c * (orderedTarget c / 4)) = y.polynomial := by
  calc
    _ = (∑ v : Fin 5 → V, ∑ c : PairPosition 5 → Fin 4,
        sampleWeight x (y.colorKernel hinj) v c * orderedTarget c) / 4 := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    _ = _ := by rw [sampleWeight_orderedTarget y hinj]; ring

end Erdos809.Certificate
