module
public import Erdos809.WeightedGraph
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! Finite sampling space for the colored-kernel certificate. Marks are indexed
by pairs of sampled positions, even when positions receive equal host types.
The connection to a graph's nontriangular sector and matching marginals is a
separate obligation; this file only constructs and normalizes the sample law.
-/

namespace Erdos809.Certificate

/-- Four possible colors, with a probability distribution for each pair of
host types. Symmetry and graph support are supplied by the later graph model. -/
structure ColorKernel (V : Type*) where
  prob : V → V → Fin 4 → ℝ
  nonneg : ∀ u v c, 0 ≤ prob u v c
  total : ∀ u v, ∑ c, prob u v c = 1

/-- Unordered pairs of distinct sample positions, represented in increasing order. -/
abbrev PairPosition (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

variable {V : Type*} [Fintype V]

noncomputable def typeWeight (x : VertexWeights V) {n : ℕ} (v : Fin n → V) : ℝ :=
  ∏ i, x.weight (v i)

noncomputable def markWeight (κ : ColorKernel V) {n : ℕ} (v : Fin n → V)
    (c : PairPosition n → Fin 4) : ℝ :=
  ∏ e, κ.prob (v e.1.1) (v e.1.2) (c e)

noncomputable def sampleWeight (x : VertexWeights V) (κ : ColorKernel V)
    {n : ℕ} (v : Fin n → V) (c : PairPosition n → Fin 4) : ℝ :=
  typeWeight x v * markWeight κ v c

theorem typeWeight_nonnegative (x : VertexWeights V) {n : ℕ} (v : Fin n → V) :
    0 ≤ typeWeight x v := Finset.prod_nonneg fun i _ => x.nonneg (v i)

theorem markWeight_nonnegative (κ : ColorKernel V) {n : ℕ} (v : Fin n → V)
    (c : PairPosition n → Fin 4) : 0 ≤ markWeight κ v c :=
  Finset.prod_nonneg fun e _ => κ.nonneg _ _ _

theorem sampleWeight_nonnegative (x : VertexWeights V) (κ : ColorKernel V)
    {n : ℕ} (v : Fin n → V) (c : PairPosition n → Fin 4) :
    0 ≤ sampleWeight x κ v c :=
  mul_nonneg (typeWeight_nonnegative x v) (markWeight_nonnegative κ v c)

theorem typeWeight_total (x : VertexWeights V) (n : ℕ) :
    (∑ v : Fin n → V, typeWeight x v) = 1 := by
  unfold typeWeight
  rw [← Fintype.prod_sum]
  simp only [x.total, Finset.prod_const_one]

omit [Fintype V] in
theorem markWeight_total (κ : ColorKernel V) {n : ℕ} (v : Fin n → V) :
    (∑ c : PairPosition n → Fin 4, markWeight κ v c) = 1 := by
  unfold markWeight
  rw [← Fintype.prod_sum]
  simp only [κ.total, Finset.prod_const_one]

theorem sampleWeight_total (x : VertexWeights V) (κ : ColorKernel V) (n : ℕ) :
    (∑ v : Fin n → V, ∑ c : PairPosition n → Fin 4, sampleWeight x κ v c) = 1 := by
  simp only [sampleWeight, ← Finset.mul_sum, markWeight_total, mul_one, typeWeight_total]

end Erdos809.Certificate
