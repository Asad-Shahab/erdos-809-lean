import Erdos809.WeightedCuts
import Erdos809.Edges
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Tactic.FieldSimp

/-!
# Uniform probability weights on finite graphs

Every vertex has weight 1/n. The formulas below identify the weighted graph
quantities exactly with ordinary edge, degree and cut counts divided by the
appropriate power of n. Nonemptiness is explicit.
-/

namespace Erdos809

open Finset SimpleGraph
open scoped BigOperators

variable (V : Type*) [Fintype V] [Nonempty V]

/-- Uniform probability weights on a nonempty finite vertex type. -/
noncomputable def uniformWeights : VertexWeights V where
  weight _ := 1 / (Fintype.card V : ℝ)
  nonneg _ := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [div_eq_mul_inv, hn]

variable {V}

@[simp] theorem uniform_weight (v : V) :
    (uniformWeights V).weight v = 1 / (Fintype.card V : ℝ) := rfl

theorem uniform_weight_pos (v : V) : 0 < (uniformWeights V).weight v :=
  div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

@[simp] theorem uniform_mass (S : Finset V) :
    (uniformWeights V).mass S = (S.card : ℝ) / Fintype.card V := by
  simp [VertexWeights.mass, uniformWeights, div_eq_mul_inv]

@[simp] theorem uniform_capacity (u v : V) :
    (uniformWeights V).capacity u v = 1 / (Fintype.card V : ℝ) ^ 2 := by
  unfold VertexWeights.capacity
  simp only [uniform_weight]
  ring

@[simp] theorem uniform_edgeCapacity (e : Sym2 V) :
    (uniformWeights V).edgeCapacity e = 1 / (Fintype.card V : ℝ) ^ 2 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [VertexWeights.edgeCapacity_mk, uniform_weight, uniform_weight]
    ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem uniform_degree (v : V) :
    (uniformWeights V).degree G v = (G.degree v : ℝ) / Fintype.card V := by
  classical
  have heq : VertexWeights.neighbors G v = G.neighborFinset v := by
    ext w
    simp
  rw [VertexWeights.degree, uniform_mass, heq, G.card_neighborFinset_eq_degree]

@[simp] theorem uniform_edgeMass :
    (uniformWeights V).edgeMass G = (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 := by
  rw [← (uniformWeights V).sum_edgeCapacity G]
  simp [div_eq_mul_inv]

theorem uniform_minDegree_iff (δ : ℝ) :
    (uniformWeights V).MinDegreeAtLeast G δ ↔
      ∀ v, δ * (Fintype.card V : ℝ) ≤ G.degree v := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  simp only [VertexWeights.MinDegreeAtLeast, uniform_degree, le_div_iff₀ hn]

theorem uniform_superquarter_iff :
    1 / 4 < (uniformWeights V).edgeMass G ↔
      (Fintype.card V : ℝ) ^ 2 / 4 < G.edgeFinset.card := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) 2
  rw [uniform_edgeMass, lt_div_iff₀ hn]
  ring_nf

variable [DecidableEq V]

@[simp] theorem uniform_cutWeight (A : Finset V) :
    (uniformWeights V).cutWeight G A =
      (G.interedges A Aᶜ).card / (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hset : G.interedges A Aᶜ =
      univ.filter (fun p : V × V ↦ G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∉ A) := by
    ext p
    simp [SimpleGraph.mem_interedges_iff, and_assoc, and_comm]
  calc
    (uniformWeights V).cutWeight G A =
        ∑ _p ∈ G.interedges A Aᶜ, 1 / (Fintype.card V : ℝ) ^ 2 := by
      rw [hset, sum_filter, Fintype.sum_prod_type]
      unfold VertexWeights.cutWeight VertexWeights.edgeSum
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases huv : G.Adj u v <;> by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;>
        simp [huv, hu, hv, pow_two]
    _ = _ := by simp [div_eq_mul_inv]

theorem uniform_cut_deficit (A : Finset V) :
    (uniformWeights V).edgeMass G - (uniformWeights V).cutWeight G A =
      ((G.edgeFinset.card : ℝ) - (G.interedges A Aᶜ).card) /
        (Fintype.card V : ℝ) ^ 2 := by
  rw [uniform_edgeMass, uniform_cutWeight, sub_div]

/-- Any ordinary maximum-cut witness normalizes to the weighted maximum cut. -/
theorem uniform_maxCut_eq_of_maximum_cut (A : Finset V)
    (hmax : ∀ B : Finset V, (G.interedges B Bᶜ).card ≤ (G.interedges A Aᶜ).card) :
    (uniformWeights V).maxCut G =
      (G.interedges A Aᶜ).card / (Fintype.card V : ℝ) ^ 2 := by
  classical
  apply le_antisymm
  · unfold VertexWeights.maxCut
    apply max'_le
    intro r hr
    obtain ⟨B, _, rfl⟩ := mem_image.mp hr
    rw [uniform_cutWeight]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hmax B)) (sq_nonneg _)
  · rw [← uniform_cutWeight G A]
    exact (uniformWeights V).cutWeight_le_maxCut G A

/-- A finite cut attains both the integer and normalized maximum. -/
theorem uniform_maxCut_attained :
    ∃ A : Finset V,
      (uniformWeights V).maxCut G =
        (G.interedges A Aᶜ).card / (Fintype.card V : ℝ) ^ 2 ∧
      ∀ B : Finset V, (G.interedges B Bᶜ).card ≤ (G.interedges A Aᶜ).card := by
  classical
  obtain ⟨A, _, hA⟩ := (univ : Finset (Finset V)).exists_max_image
    (fun B ↦ (G.interedges B Bᶜ).card) (by simp)
  have hmax : ∀ B : Finset V, (G.interedges B Bᶜ).card ≤ (G.interedges A Aᶜ).card :=
    fun B ↦ hA B (mem_univ _)
  exact ⟨A, uniform_maxCut_eq_of_maximum_cut G A hmax, hmax⟩

theorem uniform_maxCut_deficit (A : Finset V)
    (hmax : ∀ B : Finset V, (G.interedges B Bᶜ).card ≤ (G.interedges A Aᶜ).card) :
    (uniformWeights V).edgeMass G - (uniformWeights V).maxCut G =
      ((G.edgeFinset.card : ℝ) - (G.interedges A Aᶜ).card) /
        (Fintype.card V : ℝ) ^ 2 := by
  rw [uniform_edgeMass, uniform_maxCut_eq_of_maximum_cut G A hmax, sub_div]

end Erdos809
