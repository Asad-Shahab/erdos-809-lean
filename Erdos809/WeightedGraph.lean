module
public import Erdos809.Compatibility
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Finite probability weights and weighted full-host graph quantities. -/

namespace Erdos809

open scoped BigOperators
open Finset

variable {V : Type*} [Fintype V]

/-- Nonnegative real probability weights; rational/uniform weights are special cases. -/
structure VertexWeights (V : Type*) [Fintype V] where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v
  total : ∑ v, weight v = 1

namespace VertexWeights

variable (x : VertexWeights V)

def mass (s : Finset V) : ℝ := ∑ v ∈ s, x.weight v

@[simp] theorem mass_univ : x.mass univ = 1 := x.total

theorem mass_nonneg (s : Finset V) : 0 ≤ x.mass s :=
  sum_nonneg fun v _ => x.nonneg v

theorem mass_mono {s t : Finset V} (h : s ⊆ t) : x.mass s ≤ x.mass t :=
  sum_le_sum_of_subset_of_nonneg h fun v _ _ => x.nonneg v

theorem mass_le_one (s : Finset V) : x.mass s ≤ 1 := by
  simpa using x.mass_mono (subset_univ s)

theorem mass_add_le_one {s t : Finset V} (h : Disjoint s t) :
    x.mass s + x.mass t ≤ 1 := by
  classical
  simpa only [mass, sum_union h] using x.mass_le_one (s ∪ t)

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (G.Adj v)

@[simp] theorem mem_neighbors (G : SimpleGraph V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

noncomputable def degree (G : SimpleGraph V) (v : V) : ℝ :=
  x.mass (neighbors G v)

noncomputable def edgeMass (G : SimpleGraph V) : ℝ :=
  (∑ v, x.weight v * x.degree G v) / 2

noncomputable def capacity (u v : V) : ℝ := x.weight u * x.weight v

theorem degree_nonneg (G : SimpleGraph V) (v : V) : 0 ≤ x.degree G v :=
  x.mass_nonneg _

theorem degree_le_one (G : SimpleGraph V) (v : V) : x.degree G v ≤ 1 :=
  x.mass_le_one _

theorem edgeMass_nonneg (G : SimpleGraph V) : 0 ≤ x.edgeMass G := by
  unfold edgeMass
  exact div_nonneg (sum_nonneg fun v _ => mul_nonneg (x.nonneg v)
    (x.degree_nonneg G v)) (by norm_num)

theorem edgeMass_le_half (G : SimpleGraph V) : x.edgeMass G ≤ 1 / 2 := by
  unfold edgeMass
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    ∑ v, x.weight v * x.degree G v ≤ ∑ v, x.weight v * 1 :=
      sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (x.degree_le_one G v) (x.nonneg v)
    _ = 1 := by simp [x.total]

/-- Weighted minimum degree is kept as a lower-bound predicate, avoiding an
arbitrary minimum convention on an empty vertex type. -/
def MinDegreeAtLeast (G : SimpleGraph V) (δ : ℝ) : Prop :=
  ∀ v, δ ≤ x.degree G v

theorem no_three_disjoint_neighborhoods (G : SimpleGraph V) {δ : ℝ}
    (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast G δ) (a b c : V)
    (hab : Disjoint (neighbors G a) (neighbors G b))
    (hac : Disjoint (neighbors G a) (neighbors G c))
    (hbc : Disjoint (neighbors G b) (neighbors G c)) : False := by
  classical
  have h := x.mass_add_le_one (disjoint_union_left.mpr ⟨hac, hbc⟩)
  rw [mass, sum_union hab] at h
  have ha := hmin a
  have hb := hmin b
  have hc := hmin c
  dsimp [degree, mass] at ha hb hc h
  linarith

/-- The load-bearing geometric union estimate. Its witness comes from an actual
compatible triangular mate in the same full host. -/
theorem compatible_triangular_union_bound [DecidableEq V] (G : SimpleGraph V) {δ : ℝ}
    (hmin : x.MinDegreeAtLeast G δ) {u v a b : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : Triangular G a b) :
    x.mass (neighbors G u ∪ neighbors G v) ≤ 1 - δ := by
  classical
  obtain ⟨z, hz⟩ := h.exists_outside_neighborhood G huv hab
  have hd : Disjoint (neighbors G u ∪ neighbors G v) (neighbors G z) := by
    apply disjoint_left.mpr
    intro t ht hzt
    obtain ⟨hu, hv⟩ := hz t ((mem_neighbors G z t).mp hzt)
    rcases mem_union.mp ht with hut | hvt
    · exact hu ((mem_neighbors G u t).mp hut)
    · exact hv ((mem_neighbors G v t).mp hvt)
  have hmass := x.mass_add_le_one hd
  have hdegree := hmin z
  change δ ≤ x.mass (neighbors G z) at hdegree
  linarith

theorem compatible_triangular_union_lt_two_thirds [DecidableEq V] (G : SimpleGraph V) {δ : ℝ}
    (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast G δ) {u v a b : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : Triangular G a b) :
    x.mass (neighbors G u ∪ neighbors G v) < 2 / 3 := by
  have := x.compatible_triangular_union_bound G hmin h huv hab
  linarith

end VertexWeights
end Erdos809
