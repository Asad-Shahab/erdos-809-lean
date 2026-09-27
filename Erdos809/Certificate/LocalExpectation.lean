import Erdos809.Certificate.LocalSupport
import Mathlib.Data.Fintype.Perm

/-! Expectations of local graph observables and exact position symmetrization.
The finite sums use the full vertex-and-mark law, including repeated types.
-/

namespace Erdos809.Certificate

variable {V : Type*} [Fintype V]

def LocalGraph.relabelEquiv (σ : Equiv.Perm (Fin 5)) : LocalGraph ≃ LocalGraph where
  toFun g := g.relabel σ
  invFun g := g.relabel σ⁻¹
  left_inv g := by simp [LocalGraph.relabel_mul]
  right_inv g := by simp [LocalGraph.relabel_mul]

noncomputable def localExpectation (x : VertexWeights V) (κ : ColorKernel V)
    (f : LocalGraph → ℝ) : ℝ :=
  ∑ v : Fin 5 → V, ∑ g : LocalGraph, sampleWeight x κ v g * f g

theorem localExpectation_add (x : VertexWeights V) (κ : ColorKernel V)
    (f h : LocalGraph → ℝ) :
    localExpectation x κ (fun g => f g + h g) =
      localExpectation x κ f + localExpectation x κ h := by
  simp only [localExpectation, mul_add, Finset.sum_add_distrib]

theorem localExpectation_sub (x : VertexWeights V) (κ : ColorKernel V)
    (f h : LocalGraph → ℝ) :
    localExpectation x κ (fun g => f g - h g) =
      localExpectation x κ f - localExpectation x κ h := by
  simp only [localExpectation, mul_sub, Finset.sum_sub_distrib]

theorem localExpectation_mul_const (x : VertexWeights V) (κ : ColorKernel V)
    (f : LocalGraph → ℝ) (a : ℝ) :
    localExpectation x κ (fun g => f g * a) = localExpectation x κ f * a := by
  simp only [localExpectation, ← mul_assoc, Finset.sum_mul]

theorem localExpectation_const_mul (x : VertexWeights V) (κ : ColorKernel V)
    (f : LocalGraph → ℝ) (a : ℝ) :
    localExpectation x κ (fun g => a * f g) = a * localExpectation x κ f := by
  simpa only [mul_comm] using localExpectation_mul_const x κ f a

theorem localExpectation_eq_density_sum (x : VertexWeights V) (κ : ColorKernel V)
    (f : LocalGraph → ℝ) :
    localExpectation x κ f = ∑ g, coloredDensity x κ g.color * f g := by
  unfold localExpectation coloredDensity
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_mul]
  simp only [LocalGraph.color_pair]

theorem localDensity_relabel (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (g : LocalGraph) (σ : Equiv.Perm (Fin 5)) :
    coloredDensity x κ (g.relabel σ).color = coloredDensity x κ g.color := by
  simpa only [LocalGraph.color_relabel] using
    coloredDensity_relabel x κ hκ σ g.color g.color_symm

theorem localExpectation_relabel (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (f : LocalGraph → ℝ) (σ : Equiv.Perm (Fin 5)) :
    localExpectation x κ (fun g => f (g.relabel σ)) = localExpectation x κ f := by
  rw [localExpectation_eq_density_sum, localExpectation_eq_density_sum]
  apply Fintype.sum_equiv (LocalGraph.relabelEquiv σ)
  intro g
  change coloredDensity x κ g.color * f (g.relabel σ) =
    coloredDensity x κ (g.relabel σ).color * f (g.relabel σ)
  rw [localDensity_relabel x κ hκ]

theorem localExpectation_symmetrized (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (f : LocalGraph → ℝ) :
    localExpectation x κ (fun g => ∑ σ : Equiv.Perm (Fin 5), f (g.relabel σ)) =
      120 * localExpectation x κ f := by
  calc
    _ = ∑ v : Fin 5 → V, ∑ σ : Equiv.Perm (Fin 5),
        ∑ g : LocalGraph, sampleWeight x κ v g * f (g.relabel σ) := by
      unfold localExpectation
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin 5), localExpectation x κ (fun g => f (g.relabel σ)) :=
      Finset.sum_comm
    _ = _ := by
      simp only [localExpectation_relabel x κ hκ]
      norm_num [Fintype.card_perm, Nat.factorial]

theorem localExpectation_nonnegative_on_support (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (f : LocalGraph → ℝ) (hf : ∀ g, g.Admissible → 0 ≤ f g) :
    0 ≤ localExpectation x κ f := by
  rw [localExpectation_eq_density_sum]
  apply Finset.sum_nonneg
  intro g _
  by_cases hg : g.Admissible
  · exact mul_nonneg (coloredDensity_nonnegative x κ _) (hf g hg)
  · rw [coloredDensity_zero_of_not_admissible x κ hκ hfree g hg]
    simp

/-- Exchangeability transfers a nonnegative orbit sum to the ordered
observable's expectation. No pointwise sign of the ordered observable is needed. -/
theorem localExpectation_nonnegative_of_symmetrized (x : VertexWeights V)
    (κ : ColorKernel V) (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (f : LocalGraph → ℝ)
    (hf : ∀ g : LocalGraph, g.Admissible →
      0 ≤ ∑ σ : Equiv.Perm (Fin 5), f (g.relabel σ)) :
    0 ≤ localExpectation x κ f := by
  have h := localExpectation_nonnegative_on_support x κ hκ hfree _ hf
  rw [localExpectation_symmetrized x κ hκ] at h
  linarith

/-- The finite coefficient checker may certify only the symmetrized deficit;
this is sufficient for the corresponding expected inequality. -/
theorem localExpectation_le_of_symmetrized (x : VertexWeights V)
    (κ : ColorKernel V) (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (f h : LocalGraph → ℝ)
    (hf : ∀ g : LocalGraph, g.Admissible →
      0 ≤ ∑ σ : Equiv.Perm (Fin 5), (h (g.relabel σ) - f (g.relabel σ))) :
    localExpectation x κ f ≤ localExpectation x κ h := by
  have hnonneg := localExpectation_nonnegative_of_symmetrized x κ hκ hfree
    (fun g => h g - f g) hf
  rw [localExpectation_sub] at hnonneg
  exact sub_nonneg.mp hnonneg

end Erdos809.Certificate
