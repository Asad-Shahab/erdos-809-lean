module
public import Erdos809.Certificate.LocalGraphs
public import Erdos809.Certificate.SamplingSymmetry
public import Erdos809.Certificate.Admissibility

@[expose] public section

/-! Support of the finite colored sampling law. Only admissible local graphs
can have nonzero weight when triangles containing an F edge are forbidden.
-/

namespace Erdos809.Certificate

variable {V : Type*} [Fintype V]

theorem markWeight_nonzero_probability (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (v : Fin 5 → V) (g : LocalGraph) (h : markWeight κ v g ≠ 0)
    (i j : Fin 5) (hne : i ≠ j) :
    κ.prob (v i) (v j) (g.color i j) ≠ 0 := by
  have he : ∀ e : PairPosition 5,
      κ.prob (v e.1.1) (v e.1.2) (g e) ≠ 0 := by
    exact fun e => (Finset.prod_ne_zero_iff.mp h) e (Finset.mem_univ e)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · simpa only [LocalGraph.color, hlt, ↓reduceDIte] using he ⟨(i, j), hlt⟩
  · rw [hκ, g.color_symm i j]
    simpa only [LocalGraph.color, hlt, ↓reduceDIte] using he ⟨(j, i), hlt⟩

theorem sampleWeight_nonzero_admissible (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (v : Fin 5 → V) (g : LocalGraph) (h : sampleWeight x κ v g ≠ 0) :
    g.Admissible := by
  have hm : markWeight κ v g ≠ 0 := by
    intro hz
    exact h (by simp [sampleWeight, hz])
  intro i j k hij
  by_contra hf
  push_neg at hf
  have hne : i ≠ j := by
    intro heq
    subst j
    simpa using hij
  have hik : i ≠ k := by
    intro heq
    subst k
    exact hf.1 (g.color_diagonal i)
  have hjk : j ≠ k := by
    intro heq
    subst k
    exact hf.2 (g.color_diagonal j)
  have h₁ := markWeight_nonzero_probability κ hκ v g hm i j hne
  have h₂ := markWeight_nonzero_probability κ hκ v g hm i k hik
  have h₃ := markWeight_nonzero_probability κ hκ v g hm j k hjk
  rw [hij] at h₁
  exact mul_ne_zero (mul_ne_zero h₁ h₂) h₃
    (hfree (v i) (v j) (v k) (g.color i k) (g.color j k) hf.1 hf.2)

theorem sampleWeight_zero_of_not_admissible (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (v : Fin 5 → V) (g : LocalGraph) (hg : ¬g.Admissible) :
    sampleWeight x κ v g = 0 := by
  by_contra h
  exact hg (sampleWeight_nonzero_admissible x κ hκ hfree v g h)

theorem coloredDensity_zero_of_not_admissible (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    (hfree : ∀ u v w (c d : Fin 4), c ≠ 0 → d ≠ 0 →
      κ.prob u v 1 * κ.prob u w c * κ.prob v w d = 0)
    (g : LocalGraph) (hg : ¬g.Admissible) :
    coloredDensity x κ g.color = 0 := by
  unfold coloredDensity
  have hcolor : (fun e : PairPosition 5 => g.color e.1.1 e.1.2) = g := by
    funext e
    exact g.color_pair e
  rw [hcolor]
  exact Finset.sum_eq_zero fun v _ =>
    sampleWeight_zero_of_not_admissible x κ hκ hfree v g hg

end Erdos809.Certificate
