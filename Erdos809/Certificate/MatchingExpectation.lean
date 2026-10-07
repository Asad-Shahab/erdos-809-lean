module
public import Erdos809.Certificate.LocalExpectation
public import Erdos809.Certificate.TargetExpectation

@[expose] public section

/-! The actual matching law applied to a symmetrized finite certificate.
The local inequality and the expected right-hand-side bound remain explicit
premises here; neither is asserted without a checked proof. -/

namespace Erdos809.Certificate

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)
variable (hinj : Function.Injective (fun i => s(y.left i, y.right i)))

theorem matching_kernel_forbidden_triangle (u v w : V) (c d : Fin 4)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (y.colorKernel hinj).prob u v 1 * (y.colorKernel hinj).prob u w c *
      (y.colorKernel hinj).prob v w d = 0 :=
  forbidden_F_triangle_weight_zero G (nontriangularSector G)
    y.markProbability (fun _ _ h => h.2) u v w c d hc hd

theorem matching_localExpectation_nonnegative_of_symmetrized
    (f : LocalGraph → ℝ)
    (hf : ∀ g : LocalGraph, g.Admissible →
      0 ≤ ∑ σ : Equiv.Perm (Fin 5), f (g.relabel σ)) :
    0 ≤ localExpectation x (y.colorKernel hinj) f :=
  localExpectation_nonnegative_of_symmetrized x (y.colorKernel hinj)
    (y.colorKernel_symmetric hinj) (matching_kernel_forbidden_triangle y hinj) f hf

theorem localExpectation_orderedTarget :
    localExpectation x (y.colorKernel hinj) orderedTarget = 4 * y.polynomial :=
  sampleWeight_orderedTarget y hinj

/-- Once the finite local deficit and actual expected right-hand side have
been checked, the exact target normalization gives the stable polynomial
bound. The same matching supplies every term and every sampling probability. -/
theorem polynomial_bound_of_symmetrized_certificate (scale ξ : ℝ)
    (hscale : 0 < scale) (rhs : LocalGraph → ℝ)
    (hlocal : ∀ g : LocalGraph, g.Admissible →
      0 ≤ ∑ σ : Equiv.Perm (Fin 5),
        (orderedTarget (g.relabel σ) * scale - rhs (g.relabel σ)))
    (hrhs : -(4 * scale * ξ) ≤ localExpectation x (y.colorKernel hinj) rhs) :
    -ξ ≤ y.polynomial := by
  have h := localExpectation_le_of_symmetrized x (y.colorKernel hinj)
    (y.colorKernel_symmetric hinj) (matching_kernel_forbidden_triangle y hinj)
    rhs (fun g => orderedTarget g * scale) hlocal
  rw [localExpectation_mul_const, localExpectation_orderedTarget y hinj] at h
  have hprod : 0 ≤ (4 * scale) * (y.polynomial + ξ) := by nlinarith
  have hpos : 0 < 4 * scale := mul_pos (by norm_num) hscale
  have hp := nonneg_of_mul_nonneg_right hprod hpos
  linarith

end Erdos809.Certificate
