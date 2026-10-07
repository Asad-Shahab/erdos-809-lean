module
public import Erdos809.MatchingKernel
public import Erdos809.WeightedCuts
public import Erdos809.PaletteAlgebra

@[expose] public section

/-! The exact graph polynomial certified by the finite table. This module
defines its weighted graph terms and proves algebraic assembly implications;
it does not claim the certificate's sampling interpretation is complete. -/

namespace Erdos809

open Finset VertexWeights
open scoped BigOperators

variable {V : Type*} [Fintype V]

namespace VertexWeights

noncomputable def triangleResourceMass (x : VertexWeights V) (G : SimpleGraph V) : ℝ :=
  ∑ w, x.weight w * x.triangleRootMass G w * x.resourceObjective G w

theorem triangleResourceMass_le (x : VertexWeights V) (G : SimpleGraph V)
    {PF : ℝ} (hroot : ∀ w, x.resourceObjective G w ≤ PF) :
    x.triangleResourceMass G ≤ x.triangleMass G * PF :=
  weighted_root_bound x.weight (x.triangleRootMass G) (x.resourceObjective G) PF
    x.nonneg (x.triangleRootMass_nonneg G) hroot

end VertexWeights

namespace TriangularMatching

variable {E : Type*} [Fintype E] {G : SimpleGraph V} {x : VertexWeights V}
variable (y : TriangularMatching G x E)

noncomputable def polynomial : ℝ :=
  2 * x.triangleResourceMass G +
    (1 / 2 - x.edgeMass G - 2 * x.edgeMass (nontriangularSector G) - y.mass) *
      x.triangleMass G

/-- Cancellation after the exact polynomial has been established for this
same matching and the full-host resource roots. -/
theorem palette_bound_of_polynomial {P PF : ℝ}
    (hΔ : 0 < x.triangleMass G)
    (hroot : ∀ w, x.resourceObjective G w ≤ PF) (hpoly : 0 ≤ y.polynomial)
    (hdecomp : PF + x.edgeMass G - x.edgeMass (nontriangularSector G) - y.value ≤ P) :
    3 * x.edgeMass G / 2 - 1 / 4 ≤ P := by
  apply Erdos809.palette_bound_of_polynomial_le hΔ (x.triangleResourceMass_le G hroot)
    _ hdecomp
  simpa only [polynomial, y.mass_eq_twice_value] using hpoly

/-- The stable assembly retains the sole unproved certificate interpretation
as the explicit polynomial-error premise. -/
theorem stable_palette_bound_of_polynomial {P PF ξ ρ : ℝ}
    (hξ : 0 ≤ ξ) (hρ : 0 < ρ) (hsmall : ξ ≤ ρ / 2)
    (hdensity : 1 / 4 - ξ ≤ x.edgeMass G)
    (hdeficit : ρ ≤ x.edgeMass G - x.maxCut G)
    (hroot : ∀ w, x.resourceObjective G w ≤ PF) (hpoly : -ξ ≤ y.polynomial)
    (hdecomp : PF + x.edgeMass G - x.edgeMass (nontriangularSector G) - y.value ≤ P) :
    3 * x.edgeMass G / 2 - 1 / 4 - 2 * ξ / ρ ≤ P := by
  have hΔ := triangle_mass_of_cut_deficit (x.edgeMass_nonneg G) hξ hρ
    hdensity hdeficit (x.maxCut_lower G) hsmall
  apply Erdos809.stable_palette_bound_of_polynomial_le hξ hρ hΔ
    (x.triangleResourceMass_le G hroot) _ hdecomp
  simpa only [polynomial, y.mass_eq_twice_value] using hpoly

end TriangularMatching
end Erdos809
