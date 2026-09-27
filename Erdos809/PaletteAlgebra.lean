/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Algebraic assembly lemmas. These explicitly require the polynomial
inequality and palette decomposition; they are not the finite CP theorem. -/

namespace Erdos809

open scoped BigOperators

/-- A bound at every resource root bounds the triangle-weighted average. -/
theorem weighted_root_bound {V : Type*} [Fintype V]
    (weight tau q : V → ℝ) (P : ℝ)
    (hw : ∀ v, 0 ≤ weight v) (ht : ∀ v, 0 ≤ tau v) (hq : ∀ v, q v ≤ P) :
    (∑ v, weight v * tau v * q v) ≤ (∑ v, weight v * tau v) * P := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun v _ =>
    mul_le_mul_of_nonneg_left (hq v) (mul_nonneg (hw v) (ht v))

/-- Exact cancellation uses the very same matching value `nu` in both premises. -/
theorem palette_bound_of_polynomial {m f nu P PF B Δ : ℝ}
    (hΔ : 0 < Δ) (hroot : B ≤ Δ * PF)
    (hpoly : 0 ≤ 2*B + (1/2-m-2*f-2*nu)*Δ)
    (hdecomp : P = PF + m - f - nu) : 3*m/2 - 1/4 ≤ P := by
  have hmul : 0 ≤ (P - (3*m/2 - 1/4))*Δ := by
    rw [hdecomp]
    nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hmul hΔ)

/-- The averaged neighborhood cut bound forces positive triangle density even
when edge density has dropped slightly below one quarter. -/
theorem triangle_mass_of_cut_deficit {m MC Δ ξ ρ : ℝ}
    (hm : 0 ≤ m) (hξ : 0 ≤ ξ) (hρ : 0 < ρ)
    (hdensity : 1/4 - ξ ≤ m) (hdeficit : ρ ≤ m - MC)
    (hcut : 4*m^2 - 2*Δ ≤ MC) (hsmall : ξ ≤ ρ/2) : ρ/4 ≤ Δ := by
  have hquad : -ξ ≤ 4*m^2-m := by
    by_cases hquarter : 1/4 ≤ m
    · nlinarith [mul_nonneg hm (sub_nonneg.mpr hquarter)]
    · have hq := le_of_not_ge hquarter
      have hprod := mul_nonneg hm (show 0 ≤ m-1/4+ξ by linarith)
      have hprod' := mul_nonneg hξ (show 0 ≤ 1-4*m by linarith)
      nlinarith
  linarith

/-- Stable algebra after loss of density. The premises retain the exact
certificate and common-matching obligations instead of hiding them as axioms. -/
theorem stable_palette_bound_of_polynomial {m f nu P PF B Δ ξ ρ : ℝ}
    (hξ : 0 ≤ ξ) (hρ : 0 < ρ) (hΔ : ρ/4 ≤ Δ)
    (hroot : B ≤ Δ * PF)
    (hpoly : -ξ ≤ 2*B + (1/2-m-2*f-2*nu)*Δ)
    (hdecomp : P = PF + m - f - nu) :
    3*m/2 - 1/4 - 2*ξ/ρ ≤ P := by
  have hΔpos : 0 < Δ := by linarith
  have hquot : 0 ≤ 2*ξ/ρ := div_nonneg (by positivity) hρ.le
  have herror := mul_le_mul_of_nonneg_left hΔ hquot
  have hid : (2*ξ/ρ) * (ρ/4) = ξ/2 := by field_simp; ring
  rw [hid] at herror
  have hmul : 0 ≤ (P - (3*m/2 - 1/4 - 2*ξ/ρ))*Δ := by
    rw [hdecomp]
    nlinarith
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hmul hΔpos)

/-- The extracted matching only needs to give a lower bound for the actual
cover cost. Empty patterns and nonoptimal covers may make that cost larger. -/
theorem palette_bound_of_polynomial_le {m f nu P PF B Δ : ℝ}
    (hΔ : 0 < Δ) (hroot : B ≤ Δ * PF)
    (hpoly : 0 ≤ 2*B + (1/2-m-2*f-2*nu)*Δ)
    (hdecomp : PF + m - f - nu ≤ P) : 3*m/2 - 1/4 ≤ P :=
  (palette_bound_of_polynomial hΔ hroot hpoly rfl).trans hdecomp

theorem stable_palette_bound_of_polynomial_le {m f nu P PF B Δ ξ ρ : ℝ}
    (hξ : 0 ≤ ξ) (hρ : 0 < ρ) (hΔ : ρ/4 ≤ Δ)
    (hroot : B ≤ Δ * PF)
    (hpoly : -ξ ≤ 2*B + (1/2-m-2*f-2*nu)*Δ)
    (hdecomp : PF + m - f - nu ≤ P) :
    3*m/2 - 1/4 - 2*ξ/ρ ≤ P :=
  (stable_palette_bound_of_polynomial hξ hρ hΔ hroot hpoly rfl).trans hdecomp

end Erdos809
