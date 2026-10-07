module

public import Erdos809.Verification.PaletteBridge
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-! Convert the attained epsilon formulation to asymptotic equivalence. -/

@[expose] public section

namespace Erdos809.FormalConjecturesBridge

open SimpleGraph Filter Asymptotics
open scoped Topology

/-- The epsilon bounds imply convergence of the ratio to one. The cutoff is
enlarged to one so that the quadratic denominator is strictly positive. -/
theorem ratio_tendsto_one {ℓ : ℕ} (h : CycleAsymptoticExtremalValue ℓ) :
    Tendsto
      (fun n : ℕ ↦ (strongChromaticNum (cycleGraph ℓ) n (n ^ 2 / 4 + 1) : ℝ) /
        ((n : ℝ) ^ 2 / 8)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨N, hN⟩ := h ((1 - a) / 16) (by linarith)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    obtain ⟨q, hq, hl, _⟩ := hN n ((le_max_left _ _).trans hn)
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
    rw [threshold_eq, strongChromaticNum_eq hq]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2 / 8)).mpr
    have hgap : a * ((n : ℝ) ^ 2 / 8) <
        (1 / 8 - (1 - a) / 16) * (n : ℝ) ^ 2 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - a) hsq]
    exact hgap.trans_le hl
  · intro a ha
    obtain ⟨N, hN⟩ := h ((a - 1) / 16) (by linarith)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    obtain ⟨q, hq, _, hu⟩ := hN n ((le_max_left _ _).trans hn)
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
    rw [threshold_eq, strongChromaticNum_eq hq]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2 / 8)).mpr
    have hgap : (1 / 8 + (a - 1) / 16) * (n : ℝ) ^ 2 <
        a * ((n : ℝ) ^ 2 / 8) := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < a - 1) hsq]
    exact hu.trans_lt hgap

/-- Generic conversion from an attained epsilon minimum to the exact FC asymptotic. -/
theorem asymptotic_bridge {ℓ : ℕ} (h : CycleAsymptoticExtremalValue ℓ) :
    (fun n ↦ (strongChromaticNum (cycleGraph ℓ) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 :=
  isEquivalent_of_tendsto_one (ratio_tendsto_one h)

end Erdos809.FormalConjecturesBridge
