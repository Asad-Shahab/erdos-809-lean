module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Numerical margins for the near-cut construction

All quantities are real numbers. The graph application substitutes its finite
cardinalities. The elementary balance estimate avoids any square-root notation.
-/

namespace Erdos809.Source

/-- The normalized numerical assumptions supplied by the near-cut count. -/
structure NearCutParameters (τ n p q t : ℝ) : Prop where
  tau_pos : 0 < τ
  tau_le : τ ≤ 1 / 32
  order_large : 8 / τ ^ 3 ≤ n
  left_size : (1 / 2 - τ / 4) * n ≤ p
  right_size : (1 / 2 - τ / 4) * n ≤ q
  bad_nonneg : 0 ≤ t
  bad_size : t ≤ 2 * τ ^ 2 * n

namespace NearCutParameters

variable {τ n p q t : ℝ} (h : NearCutParameters τ n p q t)

include h

theorem symm : NearCutParameters τ n q p t :=
  ⟨h.tau_pos, h.tau_le, h.order_large, h.right_size, h.left_size, h.bad_nonneg, h.bad_size⟩

theorem order_pos : 0 < n :=
  lt_of_lt_of_le (div_pos (by norm_num) (pow_pos h.tau_pos 3)) h.order_large

theorem scaled_order_upper : τ * n ≤ n / 32 := by
  have hm := mul_le_mul_of_nonneg_right h.tau_le h.order_pos.le
  nlinarith only [hm]

/-- A deliberately weak uniform margin suffices for all finite exclusions. -/
theorem scaled_order_lower : 64 ≤ τ * n := by
  have hproduct : 8 ≤ n * τ ^ 3 :=
    (div_le_iff₀ (pow_pos h.tau_pos 3)).mp h.order_large
  have hτsq : τ ^ 2 ≤ 1 / 8 := by
    have hm := mul_le_mul_of_nonneg_left h.tau_le h.tau_pos.le
    nlinarith only [hm, h.tau_le]
  have hτn : 0 ≤ τ * n := mul_nonneg h.tau_pos.le h.order_pos.le
  have hm := mul_le_mul_of_nonneg_right hτsq hτn
  nlinarith only [hproduct, hm]

theorem order_lower : 64 ≤ n := by
  have hu := h.scaled_order_upper
  have hl := h.scaled_order_lower
  linarith

theorem bad_size_scaled : t ≤ τ * n / 16 := by
  have hτsq : 2 * τ ^ 2 ≤ τ / 16 := by
    have hm := mul_le_mul_of_nonneg_left h.tau_le h.tau_pos.le
    nlinarith only [hm]
  have hm := mul_le_mul_of_nonneg_right hτsq h.order_pos.le
  nlinarith only [h.bad_size, hm]

theorem bad_size_order : t ≤ n / 32 := by
  have hb := h.bad_size_scaled
  have hu := h.scaled_order_upper
  have hn := h.order_pos
  linarith

theorem sixteen_bad_le : 16 * t ≤ τ * n := by
  linarith only [h.bad_size_scaled]

theorem three_bad_le : 3 * t ≤ τ * n := by
  linarith only [h.sixteen_bad_le, h.bad_nonneg]

theorem left_size_third : n / 3 ≤ p := by
  have hu := h.scaled_order_upper
  have hp := h.left_size
  have hn := h.order_pos
  nlinarith only [hu, hp, hn]

/-- A typical crossing degree exceeds the trigger's half-side threshold. -/
theorem typical_cross_degree : p / 2 - t < p - τ * n := by
  have hp := h.left_size_third
  have hu := h.scaled_order_upper
  have hn := h.order_pos
  linarith only [hp, hu, hn, h.bad_nonneg]

/-- There is room to avoid two vertices in each trigger-neighbor intersection. -/
theorem trigger_common : 2 < p / 2 - t - τ * n := by
  have hp := h.left_size_third
  have hu := h.scaled_order_upper
  have ht := h.bad_size_order
  have hn := h.order_lower
  linarith only [hp, hu, ht, hn]

/-- Two typical opposite-side vertices have more than two common neighbors. -/
theorem typical_common : 2 < p - 2 * τ * n := by
  have hp := h.left_size_third
  have hu := h.scaled_order_upper
  have hn := h.order_lower
  linarith only [hp, hu, hn]

/-- The selected left-set bound used by the palette estimate. -/
theorem selected_left {s : ℝ} (hs : p / 2 - τ * n - 2 * t < s) :
    (1 / 4 - 3 * τ / 2) * n ≤ s := by
  have hp := h.left_size
  have ht := h.bad_size_scaled
  have hτn : 0 ≤ τ * n := mul_nonneg h.tau_pos.le h.order_pos.le
  nlinarith only [hs, hp, ht, hτn]

/-- Excluding the two trigger endpoints still leaves the required row size. -/
theorem selected_right {r : ℝ} (hr : q - t - 2 ≤ r) :
    (1 / 2 - 3 * τ / 2) * n ≤ r - τ * n ∧ 1 < r - τ * n := by
  have hq := h.right_size
  have ht := h.bad_size_scaled
  have hτn := h.scaled_order_lower
  have hl : (1 / 2 - 3 * τ / 2) * n ≤ r - τ * n := by
    nlinarith only [hr, hq, ht, hτn]
  refine ⟨hl, ?_⟩
  have hu := h.scaled_order_upper
  have hn := h.order_lower
  nlinarith only [hl, hu, hn]

/-- Cubic cut deficit is small enough for the rational side-balance margin. -/
theorem balance_square : τ ^ 3 * n ^ 2 ≤ (τ * n / 4) ^ 2 := by
  have hτ : τ ≤ 1 / 16 := h.tau_le.trans (by norm_num)
  have hcoeff := mul_le_mul_of_nonneg_right hτ (sq_nonneg τ)
  have hscaled := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg n)
  nlinarith only [hscaled]

end NearCutParameters
end Erdos809.Source
