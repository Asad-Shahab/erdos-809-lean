module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Source potential arithmetic

These are exact arithmetic ingredients of the fixed-margin peeling reduction.
They do not assert the existence of a graph peeling process.
-/

noncomputable section

namespace Erdos809.Source

/-- The source potential, with real arguments to make loss bookkeeping exact. -/
def potential (n m : ℝ) : ℝ := 3 * m / 2 - n ^ 2 / 4

/-- The quarter-density excess, including a possible single-edge excess. -/
def quarterSurplus (n m : ℝ) : ℝ := m - n ^ 2 / 4

lemma potential_delete (n m d : ℝ) :
    potential (n - 1) (m - d) - potential n m = (2 * n - 1) / 4 - 3 * d / 2 := by
  unfold potential
  ring

lemma surplus_delete (n m d : ℝ) :
    quarterSurplus (n - 1) (m - d) - quarterSurplus n m = (2 * n - 1) / 4 - d := by
  unfold quarterSurplus
  ring

lemma potential_delete_lower {n m d γ : ℝ}
    (hd : d < (1 / 3 + γ) * n + 1) :
    -(3 * γ / 2) * n - 7 / 4 < potential (n - 1) (m - d) - potential n m := by
  rw [potential_delete]
  linarith

lemma surplus_delete_lower {n m d γ : ℝ}
    (hd : d < (1 / 3 + γ) * n + 1) :
    (1 / 6 - γ) * n - 5 / 4 <
      quarterSurplus (n - 1) (m - d) - quarterSurplus n m := by
  rw [surplus_delete]
  linarith

lemma surplus_delete_strict {n m d γ : ℝ}
    (hγ : γ ≤ 1 / 48) (hn : 64 / 3 < n)
    (hd : d < (1 / 3 + γ) * n + 1) :
    quarterSurplus n m < quarterSurplus (n - 1) (m - d) := by
  have h := surplus_delete_lower (m := m) hd
  have hpos : 0 ≤ n := by linarith
  have hmul := mul_le_mul_of_nonneg_right hγ hpos
  linarith

lemma potential_initial {n m : ℝ} (hm : n ^ 2 / 4 < m) :
    n ^ 2 / 8 < potential n m := by
  unfold potential
  linarith

lemma potential_simple_bound {n m : ℝ} (hm : m ≤ n * (n - 1) / 2)
    (hn : 0 ≤ n) : potential n m ≤ n ^ 2 / 2 := by
  unfold potential
  nlinarith

lemma potential_loss {n h m q : ℝ} (hh : 0 ≤ h) (hhn : h ≤ n) :
    potential n m - potential h (m - q) ≤ 3 * q / 2 := by
  unfold potential
  nlinarith

/-- The global potential lower bound used throughout the peeling process. -/
def peelingBound (n γ : ℝ) : ℝ :=
  n ^ 2 / 8 - (3 * γ / 4) * n * (n + 1) - 7 * n / 4

lemma peelingBound_ge_numeric {n γ : ℝ} (hn : 0 ≤ n) (hγ : γ ≤ 1 / 48) :
    7 / 64 * n ^ 2 - 113 / 64 * n ≤ peelingBound n γ := by
  have hmul := mul_le_mul_of_nonneg_right hγ (show 0 ≤ n * (n + 1) by positivity)
  unfold peelingBound
  nlinarith

/-- A graph of order at most one third cannot retain the peeling lower bound.
The explicit constant 64 is enough, including all linear losses. -/
lemma peeling_order_gt_third {n h m γ : ℝ}
    (hn : 64 ≤ n) (hh : 0 ≤ h) (hγ : γ ≤ 1 / 48)
    (hm : m ≤ h * (h - 1) / 2)
    (hp : peelingBound n γ ≤ potential h m) :
    n / 3 < h := by
  by_contra hnot
  have hh' : h ≤ n / 3 := le_of_not_gt hnot
  have hpn := peelingBound_ge_numeric (by linarith : 0 ≤ n) hγ
  have hpm := potential_simple_bound hm hh
  have hsq : h ^ 2 ≤ n ^ 2 / 9 := by nlinarith [sq_nonneg (n / 3 - h)]
  have hlarge : 64 * n ≤ n ^ 2 := by nlinarith
  nlinarith

/-- Error absorption for the source reduction with gamma = epsilon / 12. -/
lemma peeling_terminal_absorption {n h ε r : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1 / 16)
    (hn : 64 / ε ≤ n) (hh : 0 ≤ h) (hhn : h ≤ n)
    (hr : peelingBound n (ε / 12) - (ε / 2) * h ^ 2 ≤ r) :
    (1 / 8 - ε) * n ^ 2 ≤ r := by
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  have hsq : h ^ 2 ≤ n ^ 2 := by nlinarith
  have hεn : 64 ≤ ε * n := by simpa [mul_comm] using (div_le_iff₀ hε).mp hn
  have hmult := mul_le_mul_of_nonneg_right hεn hn0
  have hsquare := mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε / 2 by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hε' hn0
  unfold peelingBound at hr
  nlinarith

end Erdos809.Source
