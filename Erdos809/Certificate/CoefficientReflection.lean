import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.Defs

/-! A small kernel evaluator for scaled integer coefficient identities.
The two lists preserve the separate Gram and valid-column contributions.
-/

namespace Erdos809.Certificate

def integerProducts (xs : List (ℤ × ℤ)) : ℤ :=
  (xs.map fun x => x.1 * x.2).sum

structure ScaledCoefficientRow where
  target : ℤ
  gram : List (ℤ × ℤ)
  constraints : List (ℤ × ℤ)
  slack : ℕ

def ScaledCoefficientRow.Valid (scale : ℕ) (row : ScaledCoefficientRow) : Prop :=
  row.target * scale = integerProducts row.gram + integerProducts row.constraints + row.slack

instance (scale : ℕ) (row : ScaledCoefficientRow) : Decidable (row.Valid scale) :=
  inferInstanceAs (Decidable (_ = _))

theorem coefficient_rows_valid (scale : ℕ) (rows : List ScaledCoefficientRow)
    (h : rows.all (fun row => decide (row.Valid scale)) = true)
    (row : ScaledCoefficientRow) (hr : row ∈ rows) : row.Valid scale := by
  have hrow := List.all_eq_true.mp h row hr
  exact of_decide_eq_true hrow

end Erdos809.Certificate
