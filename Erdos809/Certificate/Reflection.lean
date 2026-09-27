import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Kernel-checkable interfaces for the Campaign 4 rational certificate.

The source generator is untrusted. Concrete data must satisfy the propositions
below in Lean; none of these interfaces assumes that an external checker ran.
-/

namespace Erdos809.Certificate

/-- An exact nonnegative rational, represented by a natural numerator and denominator.
The denominator-zero convention agrees with field division. Concrete source data
additionally verifies that every denominator is positive. -/
def nonnegRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / q.2

theorem nonnegRat_nonneg (q : ℕ × ℕ) : 0 ≤ nonnegRat q := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem nonnegRat_pos (q : ℕ × ℕ) (hn : 0 < q.1) (hd : 0 < q.2) :
    0 < nonnegRat q := by
  exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hd)

/-- A supplied LDL factorization implies positive semidefiniteness. The identity
is a mathematical equality, to be checked separately for each concrete block. -/
theorem posSemidef_of_ldl {n : Type*} [Fintype n] [DecidableEq n]
    (R L : Matrix n n ℚ) (d : n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hR : R = L * Matrix.diagonal d * L.transpose) : R.PosSemidef := by
  rw [hR]
  simpa using (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L

/-- The integral change of basis used by the certificate preserves positivity. -/
theorem posSemidef_basis {m n : Type*} [Finite m] [Fintype n]
    (R : Matrix n n ℚ) (B : Matrix m n ℚ) (hR : R.PosSemidef) :
    (B * R * B.transpose).PosSemidef := by
  simpa using hR.mul_mul_conjTranspose_same B

/-- The finite algebraic part of a flag certificate: if a target expectation is
a nonnegative combination of valid columns and Gram terms plus coefficient
slacks, then it is nonnegative. The application must supply the coefficient
identity and the semantic nonnegativity of every column. -/
theorem certificate_nonnegative {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (target : ℚ) (alpha column : I → ℚ) (gram : J → ℚ) (p slack : K → ℚ)
    (halpha : ∀ i, 0 ≤ alpha i) (hcolumn : ∀ i, 0 ≤ column i)
    (hgram : ∀ j, 0 ≤ gram j) (hp : ∀ k, 0 ≤ p k) (hslack : ∀ k, 0 ≤ slack k)
    (hidentity : target = (∑ i, alpha i * column i) + (∑ j, gram j) +
      ∑ k, p k * slack k) : 0 ≤ target := by
  rw [hidentity]
  exact add_nonneg
    (add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (halpha i) (hcolumn i))
      (Finset.sum_nonneg fun j _ => hgram j))
    (Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hslack k))

end Erdos809.Certificate
