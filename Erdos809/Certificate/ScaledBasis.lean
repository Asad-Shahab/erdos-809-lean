module
public import Erdos809.Certificate.IntegerGram
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-! Link a table of scaled integer matrix entries to a basis-transformed PSD
matrix. The entry identities are separate finite kernel-checking obligations.
-/

namespace Erdos809.Certificate

theorem scaled_integer_basis_eq {K n m : Type*} [Field K] [CharZero K]
    [Fintype n] (A : Matrix n n ℤ) (B : Matrix m n ℤ) (Q : Matrix m m ℤ)
    (scaleA scaleQ : ℕ) (hscaleA : 0 < scaleA) (hscaleQ : 0 < scaleQ)
    (hentry : ∀ i j, (scaleA : ℤ) * Q i j =
      (scaleQ : ℤ) * ∑ k, ∑ l, B i k * A k l * B j l) :
    (fun i j => (Q i j : K) / scaleQ : Matrix m m K) =
      Matrix.of (fun i k => (B i k : K)) *
        Matrix.of (fun k l => (A k l : K) / scaleA) *
        (Matrix.of (fun j l => (B j l : K))).transpose := by
  ext i j
  have hcast : (scaleA : K) * (Q i j : K) =
      (scaleQ : K) * ∑ k, ∑ l, (B i k : K) * (A k l : K) * (B j l : K) := by
    exact_mod_cast hentry i j
  have hA : (scaleA : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hscaleA)
  have hQ : (scaleQ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hscaleQ)
  calc
    _ = (∑ k, ∑ l, (B i k : K) * (A k l : K) * (B j l : K)) / scaleA := by
      apply (div_eq_div_iff hQ hA).mpr
      simpa only [mul_comm] using hcast
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      change ((B i k : K) * (A k l : K) * (B j l : K)) / scaleA =
        (B i k : K) * ((A k l : K) / scaleA) * (B j l : K)
      ring

theorem posSemidef_of_scaled_integer_basis {K n m : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [StarRing K] [StarOrderedRing K] [TrivialStar K] [Fintype n] [Finite m]
    (A : Matrix n n ℤ) (B : Matrix m n ℤ) (Q : Matrix m m ℤ)
    (scaleA scaleQ : ℕ) (hscaleA : 0 < scaleA) (hscaleQ : 0 < scaleQ)
    (hentry : ∀ i j, (scaleA : ℤ) * Q i j =
      (scaleQ : ℤ) * ∑ k, ∑ l, B i k * A k l * B j l)
    (hA : Matrix.PosSemidef (fun i j => (A i j : K) / scaleA : Matrix n n K)) :
    Matrix.PosSemidef (fun i j => (Q i j : K) / scaleQ : Matrix m m K) := by
  rw [scaled_integer_basis_eq A B Q scaleA scaleQ hscaleA hscaleQ hentry]
  have h := hA.mul_mul_conjTranspose_same (Matrix.of fun i k => (B i k : K))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

end Erdos809.Certificate
