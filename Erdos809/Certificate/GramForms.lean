import Erdos809.Certificate.Reflection
import Mathlib.Data.Real.Star

/-! Finite conditional Gram forms. The application supplies the actual flag
probability vectors and their root weights; no sampling interpretation is
assumed by these algebraic lemmas. -/

namespace Erdos809.Certificate

theorem gram_form_nonnegative {I : Type*} [Fintype I]
    (Q : Matrix I I ℝ) (hQ : Q.PosSemidef) (f : I → ℝ) :
    0 ≤ ∑ i, ∑ j, f i * Q i j * f j := by
  simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, mul_assoc] using hQ.dotProduct_mulVec_nonneg f

/-- A finite nonnegative mixture of conditional flag quadratic forms. -/
theorem averaged_gram_nonnegative {S I : Type*} [Fintype S] [Fintype I]
    (Q : Matrix I I ℝ) (hQ : Q.PosSemidef)
    (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (f : S → I → ℝ) :
    0 ≤ ∑ s, p s * (∑ i, ∑ j, f s i * Q i j * f s j) := by
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (hp s) (gram_form_nonnegative Q hQ (f s))

/-- Any classifier of finite extension states can index a PSD Gram form.
The classifier need not be injective, so repeated flags and host types are
included without a distinctness or canonicalization assumption. -/
theorem flag_gram_nonnegative {S I : Type*} [Fintype S] [Fintype I]
    (Q : Matrix I I ℝ) (hQ : Q.PosSemidef) (flag : S → I) (w : S → ℝ) :
    0 ≤ ∑ s, ∑ t, w s * w t * Q (flag s) (flag t) := by
  have h := gram_form_nonnegative (Q.submatrix flag flag) (hQ.submatrix flag) w
  convert h using 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.submatrix_apply]
  ring

end Erdos809.Certificate
