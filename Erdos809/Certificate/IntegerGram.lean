module
public import Erdos809.Certificate.Reflection
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Convert

@[expose] public section

namespace Erdos809.Certificate

/-- Fraction-free Gram witnesses avoid reducing rational Gaussian elimination
inside the kernel. The witness equality uses only integer sums and products. -/
theorem posSemidef_of_integer_gram {K n k : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [StarRing K] [StarOrderedRing K] [TrivialStar K] [Fintype n] [Fintype k]
    [DecidableEq k] (A : Matrix n n ℤ) (W : Matrix n k ℤ) (c : k → ℕ)
    (scale factor : ℕ) (hscale : 0 < scale) (hfactor : 0 < factor)
    (hentry : ∀ i j, (factor : ℤ) * A i j = ∑ t, W i t * (c t : ℤ) * W j t) :
    Matrix.PosSemidef (fun i j => (A i j : K) / scale : Matrix n n K) := by
  let V : Matrix n k K := fun i t => W i t
  let e : k → K := fun t => c t
  have he : ∀ t, 0 ≤ e t := fun t => Nat.cast_nonneg (c t)
  have hgram : (V * Matrix.diagonal e * V.transpose).PosSemidef := by
    simpa using (Matrix.PosSemidef.diagonal he).mul_mul_conjTranspose_same V
  have hid : V * Matrix.diagonal e * V.transpose =
      (fun i j => (factor : K) * (A i j : K) : Matrix n n K) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    dsimp only [V, e]
    exact_mod_cast (hentry i j).symm
  rw [hid] at hgram
  have hden : 0 < (factor : K) * (scale : K) :=
    mul_pos (Nat.cast_pos.mpr hfactor) (Nat.cast_pos.mpr hscale)
  have hmatrix :
      (fun i j => (A i j : K) / scale : Matrix n n K) =
        ((factor : K) * (scale : K))⁻¹ •
          (fun i j => (factor : K) * (A i j : K) : Matrix n n K) := by
    ext i j
    change (A i j : K) / scale =
      ((factor : K) * (scale : K))⁻¹ * ((factor : K) * (A i j : K))
    have hs : (scale : K) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hscale)
    have hf : (factor : K) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hfactor)
    field_simp [hs, hf]
  rw [hmatrix]
  exact hgram.smul (inv_nonneg.mpr hden.le)


end Erdos809.Certificate
