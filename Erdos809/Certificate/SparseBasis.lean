import Erdos809.Certificate.ScaledBasis
import Mathlib.Algebra.BigOperators.Ring.List

/-! Sparse integer basis rows. The finite list evaluator is connected to the
ordinary full matrix product by a proved identity, including repeated indices.
This only changes the size of concrete kernel reductions.
-/

namespace Erdos809.Certificate

def sparseBasisEntry {I : Type*} [DecidableEq I] (row : List (I × ℤ)) (i : I) : ℤ :=
  (row.map fun e => if e.1 = i then e.2 else 0).sum

def sparseBilinear {I : Type*} (A : Matrix I I ℤ) (row col : List (I × ℤ)) : ℤ :=
  (row.map fun e => (col.map fun f => e.2 * A e.1 f.1 * f.2).sum).sum

theorem sum_sparseBasisEntry_mul {I : Type*} [Fintype I] [DecidableEq I]
    (row : List (I × ℤ)) (f : I → ℤ) :
    (∑ i, sparseBasisEntry row i * f i) = (row.map fun e => e.2 * f e.1).sum := by
  induction row with
  | nil => simp [sparseBasisEntry]
  | cons e row ih =>
    change (∑ i, ((if e.1 = i then e.2 else 0) + sparseBasisEntry row i) * f i) =
      e.2 * f e.1 + (row.map fun a => a.2 * f a.1).sum
    simp only [add_mul, Finset.sum_add_distrib]
    rw [ih]
    simp [ite_mul]

theorem sparseBasis_bilinear {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (row col : List (I × ℤ)) :
    (∑ i, ∑ j, sparseBasisEntry row i * A i j * sparseBasisEntry col j) =
      sparseBilinear A row col := by
  calc
    _ = ∑ i, sparseBasisEntry row i * (∑ j, sparseBasisEntry col j * A i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (row.map fun e => e.2 * (∑ j, sparseBasisEntry col j * A e.1 j)).sum :=
      sum_sparseBasisEntry_mul row _
    _ = sparseBilinear A row col := by
      unfold sparseBilinear
      apply congrArg List.sum
      apply List.map_congr_left
      intro e _
      rw [sum_sparseBasisEntry_mul]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro f _
      ring

end Erdos809.Certificate
