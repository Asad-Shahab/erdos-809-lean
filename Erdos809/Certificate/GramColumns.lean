import Erdos809.Certificate.RootedGram
import Erdos809.Certificate.TypedGram
import Erdos809.Certificate.LocalFormula
import Erdos809.Certificate.LocalExpectation

/-! Positivity of the exact integer Gram columns in the local certificate.
Their matrix entries are linked to checked PSD matrices at the common scale. -/

namespace Erdos809.Certificate

variable {V : Type*} [Fintype V]

theorem local_rootGram_nonnegative (x : VertexWeights V) (κ : ColorKernel V) :
    0 ≤ localExpectation x κ (fun g => (LocalFormula.rootGram g : ℝ)) := by
  have h := rooted_flag_gram_nonnegative x.weight x.nonneg κ.prob κ.nonneg κ.total
    LinkedMatrices.rootReal LinkedMatrices.rootReal_posSemidef FlagData.rootFlag
  have hgram : 0 ≤ localExpectation x κ (fun g =>
      LinkedMatrices.rootReal (LocalFormula.rootAt g 0 1 2) (LocalFormula.rootAt g 0 3 4)) := by
    simpa only [localExpectation, sampleWeight, typeWeight, markWeight, mul_assoc,
      Finset.mul_sum] using h
  have hscale : (Coefficients.scale : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Coefficients.scale_positive)
  calc
    0 ≤ (4 * (Coefficients.scale : ℝ)) * localExpectation x κ (fun g =>
        LinkedMatrices.rootReal (LocalFormula.rootAt g 0 1 2) (LocalFormula.rootAt g 0 3 4)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hgram
    _ = _ := by
      rw [← localExpectation_const_mul]
      congr 1
      funext g
      rw [LinkedMatrices.rootReal_apply]
      simp only [LocalFormula.rootGram, Int.cast_mul, Int.cast_ofNat]
      field_simp

theorem local_typeGram_term_nonnegative (x : VertexWeights V) (κ : ColorKernel V)
    (t : Fin 14) :
    0 ≤ localExpectation x κ (fun g => if LocalFormula.literalRoot g t then
      (LinkedMatrices.typeNumerator t (LocalFormula.attachmentAt g t 3)
        (LocalFormula.attachmentAt g t 4) : ℝ) else 0) := by
  have h := typed_flag_gram_nonnegative x.weight x.nonneg κ.prob κ.nonneg κ.total
    (LinkedMatrices.typeReal t) (LinkedMatrices.typeReal_posSemidef t)
    (FlagData.attachment t) (FlagData.literalType t 0) (FlagData.literalType t 1)
    (FlagData.literalType t 2)
  have hgram : 0 ≤ localExpectation x κ (fun g => if LocalFormula.literalRoot g t then
      LinkedMatrices.typeReal t (LocalFormula.attachmentAt g t 3)
        (LocalFormula.attachmentAt g t 4) else 0) := by
    simpa only [localExpectation, sampleWeight, typeWeight, markWeight, mul_assoc,
      Finset.mul_sum] using h
  have hscale : (Coefficients.scale : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Coefficients.scale_positive)
  calc
    0 ≤ (Coefficients.scale : ℝ) * localExpectation x κ (fun g =>
        if LocalFormula.literalRoot g t then
          LinkedMatrices.typeReal t (LocalFormula.attachmentAt g t 3)
            (LocalFormula.attachmentAt g t 4) else 0) :=
      mul_nonneg (Nat.cast_nonneg _) hgram
    _ = _ := by
      rw [← localExpectation_const_mul]
      congr 1
      funext g
      by_cases hg : LocalFormula.literalRoot g t
      · simp only [hg, if_true, LinkedMatrices.typeReal]
        field_simp
      · simp only [hg, if_false, mul_zero]

theorem local_typeGram_nonnegative (x : VertexWeights V) (κ : ColorKernel V) :
    0 ≤ localExpectation x κ (fun g => (LocalFormula.typeGram g : ℝ)) := by
  have h := Finset.sum_nonneg (s := Finset.univ) fun t _ =>
    local_typeGram_term_nonnegative x κ t
  have heq : localExpectation x κ (fun g => (LocalFormula.typeGram g : ℝ)) =
      4 * ∑ t, localExpectation x κ (fun g => if LocalFormula.literalRoot g t then
        (LinkedMatrices.typeNumerator t (LocalFormula.attachmentAt g t 3)
          (LocalFormula.attachmentAt g t 4) : ℝ) else 0) := by
    simp only [LocalFormula.typeGram, Int.cast_mul, Int.cast_ofNat, Int.cast_sum,
      Int.cast_ite, Int.cast_zero]
    rw [localExpectation_const_mul]
    congr 1
    unfold localExpectation
    simp only [Finset.mul_sum]
    calc
      _ = ∑ v : Fin 5 → V, ∑ t, ∑ g : LocalGraph,
          sampleWeight x κ v g * (if LocalFormula.literalRoot g t then
            (LinkedMatrices.typeNumerator t (LocalFormula.attachmentAt g t 3)
              (LocalFormula.attachmentAt g t 4) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [heq]
  exact mul_nonneg (by norm_num) h

end Erdos809.Certificate
