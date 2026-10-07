module
public import Erdos809.MatchingMarks
public import Erdos809.Certificate.Marking

@[expose] public section

/-! The certificate's auxiliary four-color sampling law for one actual
triangular matching. Its root and selected-edge constraints follow from that
same matching; no random sample is asserted to be a matching. -/

namespace Erdos809.TriangularMatching

open Finset VertexWeights
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)
variable (hinj : Function.Injective (fun i => s(y.left i, y.right i)))

noncomputable def colorKernel : Certificate.ColorKernel V :=
  Certificate.markedHostKernel G (nontriangularSector G) y.markProbability
    y.markProbability_nonneg (y.markProbability_le_one hinj)

theorem colorKernel_symmetric (u v : V) (c : Fin 4) :
    (y.colorKernel hinj).prob u v c = (y.colorKernel hinj).prob v u c :=
  Certificate.markedProbability_symm G (nontriangularSector G) y.markProbability
    y.markProbability_symm u v c

theorem colorKernel_selected (u v : V) :
    (y.colorKernel hinj).prob u v 3 = y.markProbability u v := by
  classical
  by_cases hg : G.Adj u v
  · by_cases hw : Walk2 G u v
    · simp [colorKernel, Certificate.markedHostKernel, Certificate.markedProbability,
        nontriangularSector, hg, hw]
    · have hz := y.markProbability_zero_of_not_triangular (fun ht => hw ht.2)
      simp [colorKernel, Certificate.markedHostKernel, Certificate.markedProbability,
        nontriangularSector, hg, hw, hz]
  · have hz := y.markProbability_zero_of_not_triangular (fun ht => hg ht.1)
    simp [colorKernel, Certificate.markedHostKernel, Certificate.markedProbability, hg, hz]

theorem colorKernel_F_triangle_free (u v : V)
    (hF : (nontriangularSector G).Adj u v) : ¬ Walk2 G u v := hF.2

variable [DecidableRel G.Adj]

include hinj in
/-- K(w) is nonnegative for the same actual matching used in the mark law. -/
theorem marked_root_margin (w : V) :
    0 ≤ y.mass - ∑ v, x.weight v * y.markedDegree v *
      if G.Adj w v then 1 else 0 := by
  rw [y.markedDegree_rootLoad hinj]
  exact sub_nonneg.mpr (y.rootLoad_le_mass w)

/-- This is the expected selected-edge union constraint. It applies only when
the selected mark has positive probability on the specified host pair. -/
theorem selected_union_margin [DecidableEq V] {δ : ℝ} (hδ : 1 / 3 ≤ δ)
    (hmin : x.MinDegreeAtLeast G δ) {u v : V}
    (hpos : 0 < (y.colorKernel hinj).prob u v 3) :
    0 ≤ 2 / 3 - x.mass (neighbors G u ∪ neighbors G v) := by
  rw [y.colorKernel_selected hinj] at hpos
  have hu := y.markProbability_used_union_bound hinj hmin hpos
  linarith

end Erdos809.TriangularMatching
