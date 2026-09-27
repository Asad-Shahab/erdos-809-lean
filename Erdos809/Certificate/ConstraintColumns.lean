import Erdos809.Certificate.ConstraintExpectation
import Erdos809.Certificate.LocalFormula
import Erdos809.Certificate.LocalExpectation

/-! The exact stored ordered constraint formulas satisfy the graph-model
bounds. Positivity uses total classifiers only; their canonical interpretation
is unnecessary. The density loss uses the checked largest multiplier bound. -/

noncomputable section
namespace Erdos809.Certificate

open Finset VertexWeights FlagData
open scoped BigOperators

private def densityEvent (c : PairPosition 3 → Fin 4) : ℝ :=
  densityNumerator (tripleType (c ⟨(0,1), by decide⟩) (c ⟨(0,2), by decide⟩)
    (c ⟨(1,2), by decide⟩))

private def degreeEvent (c : PairPosition 4 → Fin 4) : ℝ :=
  3 * ((4 * degreeNumerator (degreeFlag (c ⟨(0,1), by decide⟩) (c ⟨(0,2), by decide⟩)
    (c ⟨(0,3), by decide⟩) (c ⟨(1,2), by decide⟩) (c ⟨(1,3), by decide⟩)
    (c ⟨(2,3), by decide⟩)) / 3 : ℕ) : ℝ)

private def rootEvent (c : PairPosition 3 → Fin 4) : ℝ :=
  2 * (selected_rootNumerator (rootFlag (c ⟨(0,1), by decide⟩) (c ⟨(0,2), by decide⟩)
    (c ⟨(1,2), by decide⟩)) : ℝ)

private def unionEvent (c : PairPosition 4 → Fin 4) : ℝ :=
  3 * ((4 * unionNumerator (unionFlag (c ⟨(0,1), by decide⟩) (c ⟨(0,2), by decide⟩)
    (c ⟨(0,3), by decide⟩) (c ⟨(1,2), by decide⟩) (c ⟨(1,3), by decide⟩)
    (c ⟨(2,3), by decide⟩)) / 3 : ℕ) : ℝ)

private theorem density_formula (g : LocalGraph) :
    (LocalFormula.density g : ℝ) =
      densityEvent (fun p => g (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
        (2 * edgeFlag (g (densityFreshPair 0)) - 1) := by
  simp [LocalFormula.density, LocalFormula.typeAt, densityEvent, initialPairEmbedding,
    positionPairEmbedding, densityFreshPair, LocalGraph.color, LocalFormula.edge, edgeFlag]

private lemma edge_cast (c : Fin 4) : (LocalFormula.edge c : ℝ) = edgeFlag c := by
  simp [LocalFormula.edge, edgeFlag]

private lemma selected_cast (c : Fin 4) : (LocalFormula.selected c : ℝ) = selectedFlag c := by
  simp [LocalFormula.selected, selectedFlag]

private lemma degreeEvent_eq (g : LocalGraph) :
    degreeEvent (fun p => g (initialPairEmbedding (by decide : 4 ≤ 5) p)) =
      3 * ((4 * degreeNumerator (LocalFormula.degreeAt g) / 3 : ℕ) : ℝ) := rfl

private lemma unionEvent_eq (g : LocalGraph) :
    unionEvent (fun p => g (initialPairEmbedding (by decide : 4 ≤ 5) p)) =
      3 * ((4 * unionNumerator (LocalFormula.unionAt g) / 3 : ℕ) : ℝ) := rfl

private lemma rootEvent_eq (g : LocalGraph) :
    rootEvent (fun p => g (initialPairEmbedding (by decide : 3 ≤ 5) p)) =
      2 * (selected_rootNumerator (LocalFormula.rootAt g 0 1 2) : ℝ) := rfl

private theorem degree_formula (g : LocalGraph) :
    (LocalFormula.degree g : ℝ) =
      degreeEvent (fun p => g (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
        (edgeFlag (g (degreeFreshPair 0)) - 1 / 3) := by
  simp only [LocalFormula.degree, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_one, edge_cast, degreeEvent_eq]
  change (((4 * degreeNumerator (LocalFormula.degreeAt g) / 3 : ℕ) : ℝ) *
    (3 * edgeFlag (g.color 0 4) - 1)) =
    (3 * ((4 * degreeNumerator (LocalFormula.degreeAt g) / 3 : ℕ) : ℝ)) *
      (edgeFlag (g.color 0 4) - 1 / 3)
  ring

private theorem union_formula (g : LocalGraph) :
    (LocalFormula.union g : ℝ) =
      unionEvent (fun p => g (initialPairEmbedding (by decide : 4 ≤ 5) p)) *
        selectedFlag (g (initialPairEmbedding (by decide : 4 ≤ 5) unionOldPair)) *
        unionExtensionTarget (fun i => g (unionFreshPairs i)) := by
  have he (a b : Fin 4) :
      (if a ≠ 0 ∨ b ≠ 0 then (1 : ℝ) else 0) =
        edgeFlag a + edgeFlag b - edgeFlag a * edgeFlag b := by
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [edgeFlag, ha, hb]
  simp only [LocalFormula.union, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_ite, Int.cast_one, Int.cast_zero, selected_cast, unionEvent_eq]
  rw [he]
  change (((4 * unionNumerator (LocalFormula.unionAt g) / 3 : ℕ) : ℝ) * selectedFlag (g.color 0 1) *
    (2 - 3 * (edgeFlag (g.color 0 4) + edgeFlag (g.color 1 4) - edgeFlag (g.color 0 4) * edgeFlag (g.color 1 4)))) =
    (3 * ((4 * unionNumerator (LocalFormula.unionAt g) / 3 : ℕ) : ℝ)) * selectedFlag (g.color 0 1) *
      (2 / 3 - edgeFlag (g.color 0 4) - edgeFlag (g.color 1 4) + edgeFlag (g.color 0 4) * edgeFlag (g.color 1 4))
  ring

/-- Swap the old and fresh nonroot positions; this sends the stored root
orientation (old034/new12) to the proved old012/new34 orientation. -/
private def rootSwap : Equiv.Perm (Fin 5) where
  toFun := ![0,3,4,1,2]
  invFun := ![0,3,4,1,2]
  left_inv := by decide
  right_inv := by decide

private theorem root_formula (g : LocalGraph) :
    (LocalFormula.root (g.relabel rootSwap) : ℝ) =
      rootEvent (fun p => g (initialPairEmbedding (by decide : 3 ≤ 5) p)) *
        rootExtensionTarget (fun p => g (rootFreshPairs p)) := by
  simp only [LocalFormula.root, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, Int.cast_one,
    selected_cast, edge_cast, LocalFormula.rootAt, LocalGraph.color_relabel]
  rw [rootEvent_eq]
  change (2 * (selected_rootNumerator (LocalFormula.rootAt g 0 1 2) : ℝ)) *
      selectedFlag (g.color 3 4) * (1 - edgeFlag (g.color 0 3) - edgeFlag (g.color 0 4)) =
    (2 * (selected_rootNumerator (LocalFormula.rootAt g 0 1 2) : ℝ)) *
      (1 * 1 * selectedFlag (g.color 3 4) - edgeFlag (g.color 0 3) * 1 * selectedFlag (g.color 3 4) -
        1 * edgeFlag (g.color 0 4) * selectedFlag (g.color 3 4))
  ring

variable {V E : Type*} [Fintype V] [Fintype E]
  {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)
  (hinj : Function.Injective (fun i => s(y.left i, y.right i)))

/-- The exact stored density column loses at most four scale units per unit
of the sub-quarter density error. -/
theorem local_density_lower_bound {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hdensity : 1 / 4 - ξ ≤ x.edgeMass G) :
    -(4 * (Coefficients.scale : ℝ) * ξ) ≤
      localExpectation x (y.colorKernel hinj) (fun g => (LocalFormula.density g : ℝ)) := by
  have h := density_column_lower_bound y hinj (fun _ c => densityEvent c)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_le.mpr (densityNumerator_le_scale _))
    hξ hdensity
  simpa only [localExpectation, oldSampleAverage, ← density_formula] using h

/-- Exact integer division in the stored coefficient is retained. Its
nonnegativity suffices; no divisibility assumption is inserted. -/
theorem local_degree_nonnegative {δ : ℝ} (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ localExpectation x (y.colorKernel hinj) (fun g => (LocalFormula.degree g : ℝ)) := by
  have h := degree_column_nonnegative y hinj (fun _ c => degreeEvent c)
    (fun _ _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ hmin
  simpa only [localExpectation, oldSampleAverage, ← degree_formula] using h

theorem local_root_nonnegative :
    0 ≤ localExpectation x (y.colorKernel hinj) (fun g => (LocalFormula.root g : ℝ)) := by
  have h := root_column_nonnegative y hinj (fun _ c => rootEvent c)
    (fun _ _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hr : 0 ≤ localExpectation x (y.colorKernel hinj)
      (fun g => (LocalFormula.root (g.relabel rootSwap) : ℝ)) := by
    simpa only [localExpectation, oldSampleAverage, ← root_formula] using h
  rwa [localExpectation_relabel x (y.colorKernel hinj) (y.colorKernel_symmetric hinj)
    (fun g => (LocalFormula.root g : ℝ)) rootSwap] at hr

theorem local_union_nonnegative [DecidableEq V] {δ : ℝ}
    (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ) :
    0 ≤ localExpectation x (y.colorKernel hinj) (fun g => (LocalFormula.union g : ℝ)) := by
  have h := union_column_nonnegative y hinj (fun _ c => unionEvent c)
    (fun _ _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hδ hmin
  simpa only [localExpectation, oldSampleAverage, ← union_formula] using h

end Erdos809.Certificate
