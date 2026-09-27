import Erdos809.Certificate.LinkedMatrices
import Erdos809.Certificate.LocalGraphs
import Erdos809.Certificate.TargetExpectation

/-! Exact ordered local formulas for the certificate. The integer numerator
uses the actual PSD matrix entries and total finite flag classifiers. Its
symmetrization can be checked on orbit representatives. The sampling meaning
and signs of the different terms are proved separately.
-/

namespace Erdos809.Certificate.LocalFormula

open FlagData LinkedMatrices

def edge (c : Fin 4) : ℤ := if c = 0 then 0 else 1
def triangular (c : Fin 4) : ℤ := if c = 2 ∨ c = 3 then 1 else 0
def nontriangular (c : Fin 4) : ℤ := if c = 1 then 1 else 0
def selected (c : Fin 4) : ℤ := if c = 3 then 1 else 0

def triangle (g : LocalGraph) : ℤ :=
  edge (g (targetPair 0)) * edge (g (targetPair 1)) * edge (g (targetPair 2))

def target (g : LocalGraph) : ℤ :=
  4 * (triangle g * triangular (g (targetPair 3)) * nontriangular (g (targetPair 4))) +
    triangle g * 1 * 1 - triangle g * 1 * edge (g (targetPair 4)) -
    2 * (triangle g * 1 * nontriangular (g (targetPair 4))) -
    triangle g * 1 * selected (g (targetPair 4))

theorem target_cast (g : LocalGraph) : (target g : ℝ) = orderedTarget g := by
  simp [target, orderedTarget, triangle, coloredTriangle, edge, edgeFlag,
    triangular, triangularFlag, nontriangular, nontriangularFlag, selected, selectedFlag]

noncomputable def rootAt (g : LocalGraph) (i j k : Fin 5) : Fin 28 :=
  rootFlag (g.color i j) (g.color i k) (g.color j k)

noncomputable def typeAt (g : LocalGraph) : Fin 14 :=
  tripleType (g.color 0 1) (g.color 0 2) (g.color 1 2)

noncomputable def degreeAt (g : LocalGraph) : Fin 294 :=
  degreeFlag (g.color 0 1) (g.color 0 2) (g.color 0 3)
    (g.color 1 2) (g.color 1 3) (g.color 2 3)

noncomputable def unionAt (g : LocalGraph) : Fin 190 :=
  unionFlag (g.color 0 1) (g.color 0 2) (g.color 0 3)
    (g.color 1 2) (g.color 1 3) (g.color 2 3)

noncomputable def literalRoot (g : LocalGraph) (t : Fin 14) : Prop :=
  g.color 0 1 = literalType t 0 ∧ g.color 0 2 = literalType t 1 ∧
    g.color 1 2 = literalType t 2

noncomputable instance (g : LocalGraph) (t : Fin 14) : Decidable (literalRoot g t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

noncomputable def attachmentAt (g : LocalGraph) (t : Fin 14) (k : Fin 5) :
    Fin (typeSize t) := attachment t (g.color 0 k) (g.color 1 k) (g.color 2 k)

noncomputable def rootGram (g : LocalGraph) : ℤ :=
  4 * rootNumerator (rootAt g 0 1 2) (rootAt g 0 3 4)

noncomputable def typeGram (g : LocalGraph) : ℤ :=
  4 * ∑ t, if literalRoot g t then
    typeNumerator t (attachmentAt g t 3) (attachmentAt g t 4) else 0

noncomputable def density (g : LocalGraph) : ℤ :=
  (densityNumerator (typeAt g) : ℤ) * (2 * edge (g.color 3 4) - 1)

noncomputable def degree (g : LocalGraph) : ℤ :=
  ((4 * degreeNumerator (degreeAt g) / 3 : ℕ) : ℤ) *
    (3 * edge (g.color 0 4) - 1)

noncomputable def root (g : LocalGraph) : ℤ :=
  2 * (selected_rootNumerator (rootAt g 0 3 4) : ℤ) *
    selected (g.color 1 2) * (1 - edge (g.color 0 1) - edge (g.color 0 2))

noncomputable def union (g : LocalGraph) : ℤ :=
  ((4 * unionNumerator (unionAt g) / 3 : ℕ) : ℤ) * selected (g.color 0 1) *
    (2 - 3 * if g.color 0 4 ≠ 0 ∨ g.color 1 4 ≠ 0 then (1 : ℤ) else 0)

noncomputable def rhs (g : LocalGraph) : ℤ :=
  rootGram g + typeGram g + density g + degree g + root g + union g

noncomputable def deficit (g : LocalGraph) : ℤ :=
  target g * Coefficients.scale - rhs g

noncomputable def symmetrizedDeficit (g : LocalGraph) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 5), deficit (g.relabel σ)

theorem symmetrizedDeficit_relabel (g : LocalGraph) (τ : Equiv.Perm (Fin 5)) :
    symmetrizedDeficit (g.relabel τ) = symmetrizedDeficit g := by
  simp only [symmetrizedDeficit, LocalGraph.relabel_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

end Erdos809.Certificate.LocalFormula
