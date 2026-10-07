module
public import Erdos809.OutsideCover
public import Erdos809.WeightedPolynomial
public import Erdos809.Source.LowerAssembly

@[expose] public section

/-! The finite graph and source architecture reduced to one explicit stable
polynomial certificate obligation. No axiom asserts that obligation here. -/

namespace Erdos809

open VertexWeights

/-- The remaining graph interpretation of the exact certificate. The same
actual matching supplies its mass, marks, root constraints and union bounds. -/
def StableMatchingPolynomial : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : VertexWeights V),
    (∀ v, 0 < x.weight v) →
    ∀ δ ξ : ℝ, 1 / 3 < δ → x.MinDegreeAtLeast G δ →
      0 ≤ ξ → 1 / 4 - ξ ≤ x.edgeMass G →
      ∀ y : TriangularMatching G x E,
        Function.Injective (fun e => s(y.left e, y.right e)) → -ξ ≤ y.polynomial

theorem weightedStableCP_of_matchingPolynomial (hpoly : StableMatchingPolynomial) :
    Source.WeightedStableCP := by
  classical
  intro V instV instEq G instG x hx δ ξ ρ hδ hmin hξ hρ hsmall hdensity hdeficit
    P instP edges hpattern cover
  cases Subsingleton.elim instEq (Classical.decEq V)
  obtain ⟨y, PT, PF, hinj, _, _, hcost, ht, hf⟩ :=
    outsideCover_decomposition G x hδ hmin edges hpattern cover
  have hp := hpoly V (OutsideTriangularEdge G) G x hx δ ξ hδ hmin hξ hdensity y hinj
  apply y.stable_palette_bound_of_polynomial hξ hρ hsmall hdensity hdeficit hf hp
  have hm := x.edgeMass_triangular_add_nontriangular G
  linarith

/-- The complete source implication, still explicitly conditional on the
remaining certificate interpretation. -/
theorem asymptoticLowerBound_of_matchingPolynomial (hpoly : StableMatchingPolynomial) :
    AsymptoticLowerBound :=
  Source.asymptoticLowerBound_of_weightedStableCP
    (weightedStableCP_of_matchingPolynomial hpoly)

end Erdos809
