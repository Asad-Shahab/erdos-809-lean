module
public import Erdos809.WeightedCP

@[expose] public section

/-! The strict-density finite CP theorem for every exact whole-pattern cover
of the actual outside sector. Its only certificate premise is the explicit
stable matching polynomial proposition. Taking the minimum over these covers
gives the manuscript's finite CP statement without requiring an optimizer.
-/

namespace Erdos809

open VertexWeights

/-- The finite CP conclusion on all exact outside-sector pattern covers.
Compatibility, capacities and sectors refer to the same full host. The strict
edge-mass premise excludes the balanced complete bipartite boundary case. -/
def WeightedFiniteCP : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : VertexWeights V),
    (∀ v, 0 < x.weight v) →
    ∀ δ : ℝ, 1 / 3 < δ → x.MinDegreeAtLeast G δ →
      1 / 4 < x.edgeMass G →
      ∀ (P : Type) [Fintype P] (edges : P → Finset (outsideSector G).edgeSet),
        (∀ p, (edges p : Set (outsideSector G).edgeSet).Pairwise
          (fun e f => Compatible G
            (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)
            (edgeLeft (outsideSector G) f) (edgeRight (outsideSector G) f))) →
        ∀ cover : ExactPatternCover
          (fun e : (outsideSector G).edgeSet =>
            x.capacity (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)) edges,
          3 * x.edgeMass G / 2 - 1 / 4 ≤ cover.cost

/-- Finite CP follows from the same-matching certificate at zero density
error. No cut-deficit hypothesis or positive-deficit case split is needed. -/
theorem weightedFiniteCP_of_matchingPolynomial (hpoly : StableMatchingPolynomial) :
    WeightedFiniteCP := by
  classical
  intro V instV instEq G instG x hx δ hδ hmin hdensity P instP edges hpattern cover
  cases Subsingleton.elim instEq (Classical.decEq V)
  obtain ⟨y, PT, PF, hinj, _, _, hcost, ht, hf⟩ :=
    outsideCover_decomposition G x hδ hmin edges hpattern cover
  have hp := hpoly V (OutsideTriangularEdge G) G x hx δ 0 hδ hmin (by norm_num)
    (by linarith) y hinj
  apply y.palette_bound_of_polynomial (x.triangleMass_pos_of_superquarter G hdensity) hf
    (by simpa using hp)
  have hm := x.edgeMass_triangular_add_nontriangular G
  linarith

end Erdos809
