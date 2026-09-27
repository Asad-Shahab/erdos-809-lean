import Erdos809.PairCover
import Erdos809.PatternSectors
import Erdos809.Matching

/-! Extract one actual capacitated matching from any exact triangular-sector
cover. The resulting lower bound does not require choosing an LP optimizer. -/

namespace Erdos809

open Finset VertexWeights
open scoped BigOperators

variable {V E P : Type*} [Fintype V] [Fintype E] [Fintype P] [DecidableEq E]
variable (x : VertexWeights V) (G : SimpleGraph V) {δ : ℝ}
variable (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast G δ)
variable (u v : E → V) (htri : ∀ e, Triangular G (u e) (v e))
variable (edges : P → Finset E)
variable (hpattern : ∀ p, (edges p : Set E).Pairwise
  (fun e f => Compatible G (u e) (v e) (u f) (v f)))
variable (cover : ExactPatternCover (fun e => x.capacity (u e) (v e)) edges)

/-- The pair amount is the sum of the actual cover amounts of patterns
containing these two different edges. All compatibility is in the full host. -/
noncomputable def triangularCoverMatching : TriangularMatching G x E where
  left := u
  right := v
  triangular := htri
  amount := cover.pairAmount
  nonneg := cover.pairAmount_nonneg
  symmetric := cover.pairAmount_symmetric
  diagonal := cover.pairAmount_diagonal
  compatible := by
    intro e f hpos
    obtain ⟨p, he, hf, hef⟩ := cover.pairAmount_support hpos
    exact hpattern p he hf hef
  capacity := cover.pairAmount_capacity fun p =>
    triangular_pattern_card_le_two x G hδ hmin u v (edges p)
      (fun e _ => htri e) (hpattern p)

theorem triangularCoverMatching_cost_bound :
    (∑ e, x.capacity (u e) (v e)) -
      (triangularCoverMatching x G hδ hmin u v htri edges hpattern cover).value ≤
      cover.cost := by
  exact cover.pairAmount_cost_bound fun p =>
    triangular_pattern_card_le_two x G hδ hmin u v (edges p)
      (fun e _ => htri e) (hpattern p)

end Erdos809
