module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 809: the attained odd-cycle threshold

For each fixed integer k >= 3, consider all simple n-vertex graphs with at
least floor(n^2/4) + 1 edges, and all edge colorings in which every copy of
the (2k+1)-cycle is rainbow. The least number of colors actually used is
(1/8 + o(1)) n^2. The cutoff N may depend on k and epsilon, but not on the
host graph or its coloring.

`SimpleGraph.Copy` is injective and adjacency-preserving, not necessarily
induced. `Nat.card G.edgeSet` counts unordered edges, and `(Set.range c).ncard`
counts used colors rather than the size of the nominal palette. The `IsLeast`
clause includes attainment, so no default value is assigned to an empty set.
All definitions appearing in the statement come from Mathlib or Lean core.

This is Corollary 1.2 of Asad Shahab, arXiv:2609.38286v1. The k=3 case is
the paper's seven-cycle result (Theorem 1.1). For k>=4, the development
formalizes the argument of Bucić, Chen, and Ma, arXiv:2603.18952v1.
It does not assert a full-density formula for seven-cycles or claim priority
over the independently registered PALOMAR-2026-09-30-000004 v1.

The only deliberate proof hole is the Challenge theorem. Solution.lean has
the identical statement and obtains its proof from the existing development.
-/

public section

namespace Erdos809Palomar

/-- The minimum over all eligible hosts and rainbow-cycle colorings is attained
and lies within epsilon times n squared of n squared divided by eight. -/
theorem main_result (k : ℕ) (hk : 3 ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∃ q : ℕ,
        IsLeast
          {r : ℕ | ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
            n * n / 4 + 1 ≤ Nat.card G.edgeSet ∧
            (∀ F : SimpleGraph.Copy (SimpleGraph.cycleGraph (2 * k + 1)) G,
              Function.Injective (c ∘ F.mapEdgeSet)) ∧
            (Set.range c).ncard = r} q ∧
        (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (q : ℝ) ∧
        (q : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2 := by
  sorry

end Erdos809Palomar
