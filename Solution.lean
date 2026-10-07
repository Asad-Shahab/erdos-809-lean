module

public import Erdos809

/-! Palomar interface to the original proof. No mathematical hypothesis is added.
The statement is expanded to match the independent Mathlib-only Challenge. -/

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
  exact Erdos809.erdos_809 k hk

end Erdos809Palomar
