module
public import Erdos809.Main
public import Erdos809.LongOddCycles.Main

@[expose] public section

/-! Unify the preserved C7 theorem and the formalized published longer-cycle
cases. This is a split on k=3; it uses no monotonicity in cycle length. -/
namespace Erdos809

/-- Erdős #809 for every fixed odd cycle C₂ₖ₊₁ with k≥3. The actual minimum
over all hosts having at least floor(n²/4)+1 edges is attained, and has both
asymptotic bounds for every sufficiently large integer n. -/
theorem erdos_809 (k : ℕ) (hk : 3 ≤ k) :
    CycleAsymptoticExtremalValue (2 * k + 1) := by
  by_cases h : k = 3
  · subst k
    exact erdos_809_C7
  · exact erdos_809_long_odd_cycles k (by omega)

/-- Universal-host lower and existential-host upper bounds for the unified
odd-cycle theorem. Both count the image of the actual coloring. -/
theorem erdos_809_bounds (k : ℕ) (hk : 3 ≤ k) :
    CycleAsymptoticTheorem (2 * k + 1) := by
  by_cases h : k = 3
  · subst k
    exact erdos_809_C7_bounds
  · exact erdos_809_long_odd_cycles_bounds k (by omega)

/-- The unified universal lower bound, exposed separately from minimization. -/
theorem erdos_809_lower (k : ℕ) (hk : 3 ≤ k) :
    CycleAsymptoticLowerBound (2 * k + 1) :=
  (cycleAsymptoticTheorem_iff.mp (erdos_809_bounds k hk)).1

/-- The unified upper bound supplies an actual host and coloring at every
sufficiently large integer order. -/
theorem erdos_809_upper (k : ℕ) (hk : 3 ≤ k) :
    CycleAsymptoticUpperBound (2 * k + 1) :=
  (cycleAsymptoticTheorem_iff.mp (erdos_809_bounds k hk)).2

/-- Every attained generic minimum has an exact-edge realization. -/
theorem erdos_809_realized_exactly (k : ℕ) (n e q : ℕ)
    (hq : CycleExtremalValue (2 * k + 1) n e q) :
    ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      EdgeCount G = e ∧ ValidCycleColoring (2 * k + 1) c ∧ usedColors c = q :=
  cycleExtremalValue_realized_exactly hq

end Erdos809
