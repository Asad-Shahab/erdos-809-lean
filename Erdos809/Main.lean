import Erdos809.Certificate.PolynomialCertificate
import Erdos809.Certificate.LocalGraphsCoverage
import Erdos809.Certificate.SemanticRows
import Erdos809.FiniteCP
import Erdos809.FinalInterface

/-! The complete certificate-to-Erdős-809 chain. Concrete, kernel-checked
finite lemmas discharge both premises of the semantic certificate theorem.
The public asymptotic statement concerns the attained minimum over all hosts
and all valid colorings, counting only colors actually used. -/

namespace Erdos809

theorem stableMatchingPolynomial : StableMatchingPolynomial := by
  apply Certificate.stableMatchingPolynomial_of_finite_certificate
    Certificate.LocalFormula.SemanticRows.allRows_valid
  intro g hg
  obtain ⟨r, p, h⟩ := Certificate.LocalGraph.every_admissible_is_representative g hg
  exact ⟨r, Certificate.LocalGraph.Data.permutations p, h.symm⟩

theorem weightedFiniteCP : WeightedFiniteCP :=
  weightedFiniteCP_of_matchingPolynomial stableMatchingPolynomial

theorem weightedStableCP : Source.WeightedStableCP :=
  weightedStableCP_of_matchingPolynomial stableMatchingPolynomial

theorem asymptoticLowerBound : AsymptoticLowerBound :=
  asymptoticLowerBound_of_matchingPolynomial stableMatchingPolynomial

/-- The exact-threshold universal lower bound and existential upper bound,
uniformly for every sufficiently large integer. -/
theorem erdos_809_C7_bounds : AsymptoticTheorem :=
  asymptoticTheorem_of_matchingPolynomial stableMatchingPolynomial

/-- Erdős #809 for C₇: the actual host-minimized rainbow-C₇ color count is
`(1/8 + o(1)) n²`, in its two-sided epsilon formulation. The natural-number
threshold is exactly `floor(n²/4) + 1`; cycles are simple and need not be induced.
The minimum is attained on an exact-edge host by `extremalValue_realized_exactly`.
-/
theorem erdos_809_C7 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∃ k, ExtremalValue n (exactThreshold n) k ∧
        (1 / 8 - ε) * (n : ℝ)^2 ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (1 / 8 + ε) * (n : ℝ)^2 :=
  asymptoticExtremalValue_of_matchingPolynomial stableMatchingPolynomial

end Erdos809
