module
public import Erdos809.Certificate.GramColumns
public import Erdos809.Certificate.ConstraintColumns
public import Erdos809.Certificate.MatchingExpectation
public import Erdos809.Certificate.LocalFormulaReflection
public import Erdos809.WeightedCP

@[expose] public section

/-! Complete graph interpretation of the finite local certificate. Only the
explicit exhaustive coverage and concrete row-check premises remain below;
all sampling, Gram, constraint and normalization arguments are proved here. -/

namespace Erdos809.Certificate

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)
  (hinj : Function.Injective (fun i => s(y.left i, y.right i)))

include hinj in
theorem matching_polynomial_of_local_deficits
    (hlocal : ∀ g : LocalGraph, g.Admissible → 0 ≤ LocalFormula.symmetrizedDeficit g)
    {δ ξ : ℝ} (hδ : 1 / 3 ≤ δ) (hmin : x.MinDegreeAtLeast G δ)
    (hξ : 0 ≤ ξ) (hdensity : 1 / 4 - ξ ≤ x.edgeMass G) :
    -ξ ≤ y.polynomial := by
  apply polynomial_bound_of_symmetrized_certificate y hinj Coefficients.scale ξ
    (Nat.cast_pos.mpr Coefficients.scale_positive) (fun g => (LocalFormula.rhs g : ℝ))
  · intro g hg
    have h : (0 : ℝ) ≤ (LocalFormula.symmetrizedDeficit g : ℝ) := by
      exact_mod_cast hlocal g hg
    simpa only [LocalFormula.symmetrizedDeficit, LocalFormula.deficit,
      Int.cast_sum, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      LocalFormula.target_cast] using h
  · have hrootGram := local_rootGram_nonnegative x (y.colorKernel hinj)
    have htypeGram := local_typeGram_nonnegative x (y.colorKernel hinj)
    have hd := local_density_lower_bound y hinj hξ hdensity
    have hdegree := local_degree_nonnegative y hinj hδ hmin
    have hroot := local_root_nonnegative y hinj
    have hunion := local_union_nonnegative y hinj hδ hmin
    simp only [LocalFormula.rhs, Int.cast_add, localExpectation_add]
    linarith

/-- The sole remaining premises are the finite kernel-checking tasks. The
complete mathematical implication to the exact stable polynomial proposition
has no additional certificate-soundness or graph-model assumptions. -/
theorem stableMatchingPolynomial_of_finite_certificate
    (hrows : ∀ r, LocalFormula.representativeCheck r = true)
    (hcover : ∀ g : LocalGraph, g.Admissible →
      ∃ (r : Fin 1436) (σ : Equiv.Perm (Fin 5)),
        g = (LocalGraph.Data.representatives r).relabel σ) :
    StableMatchingPolynomial := by
  intro V E instV instEq instE G instG x _ δ ξ hδ hmin hξ hdensity y hinj
  exact matching_polynomial_of_local_deficits y hinj
    (LocalFormula.admissible_deficit_nonnegative hrows hcover) hδ.le hmin hξ hdensity

end Erdos809.Certificate
