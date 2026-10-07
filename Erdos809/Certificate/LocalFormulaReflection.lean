module
public import Erdos809.Certificate.LocalFormula
public import Erdos809.Certificate.LocalGraphsData

@[expose] public section

/-! Reduce the symmetrized local certificate to the explicitly ordered orbit
representatives. The checked permutation equivalence supplies all 120 orders.
Concrete row checks and exhaustive graph coverage are independent premises.
-/

namespace Erdos809.Certificate.LocalFormula

noncomputable def tableDeficit (g : LocalGraph) : ℤ :=
  ∑ p : Fin 120, deficit (g.relabel (LocalGraph.Data.permutations p))

theorem tableDeficit_eq (g : LocalGraph) : tableDeficit g = symmetrizedDeficit g :=
  Fintype.sum_equiv LocalGraph.Data.permutationEquiv _ _ (fun _ => rfl)

noncomputable def representativeCheck (r : Fin 1436) : Bool :=
  decide (0 ≤ tableDeficit (LocalGraph.Data.representatives r))

theorem representativeCheck_sound (r : Fin 1436) (h : representativeCheck r = true) :
    0 ≤ symmetrizedDeficit (LocalGraph.Data.representatives r) := by
  rw [← tableDeficit_eq]
  exact of_decide_eq_true h

theorem admissible_deficit_nonnegative
    (hrows : ∀ r, representativeCheck r = true)
    (hcover : ∀ g : LocalGraph, g.Admissible →
      ∃ (r : Fin 1436) (σ : Equiv.Perm (Fin 5)),
        g = (LocalGraph.Data.representatives r).relabel σ)
    (g : LocalGraph) (hg : g.Admissible) : 0 ≤ symmetrizedDeficit g := by
  obtain ⟨r, σ, rfl⟩ := hcover g hg
  rw [symmetrizedDeficit_relabel]
  exact representativeCheck_sound r (hrows r)

end Erdos809.Certificate.LocalFormula
