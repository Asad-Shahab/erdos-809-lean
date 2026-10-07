module
public import Erdos809.Certificate.Marking

@[expose] public section

/-! Local support of the colored sampling law: a triangle containing an F
edge has probability zero when F edges have no common neighbor in the host.
This is independent of a local table's enumeration or coefficient formulas.
-/

namespace Erdos809.Certificate

variable {V : Type*} (G F : SimpleGraph V) (lambda : V → V → ℝ)

theorem markedProbability_nonzero_adj {u v : V} {c : Fin 4}
    (hprob : markedProbability G F lambda u v c ≠ 0) (hc : c ≠ 0) :
    G.Adj u v := by
  classical
  by_contra hG
  exact hprob (by simp [markedProbability, hG, hc])

theorem markedProbability_one_nonzero_F {u v : V}
    (hprob : markedProbability G F lambda u v 1 ≠ 0) : F.Adj u v := by
  classical
  by_contra hF
  by_cases hG : G.Adj u v <;> simp [markedProbability, hG, hF] at hprob

theorem forbidden_F_triangle_weight_zero
    (hfree : ∀ u v, F.Adj u v → ¬Walk2 G u v)
    (u v w : V) (c d : Fin 4) (hc : c ≠ 0) (hd : d ≠ 0) :
    markedProbability G F lambda u v 1 *
      markedProbability G F lambda u w c *
      markedProbability G F lambda v w d = 0 := by
  by_cases h₁ : markedProbability G F lambda u v 1 = 0
  · simp [h₁]
  by_cases h₂ : markedProbability G F lambda u w c = 0
  · simp [h₂]
  by_cases h₃ : markedProbability G F lambda v w d = 0
  · simp [h₃]
  exact False.elim (hfree u v (markedProbability_one_nonzero_F G F lambda h₁)
    ⟨w, markedProbability_nonzero_adj G F lambda h₂ hc,
      (markedProbability_nonzero_adj G F lambda h₃ hd).symm⟩)

end Erdos809.Certificate
