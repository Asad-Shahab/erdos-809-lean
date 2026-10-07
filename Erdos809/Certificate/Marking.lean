module
public import Erdos809.Certificate.Sampling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! The four-color law on a marked host. The marked sector is the part of G
outside F. In the application F must be the nontriangular sector and the mark
probabilities must come from one actual matching; those identifications are
not assumed or concluded here. -/

namespace Erdos809.Certificate

variable {V : Type*}

noncomputable def markedProbability (G F : SimpleGraph V) (lambda : V → V → ℝ)
    (u v : V) (c : Fin 4) : ℝ := by
  classical
  exact if ¬G.Adj u v then (if c = 0 then 1 else 0)
    else if F.Adj u v then (if c = 1 then 1 else 0)
    else if c = 2 then 1 - lambda u v else if c = 3 then lambda u v else 0

noncomputable def markedHostKernel (G F : SimpleGraph V) (lambda : V → V → ℝ)
    (hlower : ∀ u v, 0 ≤ lambda u v) (hupper : ∀ u v, lambda u v ≤ 1) :
    ColorKernel V where
  prob := markedProbability G F lambda
  nonneg := by
    intro u v c
    classical
    unfold markedProbability
    split_ifs <;> first
      | exact sub_nonneg.mpr (hupper u v)
      | exact hlower u v
      | norm_num
  total := by
    intro u v
    classical
    by_cases hG : G.Adj u v <;> by_cases hF : F.Adj u v <;>
      simp [markedProbability, hG, hF, Fin.sum_univ_succ]

theorem markedProbability_symm (G F : SimpleGraph V) (lambda : V → V → ℝ)
    (hsymm : ∀ u v, lambda u v = lambda v u) (u v : V) (c : Fin 4) :
    markedProbability G F lambda u v c = markedProbability G F lambda v u c := by
  classical
  simp only [markedProbability, G.adj_comm v u, F.adj_comm v u, hsymm v u]

theorem markedProbability_diagonal (G F : SimpleGraph V) (lambda : V → V → ℝ)
    (u : V) (c : Fin 4) :
    markedProbability G F lambda u u c = if c = 0 then 1 else 0 := by
  simp [markedProbability]

open Classical in
theorem markedProbability_F (G F : SimpleGraph V) (hFG : F ≤ G)
    (lambda : V → V → ℝ) (u v : V) :
    markedProbability G F lambda u v 1 = if F.Adj u v then 1 else 0 := by
  classical
  by_cases hG : G.Adj u v <;> by_cases hF : F.Adj u v
  all_goals first
    | exact False.elim (hG (hFG hF))
    | simp [markedProbability, hG, hF]

end Erdos809.Certificate
