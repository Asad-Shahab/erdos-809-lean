/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Patterns
import Erdos809.Triangular

/-! Finite whole-pattern consequences of the full-host sector geometry. -/

namespace Erdos809

open Finset VertexWeights

variable {V E : Type*} [Fintype V] (x : VertexWeights V) (G : SimpleGraph V)

/-- A whole compatible pattern containing one triangular edge consists entirely
of triangular edges. Endpoints and compatibility refer to the unchanged host. -/
theorem pattern_triangular_of_mem {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u v : E → V) (s : Finset E)
    (hedge : ∀ e ∈ s, G.Adj (u e) (v e))
    (hpattern : (s : Set E).Pairwise
      (fun e f => Compatible G (u e) (v e) (u f) (v f)))
    {e : E} (he : e ∈ s) (heT : Triangular G (u e) (v e)) :
    ∀ f ∈ s, Triangular G (u f) (v f) := by
  intro f hf
  by_cases hef : e = f
  · simpa only [hef] using heT
  refine ⟨hedge f hf, ?_⟩
  by_contra hfF
  exact compatible_no_mixed_sectors x G hδ hmin (hpattern he hf hef)
    heT (hedge f hf) hfF

/-- A triangular pattern has at most two distinct edge indices. This turns
the geometric triple obstruction into the finite cover-to-matching bound. -/
theorem triangular_pattern_card_le_two {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u v : E → V) (s : Finset E)
    (htri : ∀ e ∈ s, Triangular G (u e) (v e))
    (hpattern : (s : Set E).Pairwise
      (fun e f => Compatible G (u e) (v e) (u f) (v f))) : s.card ≤ 2 := by
  by_contra hn
  obtain ⟨e, f, g, he, hf, hg, hef, heg, hfg⟩ :=
    two_lt_card_iff.mp (lt_of_not_ge hn)
  exact compatible_triple_not_triangular x G hδ hmin
    (hpattern he hf hef) (hpattern he hg heg) (hpattern hf hg hfg)
    (htri e he).1 (htri f hf).1 (htri g hg).1 (htri e he).2

end Erdos809
