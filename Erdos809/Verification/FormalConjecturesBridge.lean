module

public import Erdos809.OddCycles
public import Erdos809.Verification.AsymptoticBridge

/-! Checked versions of the three FC formal-proof claims. Each result applies
the generic bridge to its own source declaration, rather than substituting the
unified theorem for either of the two historical component claims. -/

@[expose] public section

namespace Erdos809.FormalConjecturesBridge

open SimpleGraph Filter Asymptotics

theorem full : ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 :=
  fun k hk ↦ asymptotic_bridge (Erdos809.erdos_809 k hk)

theorem bcm : ∀ k, 4 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 :=
  fun k hk ↦ asymptotic_bridge (Erdos809.erdos_809_long_odd_cycles k hk)

theorem c7 :
    (fun n ↦ (strongChromaticNum (cycleGraph 7) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := by
  apply asymptotic_bridge
  intro ε hε
  obtain ⟨N, hN⟩ := Erdos809.erdos_809_C7 ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨q, hq, hl, hu⟩ := hN n hn
  exact ⟨q, cycleExtremalValue_seven_iff.mpr hq, hl, hu⟩

/-- FC's `answer(True)` wrapper reduces to True. No answer implementation is imported. -/
theorem full_true_iff : True ↔ ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 :=
  ⟨fun _ ↦ full, fun _ ↦ True.intro⟩

-- The following propositions copy the substantive FC statement text exactly,
-- replacing only `answer(True)` with True and using the mirrored definitions.
example : True ↔ ∀ k, 3 ≤ k →
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := full_true_iff

example (k : ℕ) (hk : 4 ≤ k) :
    (fun n ↦ (strongChromaticNum (cycleGraph (2 * k + 1)) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := bcm k hk

example :
    (fun n ↦ (strongChromaticNum (cycleGraph 7) n (n ^ 2 / 4 + 1) : ℝ)) ~[atTop]
      fun n ↦ (n : ℝ) ^ 2 / 8 := c7

end Erdos809.FormalConjecturesBridge
