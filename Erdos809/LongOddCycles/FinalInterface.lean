module
public import Erdos809.LongOddCycles.UpperBound

@[expose] public section

namespace Erdos809

/-- An attained host-minimized value is attained by a host with exactly the
prescribed edge count, with all original vertices retained. -/
theorem cycleExtremalValue_realized_exactly {ℓ n e k : ℕ} (hk : CycleExtremalValue ℓ n e k) :
    ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      EdgeCount G = e ∧ ValidCycleColoring ℓ c ∧ usedColors c = k := by
  obtain ⟨G, K, c, he, hc, hck⟩ := hk.1
  obtain ⟨H, hHG, hH⟩ := exists_subgraph_edgeCount_eq G he
  let d : H.edgeSet → K := c ∘ (SimpleGraph.Copy.ofLE H G hHG).mapEdgeSet
  have hd : ValidCycleColoring ℓ d := hc.restrict hHG
  have hdk : usedColors d ≤ k := by
    simpa only [hck] using usedColors_comap_le c (SimpleGraph.Copy.ofLE H G hHG)
  have ha : CycleAttainableColorCount ℓ n e (usedColors d) := ⟨H, K, d, hH.ge, hd, rfl⟩
  exact ⟨H, K, d, hH, hd, Nat.le_antisymm hdk (hk.2 ha)⟩

/-- Combine universal lower and constructive upper estimates into the actual
attained minimum. The hypothesis is explicit; this is only a packaging lemma. -/
theorem cycleAsymptoticExtremalValue_of_lower {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hl : CycleAsymptoticLowerBound ℓ) : CycleAsymptoticExtremalValue ℓ := by
  intro ε hε
  obtain ⟨L, hL⟩ := hl ε hε
  obtain ⟨U, hU⟩ := cycle_asymptoticUpperBound hℓ ε hε
  refine ⟨max L U, fun n hn => ?_⟩
  exact cycleExtremalValue_bounds_of_lower_upper
    (hL n ((le_max_left _ _).trans hn)) (hU n ((le_max_right _ _).trans hn))

end Erdos809
