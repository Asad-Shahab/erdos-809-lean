import Erdos809.UpperBound
import Erdos809.WeightedCP

/-! Final theorem interfaces, including attainment on an exact-edge host.
The certificate-dependent theorems below retain their explicit polynomial
premise until the concrete finite checks have been integrated. -/

namespace Erdos809

/-- An attained host-minimized value is attained by a host with exactly the
prescribed edge count, with all original vertices retained. -/
theorem extremalValue_realized_exactly {n e k : ℕ} (hk : ExtremalValue n e k) :
    ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      EdgeCount G = e ∧ ValidC7Coloring c ∧ usedColors c = k := by
  obtain ⟨G, K, c, he, hc, hck⟩ := hk.1
  obtain ⟨H, hHG, hH⟩ := exists_subgraph_edgeCount_eq G he
  let d : H.edgeSet → K := c ∘ (SimpleGraph.Copy.ofLE H G hHG).mapEdgeSet
  have hd : ValidC7Coloring d := hc.restrict hHG
  have hdk : usedColors d ≤ k := by
    simpa only [hck] using usedColors_comap_le c (SimpleGraph.Copy.ofLE H G hHG)
  have ha : AttainableColorCount n e (usedColors d) := ⟨H, K, d, hH.ge, hd, rfl⟩
  exact ⟨H, K, d, hH, hd, Nat.le_antisymm hdk (hk.2 ha)⟩

theorem asymptoticTheorem_of_matchingPolynomial (hpoly : StableMatchingPolynomial) :
    AsymptoticTheorem :=
  asymptoticTheorem_iff.mpr
    ⟨asymptoticLowerBound_of_matchingPolynomial hpoly, asymptoticUpperBound⟩

/-- The epsilon conclusion for the actual attained minimum over all eligible
hosts and all valid colorings, rather than an ambient color-type size. -/
theorem asymptoticExtremalValue_of_matchingPolynomial (hpoly : StableMatchingPolynomial) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∃ k, ExtremalValue n (exactThreshold n) k ∧
        (1 / 8 - ε) * (n : ℝ)^2 ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (1 / 8 + ε) * (n : ℝ)^2 := by
  intro ε hε
  obtain ⟨N, hN⟩ := asymptoticTheorem_of_matchingPolynomial hpoly ε hε
  exact ⟨N, fun n hn => extremalValue_bounds_of_lower_upper (hN n hn).1 (hN n hn).2⟩

end Erdos809
