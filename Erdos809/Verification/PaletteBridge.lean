module

public import Erdos809.LongOddCycles.FinalInterface
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Exact correspondence with the finite palettes and rainbow copies used by FC. -/

@[expose] public section

namespace Erdos809.FormalConjecturesBridge

open SimpleGraph

/-- Mirrored verbatim from
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`.
The FC definition is not part of Mathlib 4.35. -/
def IsRainbow {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G)
    (c : G.EdgeLabeling K) : Prop :=
  Function.Injective (c.pullback f)

/-- Mirrored verbatim from `FormalConjectures/ErdosProblems/809.lean`. -/
noncomputable def strongChromaticNum {α : Type*} (H : SimpleGraph α) (n e : ℕ) : ℕ :=
  sInf {r | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
    ∃ c : G.EdgeLabeling (Fin r), ∀ f : H.Copy G, IsRainbow f.toHom c}

/-- Both predicates use the same edge map of a simple, non-induced copy. -/
theorem rainbow_iff {V K : Type*} {G : SimpleGraph V} {ℓ : ℕ}
    (c : G.EdgeLabeling K) :
    ValidCycleColoring ℓ c ↔ ∀ f : (cycleGraph ℓ).Copy G, IsRainbow f.toHom c :=
  Iff.rfl

/-- Compress precisely the used labels, including the empty palette case. -/
theorem palette_compression {V K : Type*} [Finite V] {G : SimpleGraph V} {ℓ r : ℕ}
    (c : G.edgeSet → K) (hc : ValidCycleColoring ℓ c) (hr : usedColors c = r) :
    ∃ d : G.EdgeLabeling (Fin r),
      (∀ f : (cycleGraph ℓ).Copy G, IsRainbow f.toHom d) ∧ Function.Surjective d := by
  classical
  let : Fintype (Set.range c) := Fintype.ofFinite _
  have hcard : Fintype.card (Set.range c) = r :=
    (Set.fintypeCard_eq_ncard _).trans hr
  let E : Set.range c ≃ Fin r := Fintype.equivFinOfCardEq hcard
  let d : G.EdgeLabeling (Fin r) := fun x ↦ E ⟨c x, Set.mem_range_self x⟩
  refine ⟨d, ?_, ?_⟩
  · intro f x y h
    apply hc f
    exact congrArg Subtype.val (E.injective h)
  · intro y
    obtain ⟨x, hx⟩ := (E.symm y).property
    refine ⟨x, ?_⟩
    change E ⟨c x, Set.mem_range_self x⟩ = y
    have he : (⟨c x, Set.mem_range_self x⟩ : Set.range c) = E.symm y :=
      Subtype.ext hx
    rw [he, E.apply_symm_apply]

/-- A finite nominal palette gives an arbitrary-palette coloring with at most r labels. -/
theorem finite_palette {V : Type*} {G : SimpleGraph V} {ℓ r : ℕ}
    (c : G.EdgeLabeling (Fin r))
    (hc : ∀ f : (cycleGraph ℓ).Copy G, IsRainbow f.toHom c) :
    ValidCycleColoring ℓ c ∧ usedColors c ≤ r := by
  refine ⟨(rainbow_iff c).mpr hc, ?_⟩
  simpa using usedColors_le_card c

/-- The attained at-least-e minimum is also the least exact-e finite palette.
Exact realization uses deletion of edges, with minimality forcing preservation
of the used-color count. Membership explicitly excludes the empty-sInf trap. -/
theorem exact_palette_minimum {ℓ n e q : ℕ} (hq : CycleExtremalValue ℓ n e q) :
    IsLeast {r | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
      ∃ c : G.EdgeLabeling (Fin r), ∀ f : (cycleGraph ℓ).Copy G, IsRainbow f.toHom c} q := by
  constructor
  · obtain ⟨G, K, c, he, hc, hcolors⟩ := cycleExtremalValue_realized_exactly hq
    obtain ⟨d, hd, _⟩ := palette_compression c hc hcolors
    exact ⟨G, he, d, hd⟩
  · rintro r ⟨G, he, c, hc⟩
    obtain ⟨hv, hr⟩ := finite_palette c hc
    exact (hq.2 ⟨G, Fin r, c, he.ge, hv, rfl⟩).trans hr

theorem strongChromaticNum_eq {ℓ n e q : ℕ} (hq : CycleExtremalValue ℓ n e q) :
    strongChromaticNum (cycleGraph ℓ) n e = q :=
  (exact_palette_minimum hq).csInf_eq

theorem threshold_eq (n : ℕ) : n ^ 2 / 4 + 1 = exactThreshold n := by
  simp only [exactThreshold, pow_two]

end Erdos809.FormalConjecturesBridge
