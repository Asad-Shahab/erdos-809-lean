module
public import Erdos809.Definitions

@[expose] public section

/-! Generic simple, non-induced cycle coloring semantics. These parallel the
completed C7 definitions and retain arbitrary palettes and host minimization. -/
namespace Erdos809
open SimpleGraph

abbrev CycleCopy {V : Type*} (ℓ : ℕ) (G : SimpleGraph V) :=
  Copy (cycleGraph ℓ) G

def ValidCycleColoring {V K : Type*} {G : SimpleGraph V}
    (ℓ : ℕ) (c : G.edgeSet → K) : Prop :=
  ∀ F : CycleCopy ℓ G, Function.Injective (c ∘ F.mapEdgeSet)

variable {ℓ : ℕ}

def CycleLowerBoundAt (ℓ : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
    exactThreshold n ≤ EdgeCount G → ValidCycleColoring ℓ c →
      (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (usedColors c : ℝ)

/-- Existential finite upper bound, with labels in an unrestricted countable set. -/
def CycleUpperBoundAt (ℓ : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (c : G.edgeSet → ℕ),
    exactThreshold n ≤ EdgeCount G ∧ ValidCycleColoring ℓ c ∧
      (usedColors c : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2

/-- All sufficiently large integers, with the cutoff independent of host and coloring. -/
def CycleAsymptoticLowerBound (ℓ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, CycleLowerBoundAt ℓ ε n

/-- All sufficiently large integers, not only a selected subsequence. -/
def CycleAsymptoticUpperBound (ℓ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, CycleUpperBoundAt ℓ ε n

/-- The two-sided exact-threshold target, in universal/existential epsilon form. -/
def CycleAsymptoticTheorem (ℓ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, CycleLowerBoundAt ℓ ε n ∧ CycleUpperBoundAt ℓ ε n

theorem cycleAsymptoticTheorem_iff :
    CycleAsymptoticTheorem ℓ ↔ CycleAsymptoticLowerBound ℓ ∧ CycleAsymptoticUpperBound ℓ := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun n hn ↦ (hN n hn).1⟩
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun n hn ↦ (hN n hn).2⟩
  · rintro ⟨hl, hu⟩ ε hε
    obtain ⟨L, hL⟩ := hl ε hε
    obtain ⟨U, hU⟩ := hu ε hε
    exact ⟨max L U, fun n hn ↦
      ⟨hL n ((le_max_left _ _).trans hn), hU n ((le_max_right _ _).trans hn)⟩⟩

theorem ValidCycleColoring.of_injective {V K : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} (hc : Function.Injective c) : ValidCycleColoring ℓ c :=
  fun F ↦ hc.comp F.mapEdgeSet.injective

/-- Validity restricts along any injective graph homomorphism. -/
theorem ValidCycleColoring.comap {V W K : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {c : G.edgeSet → K} (hc : ValidCycleColoring ℓ c)
    (F : Copy H G) : ValidCycleColoring ℓ (c ∘ F.mapEdgeSet) := by
  intro C x y h
  apply hc (F.comp C)
  have hm (e : (cycleGraph ℓ).edgeSet) :
      (F.comp C).mapEdgeSet e = F.mapEdgeSet (C.mapEdgeSet e) := by
    apply Subtype.ext
    exact (Sym2.map_map (g := F.toHom) (f := C.toHom) e.val).symm
  simpa only [Function.comp_apply, hm] using h

theorem ValidCycleColoring.restrict {V K : Type*} {G H : SimpleGraph V}
    {c : G.edgeSet → K} (hc : ValidCycleColoring ℓ c) (hHG : H ≤ G) :
    ValidCycleColoring ℓ (c ∘ (Copy.ofLE H G hHG).mapEdgeSet) := hc.comap _

theorem ValidCycleColoring.postcomp {V K L : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} (hc : ValidCycleColoring ℓ c) {f : K → L}
    (hf : Function.Injective f) : ValidCycleColoring ℓ (f ∘ c) :=
  fun F ↦ hf.comp (hc F)

def CycleAttainableColorCount (ℓ : ℕ) (n e k : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
    e ≤ EdgeCount G ∧ ValidCycleColoring ℓ c ∧ usedColors c = k

/-- The canonical host-minimized value, expressed relationally so impossible
parameters are not assigned an arbitrary natural number. -/
def CycleExtremalValue (ℓ : ℕ) (n e k : ℕ) : Prop :=
  IsLeast {k | CycleAttainableColorCount ℓ n e k} k

/-- Any feasible instance has an attained minimum. -/
theorem exists_cycleExtremalValue {n e : ℕ} (h : ∃ k, CycleAttainableColorCount ℓ n e k) :
    ∃ k, CycleExtremalValue ℓ n e k := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hk ↦ Nat.find_min' h hk⟩

theorem cycleExtremalValue_unique {n e k l : ℕ} (hk : CycleExtremalValue ℓ n e k)
    (hl : CycleExtremalValue ℓ n e l) : k = l := hk.unique hl

/-- The epsilon target bounds the actual attained minimum over hosts and colors. -/
theorem cycleExtremalValue_bounds_of_lower_upper {ε : ℝ} {n : ℕ}
    (hl : CycleLowerBoundAt ℓ ε n) (hu : CycleUpperBoundAt ℓ ε n) :
    ∃ k, CycleExtremalValue ℓ n (exactThreshold n) k ∧
      (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (k : ℝ) ∧
      (k : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2 := by
  obtain ⟨G, c, hm, hv, hc⟩ := hu
  have ha : CycleAttainableColorCount ℓ n (exactThreshold n) (usedColors c) :=
    ⟨G, ℕ, c, hm, hv, rfl⟩
  obtain ⟨k, hk⟩ := exists_cycleExtremalValue ⟨usedColors c, ha⟩
  refine ⟨k, hk, ?_, (Nat.cast_le.mpr (hk.2 ha)).trans hc⟩
  obtain ⟨H, K, d, hHm, hd, hdk⟩ := hk.1
  simpa only [hdk] using hl H K d hHm hd

theorem cycleAtLeast_iff_exact_lowerBound (n e : ℕ) (B : ℝ) :
    (∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      e ≤ EdgeCount G → ValidCycleColoring ℓ c → B ≤ (usedColors c : ℝ)) ↔
    (∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      e = EdgeCount G → ValidCycleColoring ℓ c → B ≤ (usedColors c : ℝ)) := by
  constructor
  · intro h G K c he hc
    exact h G K c he.le hc
  · intro h G K c he hc
    obtain ⟨H, hHG, hH⟩ := exists_subgraph_edgeCount_eq G he
    have hl := h H K (c ∘ (Copy.ofLE H G hHG).mapEdgeSet) hH.symm (hc.restrict hHG)
    exact hl.trans (Nat.cast_le.mpr (usedColors_comap_le c _))

def CycleAsymptoticExtremalValue (ℓ : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∃ q, CycleExtremalValue ℓ n (exactThreshold n) q ∧
      (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (q : ℝ) ∧
      (q : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2

theorem validCycleColoring_seven_iff {V K : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} : ValidCycleColoring 7 c ↔ ValidC7Coloring c := Iff.rfl

theorem cycleAttainableColorCount_seven_iff {n e q : ℕ} :
    CycleAttainableColorCount 7 n e q ↔ AttainableColorCount n e q := Iff.rfl

theorem cycleExtremalValue_seven_iff {n e q : ℕ} :
    CycleExtremalValue 7 n e q ↔ ExtremalValue n e q := Iff.rfl

end Erdos809
