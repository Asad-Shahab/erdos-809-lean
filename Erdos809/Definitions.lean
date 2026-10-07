module
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Exact finite semantics for Erdős 809, C₇

`Copy` is an injective adjacency-preserving map, not an induced embedding.
Colors are counted by their finite image, with no assumption on unused labels.
-/
namespace Erdos809

open SimpleGraph

/-- A labelled simple, not necessarily induced, seven-cycle. -/
abbrev C7Copy {V : Type*} (G : SimpleGraph V) := Copy (cycleGraph 7) G

/-- Number of unordered host edges. -/
noncomputable def EdgeCount {V : Type*} (G : SimpleGraph V) : ℕ := Nat.card G.edgeSet

/-- The cardinality of the image, rather than the size of the nominal palette. -/
noncomputable def usedColors {V K : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → K) : ℕ := (Set.range c).ncard

/-- Every simple seven-cycle has pairwise distinct edge colors. -/
def ValidC7Coloring {V K : Type*} {G : SimpleGraph V} (c : G.edgeSet → K) : Prop :=
  ∀ F : C7Copy G, Function.Injective (c ∘ F.mapEdgeSet)

/-- The exact one-edge excess over the integral Mantel threshold. -/
def exactThreshold (n : ℕ) : ℕ := n * n / 4 + 1

/-- Universal finite lower bound; isolated vertices remain counted by `Fin n`. -/
def LowerBoundAt (ε : ℝ) (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
    exactThreshold n ≤ EdgeCount G → ValidC7Coloring c →
      (1 / 8 - ε) * (n : ℝ) ^ 2 ≤ (usedColors c : ℝ)

/-- Existential finite upper bound, with labels in an unrestricted countable set. -/
def UpperBoundAt (ε : ℝ) (n : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (c : G.edgeSet → ℕ),
    exactThreshold n ≤ EdgeCount G ∧ ValidC7Coloring c ∧
      (usedColors c : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2

/-- All sufficiently large integers, with the cutoff independent of host and coloring. -/
def AsymptoticLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, LowerBoundAt ε n

/-- All sufficiently large integers, not only a selected subsequence. -/
def AsymptoticUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, UpperBoundAt ε n

/-- The two-sided exact-threshold target, in universal/existential epsilon form. -/
def AsymptoticTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, LowerBoundAt ε n ∧ UpperBoundAt ε n

theorem asymptoticTheorem_iff :
    AsymptoticTheorem ↔ AsymptoticLowerBound ∧ AsymptoticUpperBound := by
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

/-- A genuine C₇ has seven unordered edges. This small finite fact is kernel evaluated. -/
theorem c7_edgeCount : EdgeCount (cycleGraph 7) = 7 := by
  rw [EdgeCount, Nat.card_eq_fintype_card]
  decide

theorem ValidC7Coloring.of_injective {V K : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} (hc : Function.Injective c) : ValidC7Coloring c :=
  fun F ↦ hc.comp F.mapEdgeSet.injective

/-- Validity restricts along any injective graph homomorphism. -/
theorem ValidC7Coloring.comap {V W K : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {c : G.edgeSet → K} (hc : ValidC7Coloring c)
    (F : Copy H G) : ValidC7Coloring (c ∘ F.mapEdgeSet) := by
  intro C x y h
  apply hc (F.comp C)
  have hm (e : (cycleGraph 7).edgeSet) :
      (F.comp C).mapEdgeSet e = F.mapEdgeSet (C.mapEdgeSet e) := by
    apply Subtype.ext
    exact (Sym2.map_map (g := F.toHom) (f := C.toHom) e.val).symm
  simpa only [Function.comp_apply, hm] using h

/-- Restriction cannot create colors. No retention of original conflicts is asserted. -/
theorem usedColors_comap_le {V W K : Type*} [Finite V] {G : SimpleGraph V}
    {H : SimpleGraph W} (c : G.edgeSet → K) (F : Copy H G) :
    usedColors (c ∘ F.mapEdgeSet) ≤ usedColors c := by
  apply Set.ncard_le_ncard
  · rintro _ ⟨e, rfl⟩
    exact ⟨F.mapEdgeSet e, rfl⟩
  · exact Set.finite_range c

theorem ValidC7Coloring.restrict {V K : Type*} {G H : SimpleGraph V}
    {c : G.edgeSet → K} (hc : ValidC7Coloring c) (hHG : H ≤ G) :
    ValidC7Coloring (c ∘ (Copy.ofLE H G hHG).mapEdgeSet) := hc.comap _

theorem edgeCount_mono {V W : Type*} [Finite W] {G : SimpleGraph V}
    {H : SimpleGraph W} (F : Copy G H) : EdgeCount G ≤ EdgeCount H :=
  Nat.card_le_card_of_injective _ F.mapEdgeSet.injective

theorem usedColors_injective {V K : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} (hc : Function.Injective c) : usedColors c = EdgeCount G :=
  Set.ncard_range_of_injective hc

theorem usedColors_le_card {V K : Type*} [Finite K] {G : SimpleGraph V}
    (c : G.edgeSet → K) : usedColors c ≤ Nat.card K := Set.ncard_le_card _

/-- Injectively renaming labels preserves the rainbow requirement. -/
theorem ValidC7Coloring.postcomp {V K L : Type*} {G : SimpleGraph V}
    {c : G.edgeSet → K} (hc : ValidC7Coloring c) {f : K → L}
    (hf : Function.Injective f) : ValidC7Coloring (f ∘ c) :=
  fun F ↦ hf.comp (hc F)

/-- Injective relabelling leaves the number of actually used colors unchanged. -/
theorem usedColors_postcomp {V K L : Type*} {G : SimpleGraph V}
    (c : G.edgeSet → K) {f : K → L} (hf : Function.Injective f) :
    usedColors (f ∘ c) = usedColors c := by
  unfold usedColors
  rw [Set.range_comp, Set.ncard_image_of_injective _ hf]

/-- An attained palette size among all eligible hosts and all valid colorings. -/
def AttainableColorCount (n e k : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
    e ≤ EdgeCount G ∧ ValidC7Coloring c ∧ usedColors c = k

/-- The canonical host-minimized value, expressed relationally so impossible
parameters are not assigned an arbitrary natural number. -/
def ExtremalValue (n e k : ℕ) : Prop := IsLeast {k | AttainableColorCount n e k} k

/-- Any feasible instance has an attained minimum. -/
theorem exists_extremalValue {n e : ℕ} (h : ∃ k, AttainableColorCount n e k) :
    ∃ k, ExtremalValue n e k := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hk ↦ Nat.find_min' h hk⟩

theorem extremalValue_unique {n e k l : ℕ} (hk : ExtremalValue n e k)
    (hl : ExtremalValue n e l) : k = l := hk.unique hl

/-- The epsilon target bounds the actual attained minimum over hosts and colors. -/
theorem extremalValue_bounds_of_lower_upper {ε : ℝ} {n : ℕ}
    (hl : LowerBoundAt ε n) (hu : UpperBoundAt ε n) :
    ∃ k, ExtremalValue n (exactThreshold n) k ∧
      (1/8 - ε) * (n : ℝ)^2 ≤ (k : ℝ) ∧
      (k : ℝ) ≤ (1/8 + ε) * (n : ℝ)^2 := by
  obtain ⟨G, c, hm, hv, hc⟩ := hu
  have ha : AttainableColorCount n (exactThreshold n) (usedColors c) :=
    ⟨G, ℕ, c, hm, hv, rfl⟩
  obtain ⟨k, hk⟩ := exists_extremalValue ⟨usedColors c, ha⟩
  refine ⟨k, hk, ?_, (Nat.cast_le.mpr (hk.2 ha)).trans hc⟩
  obtain ⟨H, K, d, hHm, hd, hdk⟩ := hk.1
  simpa only [hdk] using hl H K d hHm hd

/-- Retain exactly any prescribed number of edges, preserving every vertex. -/
theorem exists_subgraph_edgeCount_eq {V : Type*} [Finite V] (G : SimpleGraph V)
    {e : ℕ} (he : e ≤ EdgeCount G) : ∃ H : SimpleGraph V, H ≤ G ∧ EdgeCount H = e := by
  obtain ⟨D, hDG, hD⟩ := Set.exists_subset_card_eq (s := G.edgeSet) he
  have hdis : Disjoint D Sym2.diagSet := by
    apply Set.disjoint_left.mpr
    intro x hx hdiag
    exact G.not_isDiag_of_mem_edgeSet (hDG hx) hdiag
  refine ⟨fromEdgeSet D, ?_, ?_⟩
  · intro u v huv
    exact hDG huv.1
  · have hs : D \ Sym2.diagSet = D := by
      ext x
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun hd ↦ Set.disjoint_left.mp hdis h hd⟩⟩
    change (fromEdgeSet D).edgeSet.ncard = e
    rw [edgeSet_fromEdgeSet, hs]
    exact hD

/-- Exactly-e and at-least-e formulations give the same universal palette lower
bound. Deletion may destroy conflicts, which does not affect this implication. -/
theorem atLeast_iff_exact_lowerBound (n e : ℕ) (B : ℝ) :
    (∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      e ≤ EdgeCount G → ValidC7Coloring c → B ≤ (usedColors c : ℝ)) ↔
    (∀ (G : SimpleGraph (Fin n)) (K : Type) (c : G.edgeSet → K),
      e = EdgeCount G → ValidC7Coloring c → B ≤ (usedColors c : ℝ)) := by
  constructor
  · intro h G K c he hc
    exact h G K c he.le hc
  · intro h G K c he hc
    obtain ⟨H, hHG, hH⟩ := exists_subgraph_edgeCount_eq G he
    have hl := h H K (c ∘ (Copy.ofLE H G hHG).mapEdgeSet) hH.symm (hc.restrict hHG)
    exact hl.trans (Nat.cast_le.mpr (usedColors_comap_le c _))

end Erdos809
