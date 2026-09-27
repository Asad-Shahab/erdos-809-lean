import Erdos809.Source.ColoringBridge
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.List.Nodup

/-!
# Explicit seven-cycles for the near-cut branch

The counting argument supplies a trigger edge and finite sets satisfying
`NearCutCliqueWitness`. This module constructs an actual simple seven-cycle
through every two selected crossing edges, including edges sharing an endpoint.
All edges and colors refer to the original source graph.
-/

namespace Erdos809.Source

open SimpleGraph Finset

variable {V K : Type*} [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The finite neighborhood properties needed for the three seven-cycle cases.
The two vertices in `common_right` are allowed to coincide. -/
structure NearCutCliqueWitness (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q S R : Finset V) (u v : V) : Prop where
  disjoint : Disjoint P Q
  left_subset : S ⊆ P
  right_subset : R ⊆ Q
  trigger_left_mem : u ∈ Q
  trigger_right_mem : v ∈ Q
  trigger_adj : G.Adj u v
  trigger_left_not : u ∉ R
  trigger_right_not : v ∉ R
  endpoints : ∀ x ∈ S, G.Adj u x ∧ G.Adj v x
  common_right : ∀ y ∈ R, ∀ w ∈ R,
    2 < (P.filter (fun b ↦ G.Adj y b ∧ G.Adj w b)).card
  common_trigger_left : ∀ y ∈ R,
    2 < (P.filter (fun b ↦ G.Adj u b ∧ G.Adj y b)).card
  common_trigger_right : ∀ y ∈ R,
    2 < (P.filter (fun b ↦ G.Adj v b ∧ G.Adj y b)).card
  row : ∀ z ∈ S, 1 < (R.filter (G.Adj z)).card

private lemma exists_mem_avoiding_pair {C : Finset V} (hC : 2 < C.card) (x z : V) :
    ∃ b ∈ C, b ≠ x ∧ b ≠ z := by
  have hnot : ¬C ⊆ {x, z} := by
    intro hsub
    exact hC.not_ge ((card_le_card hsub).trans card_le_two)
  obtain ⟨b, hb, hbxz⟩ := not_subset.mp hnot
  exact ⟨b, hb, by simpa only [mem_insert, mem_singleton, not_or] using hbxz⟩

omit [DecidableEq V] in
/-- Three different left vertices and four different right vertices give
seven different actual vertices, independently of any cluster labels. -/
private lemma alternating_seven_nodup {P Q : Finset V} (hPQ : Disjoint P Q)
    {p₀ p₁ p₂ q₀ q₁ q₂ q₃ : V}
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) (hp₂ : p₂ ∈ P)
    (hq₀ : q₀ ∈ Q) (hq₁ : q₁ ∈ Q) (hq₂ : q₂ ∈ Q) (hq₃ : q₃ ∈ Q)
    (hp : p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂)
    (hq : q₀ ≠ q₁ ∧ q₀ ≠ q₂ ∧ q₀ ≠ q₃ ∧
      q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃) :
    [q₀, p₀, q₁, p₁, q₂, p₂, q₃].Nodup := by
  have hpq {p q : V} (hp : p ∈ P) (hq : q ∈ Q) : p ≠ q := by
    intro heq
    exact disjoint_left.mp hPQ hp (heq.symm ▸ hq)
  have hqp {q p : V} (hq : q ∈ Q) (hp : p ∈ P) : q ≠ p :=
    (hpq hp hq).symm
  rcases hp with ⟨hp₀₁, hp₀₂, hp₁₂⟩
  rcases hq with ⟨hq₀₁, hq₀₂, hq₀₃, hq₁₂, hq₁₃, hq₂₃⟩
  simp [hp₀₁, hp₀₂, hp₁₂, hq₀₁, hq₀₂, hq₀₃, hq₁₂, hq₁₃, hq₂₃,
    hpq hp₀ hq₁, hpq hp₀ hq₂, hpq hp₀ hq₃,
    hpq hp₁ hq₂, hpq hp₁ hq₃, hpq hp₂ hq₃,
    hqp hq₀ hp₀, hqp hq₀ hp₁, hqp hq₀ hp₂,
    hqp hq₁ hp₁, hqp hq₁ hp₂, hqp hq₂ hp₂]

private def alternatingSevenCopy {p₀ p₁ p₂ q₀ q₁ q₂ q₃ : V}
    (hn : [q₀, p₀, q₁, p₁, q₂, p₂, q₃].Nodup)
    (h₀ : G.Adj q₀ p₀) (h₁ : G.Adj p₀ q₁) (h₂ : G.Adj q₁ p₁)
    (h₃ : G.Adj p₁ q₂) (h₄ : G.Adj q₂ p₂) (h₅ : G.Adj p₂ q₃)
    (h₆ : G.Adj q₃ q₀) : C7Copy G :=
  sevenCycleCopy [q₀, p₀, q₁, p₁, q₂, p₂, q₃].get hn.injective_get (by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · exact h₅
    · exact h₆)

private lemma nearCut_disjoint_colors_ne {P Q S R : Finset V} {u v x y z w : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hx : x ∈ S) (hy : y ∈ R) (hz : z ∈ S) (hw : w ∈ R)
    (hxy : G.Adj x y) (hzw : G.Adj z w) (hxz : x ≠ z) (hyw : y ≠ w) :
    edgeColor c hxy ≠ edgeColor c hzw := by
  obtain ⟨b, hb, hbx, hbz⟩ := exists_mem_avoiding_pair (hW.common_right y hy w hw) x z
  obtain ⟨hbP, hyb, hwb⟩ := mem_filter.mp hb
  have hvy : v ≠ y := fun h ↦ hW.trigger_right_not (h.symm ▸ hy)
  have hvw : v ≠ w := fun h ↦ hW.trigger_right_not (h.symm ▸ hw)
  have hyu : y ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hy)
  have hwu : w ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hw)
  have hn := alternating_seven_nodup hW.disjoint
    (hW.left_subset hx) hbP (hW.left_subset hz)
    hW.trigger_right_mem (hW.right_subset hy) (hW.right_subset hw) hW.trigger_left_mem
    ⟨hbx.symm, hxz, hbz⟩ ⟨hvy, hvw, hW.trigger_adj.ne.symm, hyw, hyu, hwu⟩
  let F := alternatingSevenCopy hn (hW.endpoints x hx).2 hxy hyb hwb.symm
    hzw.symm (hW.endpoints z hz).1.symm hW.trigger_adj
  have hne := edgeColor_ne_of_copy c hc F
    (show (cycleGraph 7).Adj 1 2 by decide)
    (show (cycleGraph 7).Adj 5 4 by decide) (by decide)
  exact hne

private lemma nearCut_shared_left_colors_ne {P Q S R : Finset V} {u v x y w : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hx : x ∈ S) (hy : y ∈ R) (hw : w ∈ R)
    (hxy : G.Adj x y) (hxw : G.Adj x w) (hyw : y ≠ w) :
    edgeColor c hxy ≠ edgeColor c hxw := by
  obtain ⟨a, ha, hax, _⟩ := exists_mem_avoiding_pair (hW.common_trigger_right y hy) x x
  obtain ⟨haP, hva, hya⟩ := mem_filter.mp ha
  obtain ⟨b, hb, hbx, hba⟩ := exists_mem_avoiding_pair (hW.common_trigger_left w hw) x a
  obtain ⟨hbP, hub, hwb⟩ := mem_filter.mp hb
  have hvy : v ≠ y := fun h ↦ hW.trigger_right_not (h.symm ▸ hy)
  have hvw : v ≠ w := fun h ↦ hW.trigger_right_not (h.symm ▸ hw)
  have hyu : y ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hy)
  have hwu : w ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hw)
  have hn := alternating_seven_nodup hW.disjoint haP (hW.left_subset hx) hbP
    hW.trigger_right_mem (hW.right_subset hy) (hW.right_subset hw) hW.trigger_left_mem
    ⟨hax, hba.symm, hbx.symm⟩ ⟨hvy, hvw, hW.trigger_adj.ne.symm, hyw, hyu, hwu⟩
  let F := alternatingSevenCopy hn hva hya.symm hxy.symm hxw hwb hub.symm hW.trigger_adj
  have hne := edgeColor_ne_of_copy c hc F
    (show (cycleGraph 7).Adj 3 2 by decide)
    (show (cycleGraph 7).Adj 3 4 by decide) (by decide)
  exact hne

private lemma nearCut_shared_right_colors_ne {P Q S R : Finset V} {u v x z y : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hx : x ∈ S) (hz : z ∈ S) (hy : y ∈ R)
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) :
    edgeColor c hxy ≠ edgeColor c hzy := by
  obtain ⟨w, hw, hwy⟩ := exists_mem_ne (hW.row z hz) y
  obtain ⟨hwR, hzw⟩ := mem_filter.mp hw
  obtain ⟨b, hb, hbx, hbz⟩ := exists_mem_avoiding_pair (hW.common_trigger_left w hwR) x z
  obtain ⟨hbP, hub, hwb⟩ := mem_filter.mp hb
  have hvy : v ≠ y := fun h ↦ hW.trigger_right_not (h.symm ▸ hy)
  have hvw : v ≠ w := fun h ↦ hW.trigger_right_not (h.symm ▸ hwR)
  have hyu : y ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hy)
  have hwu : w ≠ u := fun h ↦ hW.trigger_left_not (h ▸ hwR)
  have hn := alternating_seven_nodup hW.disjoint (hW.left_subset hx) (hW.left_subset hz) hbP
    hW.trigger_right_mem (hW.right_subset hy) (hW.right_subset hwR) hW.trigger_left_mem
    ⟨hxz, hbx.symm, hbz.symm⟩ ⟨hvy, hvw, hW.trigger_adj.ne.symm, hwy.symm, hyu, hwu⟩
  let F := alternatingSevenCopy hn (hW.endpoints x hx).2 hxy hzy.symm hzw hwb hub.symm
    hW.trigger_adj
  have hne := edgeColor_ne_of_copy c hc F
    (show (cycleGraph 7).Adj 1 2 by decide)
    (show (cycleGraph 7).Adj 3 2 by decide) (by decide)
  exact hne

/-- Every pair of distinct selected crossing edges has different original
colors. This includes both possible shared-endpoint cases. -/
theorem nearCut_selected_colors_ne {P Q S R : Finset V} {u v x y z w : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (hx : x ∈ S) (hy : y ∈ R) (hz : z ∈ S) (hw : w ∈ R)
    (hxy : G.Adj x y) (hzw : G.Adj z w) (hne : (x, y) ≠ (z, w)) :
    edgeColor c hxy ≠ edgeColor c hzw := by
  by_cases hxz : x = z
  · subst z
    have hyw : y ≠ w := fun h ↦ hne (Prod.ext rfl h)
    exact nearCut_shared_left_colors_ne hW c hc hx hy hw hxy hzw hyw
  · by_cases hyw : y = w
    · subst w
      exact nearCut_shared_right_colors_ne hW c hc hx hz hy hxy hzw hxz
    · exact nearCut_disjoint_colors_ne hW c hc hx hy hz hw hxy hzw hxz hyw

/-- Regard the selected ordered crossing pairs as original unordered edges. -/
def nearCutSelectedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S R : Finset V) :
    (G.interedges S R) → G.edgeSet :=
  fun e ↦ ⟨s(e.val.1, e.val.2), (G.mem_interedges_iff.mp e.property).2.2⟩

/-- The original coloring is injective on all selected near-cut edges. -/
theorem nearCut_color_injective {P Q S R : Finset V} {u v : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    Function.Injective (c ∘ nearCutSelectedEdges G S R) := by
  intro e f heq
  apply Subtype.ext
  by_contra hne
  obtain ⟨hx, hy, hxy⟩ := G.mem_interedges_iff.mp e.property
  obtain ⟨hz, hw, hzw⟩ := G.mem_interedges_iff.mp f.property
  exact nearCut_selected_colors_ne hW c hc hx hy hz hw hxy hzw hne heq

/-- A near-cut clique witness forces at least as many used colors as
selected crossing edges, for arbitrary original labels. -/
theorem nearCut_card_le_usedColors [Fintype V] {P Q S R : Finset V} {u v : V}
    (hW : NearCutCliqueWitness G P Q S R u v)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) :
    (G.interedges S R).card ≤ usedColors c := by
  let f : (G.interedges S R) → Set.range c :=
    fun e ↦ ⟨c (nearCutSelectedEdges G S R e), ⟨nearCutSelectedEdges G S R e, rfl⟩⟩
  have hf : Function.Injective f := by
    intro e e' h
    exact nearCut_color_injective hW c hc (congrArg Subtype.val h)
  calc
    (G.interedges S R).card = Nat.card (G.interedges S R) := by
      rw [Nat.card_eq_fintype_card]
      simp
    _ ≤ Nat.card (Set.range c) := Nat.card_le_card_of_injective f hf
    _ = usedColors c := rfl

end Erdos809.Source
