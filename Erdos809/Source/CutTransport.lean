module
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Transport cut deficits through an injective graph copy

The image of a cut of a retained graph is a cut of the original graph. Every
retained crossing edge remains crossing: injectivity prevents a vertex outside
the retained cut from entering its image. Consequently the cut-deficit loss is
bounded by the entire original-to-retained edge loss.
-/

namespace Erdos809.Source

open SimpleGraph Finset

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {J : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel J.Adj]

/-- An injective graph copy carries each ordered crossing pair to a distinct
crossing pair of the image cut. -/
theorem interedges_card_le_copy (F : Copy J G) (A : Finset W) :
    (J.interedges A Aᶜ).card ≤
      (G.interedges (A.image F) (A.image F)ᶜ).card := by
  apply Finset.card_le_card_of_injOn (fun p : W × W ↦ (F p.1, F p.2))
  · intro p hp
    change p ∈ J.interedges A Aᶜ at hp
    change (F p.1, F p.2) ∈ G.interedges (A.image F) (A.image F)ᶜ
    rw [SimpleGraph.mem_interedges_iff] at hp ⊢
    obtain ⟨hp₁, hp₂, hadj⟩ := hp
    refine ⟨mem_image.mpr ⟨p.1, hp₁, rfl⟩, ?_, F.toHom.map_rel hadj⟩
    simp only [mem_compl] at hp₂ ⊢
    intro hm
    obtain ⟨w, hw, hweq⟩ := mem_image.mp hm
    have hwp : w = p.2 := F.injective hweq
    exact hp₂ (hwp ▸ hw)
  · intro p _ q _ hpq
    exact Prod.ext (F.injective (congrArg Prod.fst hpq))
      (F.injective (congrArg Prod.snd hpq))

/-- A uniform lower bound for original cut deficits loses at most the total
number of edges deleted from the original graph. -/
theorem cut_deficit_copy (F : Copy J G) {r : ℝ}
    (hdeficit : ∀ B : Finset V,
      r ≤ (G.edgeFinset.card : ℝ) - (G.interedges B Bᶜ).card)
    (A : Finset W) :
    r - ((G.edgeFinset.card : ℝ) - J.edgeFinset.card) ≤
      (J.edgeFinset.card : ℝ) - (J.interedges A Aᶜ).card := by
  have hcut : ((J.interedges A Aᶜ).card : ℝ) ≤
      (G.interedges (A.image F) (A.image F)ᶜ).card :=
    Nat.cast_le.mpr (interedges_card_le_copy F A)
  have hsource := hdeficit (A.image F)
  linarith only [hcut, hsource]

/-- A supplied upper bound on edge loss yields the same bound without retaining
the exact loss expression. -/
theorem cut_deficit_copy_of_loss_le (F : Copy J G) {r q : ℝ}
    (hdeficit : ∀ B : Finset V,
      r ≤ (G.edgeFinset.card : ℝ) - (G.interedges B Bᶜ).card)
    (hloss : (G.edgeFinset.card : ℝ) - J.edgeFinset.card ≤ q)
    (A : Finset W) :
    r - q ≤ (J.edgeFinset.card : ℝ) - (J.interedges A Aᶜ).card := by
  have h := cut_deficit_copy F hdeficit A
  linarith only [h, hloss]

end Erdos809.Source
