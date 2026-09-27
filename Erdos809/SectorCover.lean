import Erdos809.PatternSectors

/-! Split an exact cover along sectors only when every whole pattern lies
in one sector. Empty patterns are assigned by the explicit pattern tag. -/

namespace Erdos809

open Finset
open scoped BigOperators

namespace ExactPatternCover

variable {E P : Type*} [Fintype E] [Fintype P] [DecidableEq E]
variable {capacity : E → ℝ} {edges : P → Finset E}
variable (cover : ExactPatternCover capacity edges)

open Classical in
noncomputable def sectorEdges (side : E → Prop) (p : P) : Finset {e // side e} :=
  univ.filter fun e => e.val ∈ edges p

open Classical in
noncomputable def sectorCover (side : E → Prop) (tag : P → Prop)
    (hhom : ∀ p e, e ∈ edges p → (side e ↔ tag p)) :
    ExactPatternCover (fun e : {e // side e} => capacity e.val)
      (sectorEdges (edges := edges) side) where
  amount := fun p => if tag p then cover.amount p else 0
  nonneg := fun p => by split_ifs; exact cover.nonneg p; exact le_refl _
  covers := by
    intro e
    simp only [sectorEdges, mem_filter, mem_univ, true_and]
    rw [← cover.covers e.val]
    apply sum_congr rfl
    intro p _
    by_cases he : e.val ∈ edges p
    · have ht : tag p := (hhom p e.val he).mp e.property
      simp only [he, ht, if_true]
    · simp only [he, if_false]

open Classical in
theorem sectorCover_cost_add_complement (side : E → Prop) (tag : P → Prop)
    (hhom : ∀ p e, e ∈ edges p → (side e ↔ tag p)) :
    (cover.sectorCover side tag hhom).cost +
      (cover.sectorCover (fun e => ¬ side e) (fun p => ¬ tag p)
        (fun p e he => not_congr (hhom p e he))).cost = cover.cost := by
  unfold cost sectorCover
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hp : tag p <;> simp [hp]

end ExactPatternCover

variable {V E P : Type*} [Fintype V]
variable (x : VertexWeights V) (G : SimpleGraph V)

/-- The full-host no-mixing theorem supplies the required whole-pattern tag.
This is not a restriction of the conflict graph to a smaller host. -/
theorem triangular_pattern_homogeneous {δ : ℝ} (hδ : 1 / 3 < δ)
    (hmin : x.MinDegreeAtLeast G δ) (u v : E → V) (edges : P → Finset E)
    (hedge : ∀ e, G.Adj (u e) (v e))
    (hpattern : ∀ p, (edges p : Set E).Pairwise
      (fun e f => Compatible G (u e) (v e) (u f) (v f))) :
    ∀ p e, e ∈ edges p →
      (Triangular G (u e) (v e) ↔ ∃ f ∈ edges p, Triangular G (u f) (v f)) := by
  intro p e he
  constructor
  · exact fun h => ⟨e, he, h⟩
  · rintro ⟨f, hf, ht⟩
    exact pattern_triangular_of_mem x G hδ hmin u v (edges p)
      (fun e _ => hedge e) (hpattern p) hf ht e he

end Erdos809
