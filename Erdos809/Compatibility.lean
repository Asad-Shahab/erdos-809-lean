import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Full-host walk compatibility. Walks in this module may repeat vertices. -/

namespace Erdos809

variable {V : Type*} (G : SimpleGraph V)

/-- A two-step walk, including closed walks. -/
def Walk2 (u v : V) : Prop := ∃ z, G.Adj u z ∧ G.Adj z v

/-- A three-step walk, with no distinctness requirements. -/
def Walk3 (u v : V) : Prop := ∃ z t, G.Adj u z ∧ G.Adj z t ∧ G.Adj t v

theorem walk2_symm {u v : V} (h : Walk2 G u v) : Walk2 G v u := by
  obtain ⟨z, huz, hzv⟩ := h
  exact ⟨z, hzv.symm, huz.symm⟩

theorem walk3_symm {u v : V} (h : Walk3 G u v) : Walk3 G v u := by
  obtain ⟨z, t, huz, hzt, htv⟩ := h
  exact ⟨t, z, htv.symm, hzt.symm, huz.symm⟩

/-- Exclude complementary two- and three-walks for all four endpoint orientations.
The host edges themselves are supplied separately by callers. -/
def Compatible (u v a b : V) : Prop :=
  ¬ (Walk2 G u a ∧ Walk3 G v b) ∧
  ¬ (Walk2 G u b ∧ Walk3 G v a) ∧
  ¬ (Walk2 G v a ∧ Walk3 G u b) ∧
  ¬ (Walk2 G v b ∧ Walk3 G u a)

theorem Compatible.flip_left {u v a b : V} (h : Compatible G u v a b) :
    Compatible G v u a b := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₃, h₄, h₁, h₂⟩

theorem Compatible.flip_right {u v a b : V} (h : Compatible G u v a b) :
    Compatible G u v b a := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨h₂, h₁, h₄, h₃⟩

theorem Compatible.symm {u v a b : V} (h : Compatible G u v a b) :
    Compatible G a b u v := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨fun ⟨p, q⟩ => h₁ ⟨walk2_symm G p, walk3_symm G q⟩,
    fun ⟨p, q⟩ => h₃ ⟨walk2_symm G p, walk3_symm G q⟩,
    fun ⟨p, q⟩ => h₂ ⟨walk2_symm G p, walk3_symm G q⟩,
    fun ⟨p, q⟩ => h₄ ⟨walk2_symm G p, walk3_symm G q⟩⟩

/-- One endpoint neighborhood cannot meet both neighborhoods of a compatible mate. -/
theorem Compatible.partial_row {u v a b : V} (h : Compatible G u v a b)
    (huv : G.Adj u v) : ¬ (Walk2 G u a ∧ Walk2 G u b) := by
  rintro ⟨hua, z, huz, hzb⟩
  exact h.1 ⟨hua, u, z, huv.symm, huz, hzb⟩

/-- The cross-neighborhood intersection relation is a partial matching. -/
theorem Compatible.partial_column {u v a b : V} (h : Compatible G u v a b)
    (hab : G.Adj a b) : ¬ (Walk2 G u a ∧ Walk2 G v a) := by
  rintro ⟨hua, hva⟩
  exact (h.symm G).partial_row G hab ⟨walk2_symm G hua, walk2_symm G hva⟩

/-- An edge is triangular precisely when its endpoints have a common neighbor. -/
def Triangular (u v : V) : Prop := G.Adj u v ∧ Walk2 G u v

/-- The two-cross-intersection case in the selected triangular edge geometry. -/
theorem Compatible.outside_of_aligned {u v a b : V}
    (h : Compatible G u v a b) (hua : Walk2 G u a) (hvb : Walk2 G v b)
    (hab : Walk2 G a b) :
    ∃ z, ∀ t, G.Adj z t → ¬ G.Adj u t ∧ ¬ G.Adj v t := by
  obtain ⟨z, haz, hzb⟩ := hab
  refine ⟨z, fun t hzt => ⟨?_, ?_⟩⟩
  · intro hut
    exact h.2.2.2 ⟨hvb, t, z, hut, hzt.symm, haz.symm⟩
  · intro hvt
    exact h.1 ⟨hua, t, z, hvt, hzt.symm, hzb⟩

/-- A compatible triangular mate supplies an entire neighborhood outside the
endpoint-neighborhood union. No distinctness of the four endpoints is assumed. -/
theorem Compatible.exists_outside_neighborhood {u v a b : V}
    (h : Compatible G u v a b) (huv : G.Adj u v) (hab : Triangular G a b) :
    ∃ z, ∀ t, G.Adj z t → ¬ G.Adj u t ∧ ¬ G.Adj v t := by
  classical
  have isolated (z : V) (hu : ¬ Walk2 G u z) (hv : ¬ Walk2 G v z) :
      ∀ t, G.Adj z t → ¬ G.Adj u t ∧ ¬ G.Adj v t := by
    intro t hzt
    exact ⟨fun hut => hu ⟨t, hut, hzt.symm⟩,
      fun hvt => hv ⟨t, hvt, hzt.symm⟩⟩
  by_cases hua : Walk2 G u a
  · have hub : ¬ Walk2 G u b := fun hub => h.partial_row G huv ⟨hua, hub⟩
    by_cases hvb : Walk2 G v b
    · exact h.outside_of_aligned G hua hvb hab.2
    · exact ⟨b, isolated b hub hvb⟩
  · by_cases hva : Walk2 G v a
    · have hvb : ¬ Walk2 G v b :=
        fun hvb => (h.flip_left G).partial_row G huv.symm ⟨hva, hvb⟩
      by_cases hub : Walk2 G u b
      · exact (h.flip_right G).outside_of_aligned G hub hva (walk2_symm G hab.2)
      · exact ⟨b, isolated b hub hvb⟩
    · exact ⟨a, isolated a hua hva⟩

end Erdos809
