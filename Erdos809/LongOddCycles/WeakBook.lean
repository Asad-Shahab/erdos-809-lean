import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! The near-degree weak book bound, obtained from Mantel and three-set
incidence counting. No stronger external book theorem is assumed. -/
namespace Erdos809.LongOddCycles
open SimpleGraph Finset

lemma card_three_sets_le {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : Finset V) :
    A.card + B.card + C.card ≤ Fintype.card V +
      (A ∩ B).card + (B ∩ C).card + (C ∩ A).card := by
  have h := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => show
    (if v ∈ A then 1 else 0) + (if v ∈ B then 1 else 0) +
      (if v ∈ C then 1 else 0) ≤
    1 + (if v ∈ A ∩ B then 1 else 0) + (if v ∈ B ∩ C then 1 else 0) +
      (if v ∈ C ∩ A then 1 else 0 : ℕ) by
        by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;> by_cases hc : v ∈ C <;>
          simp [ha, hb, hc])
  simpa only [sum_add_distrib, sum_boole, filter_mem_eq_inter,
    univ_inter, sum_const, card_univ, smul_eq_mul, mul_one] using h

lemma triangle_incidence {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) :
    G.degree a + G.degree b + G.degree c ≤ Fintype.card V +
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      (G.neighborFinset b ∩ G.neighborFinset c).card +
      (G.neighborFinset c ∩ G.neighborFinset a).card := by
  simpa using card_three_sets_le (G.neighborFinset a) (G.neighborFinset b)
    (G.neighborFinset c)

lemma triangle_of_above_quarter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : (Fintype.card V : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ)) :
    ∃ a b c : V, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  have hcf : ¬G.CliqueFree 3 := by
    intro h
    have hb := h.card_edgeFinset_le (r := 2)
    have hmod : (Fintype.card V % 2).choose 2 = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.mod_lt _ (by omega))
    simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, mul_one, hmod, add_zero] at hb
    have hb' : G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 :=
      hb.trans (Nat.div_le_div_right (Nat.sub_le _ _))
    have hcast := Nat.cast_le (α := ℝ) |>.mpr hb'
    have hdiv : ((Fintype.card V ^ 2 / 4 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
      have h : ((Fintype.card V ^ 2 / 4 : ℕ) : ℝ) ≤ ((Fintype.card V ^ 2 : ℕ) : ℝ) / 4 := Nat.cast_div_le
      push_cast at h
      exact h
    linarith
  unfold SimpleGraph.CliqueFree at hcf
  push_neg at hcf
  obtain ⟨s, hs⟩ := hcf
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := G.is3Clique_iff.mp hs
  exact ⟨a, b, c, hab, hac, hbc⟩

theorem weakBook {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ)
    (hm : (Fintype.card V : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ))
    (hd : ∀ v, d ≤ (G.degree v : ℝ)) :
    ∃ p q : V, G.Adj p q ∧
      d - (Fintype.card V : ℝ) / 3 ≤
        ((G.neighborFinset p ∩ G.neighborFinset q).card : ℝ) := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := triangle_of_above_quarter G hm
  by_contra! h
  have hi := triangle_incidence G a b c
  have hiR : (G.degree a : ℝ) + G.degree b + G.degree c ≤ Fintype.card V +
      (G.neighborFinset a ∩ G.neighborFinset b).card +
      (G.neighborFinset b ∩ G.neighborFinset c).card +
      (G.neighborFinset c ∩ G.neighborFinset a).card := by exact_mod_cast hi
  have h1 := h a b hab
  have h2 := h b c hbc
  have h3 := h c a hac.symm
  linarith [hd a, hd b, hd c]

end Erdos809.LongOddCycles
