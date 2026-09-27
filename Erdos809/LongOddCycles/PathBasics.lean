import Erdos809.Source.RobustPaths
import Mathlib.Tactic

/-!
# Exact path operations for the longer odd cycles

The greedy budget is sharp: it allows length zero and equality in the minimum
 degree bound. Paths are never shortened after their length has been fixed.
-/

namespace Erdos809.LongOddCycles

open SimpleGraph
open Source

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- A simple path of any prescribed affordable length avoiding a finite set.
The recursive forbidden set inserts the previous endpoint; irreflexivity ensures
that choosing its neighbor does not incur another forbidden vertex. -/
theorem exists_greedy_avoiding_path [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (L : ℕ) (S : Finset V) (u : V) (hu : u ∉ S)
    (hbudget : S.card + L ≤ G.minDegree) :
    ∃ v, HasAvoidingPath G u v L S := by
  induction L generalizing S u with
  | zero =>
    refine ⟨u, .nil, .nil, rfl, ?_⟩
    simpa using hu
  | succ L ih =>
    have hcard : S.card < (G.neighborFinset u).card := by
      rw [G.card_neighborFinset_eq_degree]
      have := G.minDegree_le_degree u
      omega
    have hnot : ¬G.neighborFinset u ⊆ S := fun h =>
      (Finset.card_le_card h).not_gt hcard
    obtain ⟨v, hv, hvS⟩ := Finset.not_subset.mp hnot
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    obtain ⟨w, p, hp, hlen, hav⟩ := ih (insert u S) v
      (by simp [hvS, huv.ne.symm]) (by simpa [Finset.card_insert_of_notMem hu,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbudget)
    refine ⟨w, p.cons huv, hp.cons (fun h => hav u h (by simp)), ?_, ?_⟩
    · simp [hlen]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact fun hxS => hav x hx (Finset.mem_insert_of_mem hxS)

/-- The first endpoint never reappears in the tail of a simple path. -/
lemma start_not_mem_tail {p : G.Walk u v} (hp : p.IsPath) : u ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [p.support_eq_cons] at hn
  exact (List.nodup_cons.mp hn).1

/-- Simple paths concatenate without any loss of length if their supports meet
only at the joining endpoint. Either constituent may have length zero. -/
theorem isPath_append {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hx hxq
  exact start_not_mem_tail hq ((hinter x hx (List.mem_of_mem_tail hxq)) ▸ hxq)

/-- Delete both endpoints from the support of a path. -/
def pathInterior [DecidableEq V] (p : G.Walk u v) : Finset V :=
  p.support.toFinset \ {u, v}

@[simp] theorem mem_pathInterior [DecidableEq V] {p : G.Walk u v} {x : V} :
    x ∈ pathInterior p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  simp [pathInterior]

@[simp] theorem start_not_mem_pathInterior [DecidableEq V] (p : G.Walk u v) :
    u ∉ pathInterior p := by simp

@[simp] theorem end_not_mem_pathInterior [DecidableEq V] (p : G.Walk u v) :
    v ∉ pathInterior p := by simp

/-- A positive simple path has exactly length minus one internal vertices. -/
theorem card_pathInterior [DecidableEq V] {p : G.Walk u v}
    (hp : p.IsPath) (huv : u ≠ v) : (pathInterior p).card = p.length - 1 := by
  have hend : ({u, v} : Finset V) ⊆ p.support.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  rw [pathInterior, Finset.card_sdiff_of_subset hend,
    List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  simp [huv]

/-- A nonzero simple path has distinct endpoints. -/
theorem endpoints_ne_of_isPath {p : G.Walk u v} (hp : p.IsPath)
    (hlen : 0 < p.length) : u ≠ v := by
  intro huv
  subst v
  have hnil := (Walk.isPath_iff_eq_nil p).mp hp
  simp [hnil] at hlen

/-- An interior forbidden set works for every shorter path supported inside the
same path and having the same endpoints. -/
theorem pathInterior_mono [DecidableEq V] {p q : G.Walk u v}
    (hs : q.support ⊆ p.support) : pathInterior q ⊆ pathInterior p := by
  intro x hx
  obtain ⟨hx, hxu, hxv⟩ := mem_pathInterior.mp hx
  exact mem_pathInterior.mpr ⟨hs hx, hxu, hxv⟩

/-- Two endpoint paths with disjoint interiors form a simple cycle when their
combined length is at least three. Both prescribed lengths are retained. -/
theorem isCycle_append {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v)
    (hlen : 3 ≤ p.length + q.length) : (p.append q).IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  have hnil : ¬(p.append q).Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_append]
    omega
  refine ⟨?_, by simpa using hlen⟩
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ hnil,
    Walk.tail_support_append, List.nodup_append']
  refine ⟨hp.support_nodup.tail, hq.support_nodup.tail, ?_⟩
  intro x hx hxq
  rcases hinter x (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hxq) with rfl | rfl
  · exact start_not_mem_tail hp hx
  · exact start_not_mem_tail hq hxq

/-- The forbidden interior interface directly certifies the cycle closure. -/
theorem isCycle_append_of_avoiding_interior [DecidableEq V]
    {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (havoid : ∀ x ∈ q.support, x ∉ pathInterior p)
    (hlen : 3 ≤ p.length + q.length) : (p.append q).IsCycle := by
  apply isCycle_append hp hq _ hlen
  intro x hxp hxq
  by_contra h
  have h' : x ≠ u ∧ x ≠ v := by tauto
  exact havoid x hxq (mem_pathInterior.mpr ⟨hxp, h'.1, h'.2⟩)

end Erdos809.LongOddCycles
