module
public import Erdos809.LongOddCycles.Definitions
public import Erdos809.LongOddCycles.PathBasics

@[expose] public section

/-!
# Exact cycles and their non-induced copies

Every edge of the closed walk is in the image of the copy's edge map. This is
what lets validity transfer to the two designated original-host edges.
-/

namespace Erdos809.LongOddCycles

open SimpleGraph

variable {V K : Type*} {G : SimpleGraph V} {u v : V}

/-- Distinct cyclically ordered vertices with consecutive adjacencies define a
non-induced copy; additional chords in the host cause no difficulty. -/
def cycleCopyOfVertices (n : ℕ) [NeZero n] (hn : 2 ≤ n) (f : Fin n → V)
    (hf : Function.Injective f)
    (ha : ∀ i : Fin n, G.Adj (f i) (f (i + 1))) : CycleCopy n G where
  toHom := {
    toFun := f
    map_rel' := by
      intro i j hij
      have h1 : (1 : Fin n).val = 1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      rcases cycleGraph_adj'.mp hij with hij | hji
      · have hi : i = j + 1 := (sub_eq_iff_eq_add').mp (Fin.ext (hij.trans h1.symm))
        simpa only [hi] using (ha j).symm
      · have hj : j = i + 1 := (sub_eq_iff_eq_add').mp (Fin.ext (hji.trans h1.symm))
        simpa only [hj] using ha i
  }
  injective' := hf

/-- The cyclic successor index has exactly the next vertex of a closed walk,
including the final wrap to its first vertex. -/
lemma getVert_cyclic_succ (p : G.Walk u u) [NeZero p.length]
    (hlen : 2 ≤ p.length) (i : Fin p.length) :
    p.getVert (i + 1).val = p.getVert (i.val + 1) := by
  have h1 : (1 : Fin p.length).val = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < p.length)]
  rw [Fin.val_add, h1]
  by_cases hi : i.val + 1 = p.length
  · rw [hi, Nat.mod_self]
    simp
  · rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]

/-- A simple closed walk gives a copy of the cycle with precisely its length. -/
def cycleCopyOfIsCycle (p : G.Walk u u) (hp : p.IsCycle) : CycleCopy p.length G := by
  letI : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  exact cycleCopyOfVertices p.length (by have := hp.three_le_length; omega)
    (fun i => p.getVert i.val)
    (by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn' (by simp; omega) (by simp; omega) hij)
    (by
      intro i
      change G.Adj (p.getVert i.val) (p.getVert (i + 1).val)
      rw [getVert_cyclic_succ p (by have := hp.three_le_length; omega)]
      exact p.adj_getVert_succ i.isLt)

@[simp] theorem cycleCopyOfIsCycle_apply (p : G.Walk u u) (hp : p.IsCycle)
    (i : Fin p.length) : cycleCopyOfIsCycle p hp i = p.getVert i.val := rfl

/-- Any member of a walk's edge list occurs at two consecutive indices. -/
lemma mem_edges_iff_getVert {p : G.Walk u v} {e : Sym2 V} :
    e ∈ p.edges ↔ ∃ i, i < p.length ∧ s(p.getVert i, p.getVert (i + 1)) = e := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    constructor
    · intro he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨0, by simp, by simp [Dart.edge]⟩
      · obtain ⟨i, hi, he⟩ := ih.mp he
        exact ⟨i + 1, by simpa using hi, by simpa using he⟩
    · rintro ⟨i, hi, he⟩
      cases i with
      | zero => exact List.mem_cons.mpr (Or.inl (by simpa using he.symm))
      | succ i =>
        apply List.mem_cons_of_mem
        exact ih.mpr ⟨i, by simpa using hi, by simpa using he⟩

/-- Consecutive cyclic indices are adjacent for every cycle of length at least two. -/
lemma cycleGraph_adj_succ (n : ℕ) [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i + 1) := by
  apply cycleGraph_adj'.mpr
  right
  have h1 : (1 : Fin n).val = 1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  simpa using h1

/-- Every original edge of the exact closed walk is an edge of the resulting
copy. In particular this preserves any designated edges through cycle assembly. -/
theorem exists_copy_edge_of_mem_edges (p : G.Walk u u) (hp : p.IsCycle)
    (e : G.edgeSet) (he : e.val ∈ p.edges) :
    ∃ a : (cycleGraph p.length).edgeSet, (cycleCopyOfIsCycle p hp).mapEdgeSet a = e := by
  letI : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  obtain ⟨i, hi, he⟩ := mem_edges_iff_getVert.mp he
  let j : Fin p.length := ⟨i, hi⟩
  refine ⟨⟨s(j, j + 1), cycleGraph_adj_succ p.length
    (by have := hp.three_le_length; omega) j⟩, ?_⟩
  apply Subtype.ext
  change s(p.getVert j.val, p.getVert (j + 1).val) = e.val
  rw [getVert_cyclic_succ p (by have := hp.three_le_length; omega)]
  exact he

/-- Conversely the edge image of the constructed copy contains no edge beyond
those traversed by the closed walk, even when the host has chords. -/
theorem copy_edge_mem_edges (p : G.Walk u u) (hp : p.IsCycle)
    (a : (cycleGraph p.length).edgeSet) :
    ((cycleCopyOfIsCycle p hp).mapEdgeSet a).val ∈ p.edges := by
  letI : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ i j =>
    have h1 : (1 : Fin p.length).val = 1 := by
      simp [Nat.mod_eq_of_lt (by have := hp.three_le_length; omega : 1 < p.length)]
    change s(p.getVert i.val, p.getVert j.val) ∈ p.edges
    rcases cycleGraph_adj'.mp ha with hij | hji
    · have hi : i = j + 1 := (sub_eq_iff_eq_add').mp (Fin.ext (hij.trans h1.symm))
      rw [hi, getVert_cyclic_succ p (by have := hp.three_le_length; omega)]
      apply mem_edges_iff_getVert.mpr
      exact ⟨j.val, j.isLt, Sym2.eq_swap⟩
    · have hj : j = i + 1 := (sub_eq_iff_eq_add').mp (Fin.ext (hji.trans h1.symm))
      rw [hj, getVert_cyclic_succ p (by have := hp.three_le_length; omega)]
      exact mem_edges_iff_getVert.mpr ⟨i.val, i.isLt, rfl⟩

/-- The map has exactly the original cycle edges as image. -/
theorem range_cycleCopyOfIsCycle_mapEdgeSet (p : G.Walk u u) (hp : p.IsCycle) :
    Set.range (cycleCopyOfIsCycle p hp).mapEdgeSet = {e | e.val ∈ p.edges} := by
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    exact copy_edge_mem_edges p hp a
  · exact exists_copy_edge_of_mem_edges p hp e

/-- Cycle validity separates any two distinct designated original edges of a
simple closed walk of the required exact length. -/
theorem edgeColors_ne_of_isCycle {ℓ : ℕ} (c : G.edgeSet → K)
    (hc : ValidCycleColoring ℓ c) (p : G.Walk u u) (hp : p.IsCycle)
    (hlen : p.length = ℓ) {e f : G.edgeSet}
    (he : e.val ∈ p.edges) (hf : f.val ∈ p.edges) (hne : e ≠ f) : c e ≠ c f := by
  subst ℓ
  obtain ⟨a, ha⟩ := exists_copy_edge_of_mem_edges p hp e he
  obtain ⟨b, hb⟩ := exists_copy_edge_of_mem_edges p hp f hf
  intro hef
  have hab : a = b := hc (cycleCopyOfIsCycle p hp) (by simpa [ha, hb] using hef)
  exact hne (by rw [← ha, ← hb, hab])

/-- A triangle-shortenable path keeps both designated edges and both endpoints.
The support of the short version is contained in that of the long one. -/
structure AdjustablePath (k : ℕ) (e f : G.edgeSet) (u v : V) where
  long : G.Walk u v
  short : G.Walk u v
  long_isPath : long.IsPath
  short_isPath : short.IsPath
  endpoints_ne : u ≠ v
  long_length : long.length = 2 * k - 1
  short_length : short.length = 2 * k - 2
  short_support : short.support ⊆ long.support
  first_long : e.val ∈ long.edges
  second_long : f.val ∈ long.edges
  first_short : e.val ∈ short.edges
  second_short : f.val ∈ short.edges

/-- The two possible closing lengths are matched to the correct exact path.
Both designated original edges retain their colors after closure. -/
theorem AdjustablePath.colors_ne [DecidableEq V] {k : ℕ} (hk : 2 ≤ k)
    {e f : G.edgeSet} (P : AdjustablePath k e f u v)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c)
    (hclose : Source.HasAvoidingPath G v u 2 (pathInterior P.long) ∨
      Source.HasAvoidingPath G v u 3 (pathInterior P.long))
    (hef : e ≠ f) : c e ≠ c f := by
  rcases hclose with ⟨q, hq, hlen, hav⟩ | ⟨q, hq, hlen, hav⟩
  · have hcycle := isCycle_append_of_avoiding_interior P.long_isPath hq hav
      (by rw [P.long_length, hlen]; omega)
    apply edgeColors_ne_of_isCycle c hc _ hcycle
      (by simp [P.long_length, hlen]; omega) _ _ hef
    · simp [Walk.edges_append, P.first_long]
    · simp [Walk.edges_append, P.second_long]
  · have hav' : ∀ x ∈ q.support, x ∉ pathInterior P.short := by
      intro x hx hxi
      exact hav x hx (pathInterior_mono P.short_support hxi)
    have hcycle := isCycle_append_of_avoiding_interior P.short_isPath hq hav'
      (by rw [P.short_length, hlen]; omega)
    apply edgeColors_ne_of_isCycle c hc _ hcycle
      (by simp [P.short_length, hlen]; omega) _ _ hef
    · simp [Walk.edges_append, P.first_short]
    · simp [Walk.edges_append, P.second_short]

/-- A triangle at the start of a path provides the exact adjustable interface.
Both designated edges occur after the triangle, so the shortcut retains them. -/
def AdjustablePath.of_triangle {k : ℕ} (hk : 2 ≤ k) {a b d v : V}
    (hab : G.Adj a b) (hbd : G.Adj b d) (had : G.Adj a d)
    (p : G.Walk d v) (hlong : (p.cons hbd |>.cons hab).IsPath)
    (hlen : p.length = 2 * k - 3) (e f : G.edgeSet)
    (he : e.val ∈ p.edges) (hf : f.val ∈ p.edges) : AdjustablePath k e f a v := by
  have hp := hlong.of_cons.of_cons
  have hap : a ∉ p.support := by
    intro h
    exact (Walk.cons_isPath_iff hab _).mp hlong |>.2 (List.mem_cons_of_mem _ h)
  refine {
    long := p.cons hbd |>.cons hab
    short := p.cons had
    long_isPath := hlong
    short_isPath := hp.cons hap
    endpoints_ne := endpoints_ne_of_isPath hlong (by simp)
    long_length := by simp [hlen]; omega
    short_length := by simp [hlen]; omega
    short_support := ?_
    first_long := by simp [he]
    second_long := by simp [hf]
    first_short := by simp [he]
    second_short := by simp [hf]
  }
  intro x hx
  simp only [Walk.support_cons, List.mem_cons] at hx ⊢
  exact hx.imp_right Or.inr

end Erdos809.LongOddCycles
