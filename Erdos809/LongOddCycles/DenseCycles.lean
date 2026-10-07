module
public import Erdos809.LongOddCycles.CycleCopies

@[expose] public section

/-!
# Two designated edges in a dense common-neighbor graph

This is the auxiliary graph used when the near-case robust connectivity
alternative fails. The proof produces an exact simple cycle before applying
color validity; it does not assume the target host is an induced cycle.
-/

namespace Erdos809.LongOddCycles

open SimpleGraph Source

variable {V K : Type*} {G : SimpleGraph V} {u v : V}

/-- Extend a simple prefix by an exact number of edges, preserving every prefix
edge. The prefix's last vertex is excluded from the greedy forbidden set. -/
theorem exists_path_extension [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (p : G.Walk u v) (hp : p.IsPath) (L : ℕ)
    (hbudget : p.length + L ≤ G.minDegree) :
    ∃ w, ∃ q : G.Walk u w, q.IsPath ∧ q.length = p.length + L ∧ p.edges ⊆ q.edges := by
  let S := p.support.toFinset.erase v
  have hS : S.card = p.length := by
    rw [Finset.card_erase_of_mem (by simp : v ∈ p.support.toFinset),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
    omega
  obtain ⟨w, q, hq, hlen, hav⟩ := exists_greedy_avoiding_path L S v
    (by simp [S]) (by simpa [hS] using hbudget)
  refine ⟨w, p.append q, isPath_append hp hq ?_, by simp [hlen], ?_⟩
  · intro x hxp hxq
    by_contra hxv
    exact hav x hxq (by simp [S, hxp, hxv])
  · intro e he
    simp [Walk.edges_append, he]

/-- A simple path of length `2k-1` closes through a common neighbor avoiding
its interior; the resulting simple cycle retains the whole path. -/
theorem close_path_of_codegree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    (p : G.Walk u v) (hp : p.IsPath) (hlen : p.length = 2 * k - 1) :
    ∃ q : G.Walk u u, q.IsCycle ∧ q.length = 2 * k + 1 ∧ p.edges ⊆ q.edges := by
  have huv : u ≠ v := endpoints_ne_of_isPath hp (by omega)
  obtain ⟨q, hq, hqLen, hav⟩ := hasAvoidingPath_two_of_codegree (G := G) huv.symm
    (F := pathInterior p)
    (by rw [card_pathInterior hp huv, hlen]; have := hcodeg v u huv.symm; omega)
    (end_not_mem_pathInterior p) (start_not_mem_pathInterior p)
  refine ⟨p.append q, isCycle_append_of_avoiding_interior hp hq hav
    (by rw [hlen, hqLen]; omega), by simp [hlen, hqLen]; omega, ?_⟩
  intro e he
  simp [Walk.edges_append, he]

/-- Extend a designated simple prefix, then close it by a fresh common neighbor. -/
theorem cycle_through_prefix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    (p : G.Walk u v) (hp : p.IsPath) (hlen : p.length ≤ 2 * k - 1) :
    ∃ q : G.Walk u u, q.IsCycle ∧ q.length = 2 * k + 1 ∧ p.edges ⊆ q.edges := by
  obtain ⟨w, q, hq, hqlen, hsub⟩ := exists_path_extension p hp
    (2 * k - 1 - p.length) (by omega)
  obtain ⟨r, hr, hrlen, hsub'⟩ := close_path_of_codegree hk hcodeg q hq (by omega)
  exact ⟨r, hr, hrlen, List.Subset.trans hsub hsub'⟩

/-- Any pair of distinct adjacent edges lies on an exact odd cycle under the
dense auxiliary graph hypotheses. -/
theorem cycle_through_adjacent_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    {a b d : V} (hab : G.Adj a b) (had : G.Adj a d) (hbd : b ≠ d) :
    ∃ p : G.Walk b b, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(a, d) ∈ p.edges := by
  let q : G.Walk b d := .cons hab.symm (.cons had .nil)
  have hq : q.IsPath := by
    simp [q, Walk.isPath_def, hab.ne.symm, had.ne, hbd]
  obtain ⟨p, hp, hlen, hsub⟩ := cycle_through_prefix hk hdegree hcodeg q hq (by
    simp [q]; omega)
  exact ⟨p, hp, hlen, hsub (by simp [q, Sym2.eq_swap]), hsub (by simp [q])⟩

/-- Disjoint designated edges are joined using one fresh common neighbor,
then the same greedy-extension and closure interface. -/
theorem cycle_through_disjoint_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    {a b d e : V} (hab : G.Adj a b) (hde : G.Adj d e)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) :
    ∃ p : G.Walk b b, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(d, e) ∈ p.edges := by
  have hcard : ({b, e} : Finset V).card < (G.neighborFinset a ∩ G.neighborFinset d).card := by
    have := hcodeg a d had
    have : ({b, e} : Finset V).card ≤ 2 := by
      simpa using Finset.card_insert_le b ({e} : Finset V)
    omega
  have hnot : ¬G.neighborFinset a ∩ G.neighborFinset d ⊆ {b, e} := fun h =>
    (Finset.card_le_card h).not_gt hcard
  obtain ⟨x, hx, hxf⟩ := Finset.not_subset.mp hnot
  have hax : G.Adj a x := (G.mem_neighborFinset a x).mp (Finset.mem_inter.mp hx).1
  have hdx : G.Adj d x := (G.mem_neighborFinset d x).mp (Finset.mem_inter.mp hx).2
  have hxb : x ≠ b := fun h => hxf (by simp [h])
  have hxe : x ≠ e := fun h => hxf (by simp [h])
  let q : G.Walk b e := .cons hab.symm (.cons hax (.cons hdx.symm (.cons hde .nil)))
  have hq : q.IsPath := by
    simp [q, Walk.isPath_def, hab.ne.symm, had, hae, hbd, hbe, hax.ne,
      hdx.ne.symm, hde.ne, hxb.symm, hxe]
  obtain ⟨p, hp, hlen, hsub⟩ := cycle_through_prefix (by omega) hdegree hcodeg q hq (by
    simp [q]; omega)
  exact ⟨p, hp, hlen, hsub (by simp [q, Sym2.eq_swap]), hsub (by simp [q])⟩

/-- Named endpoints may occur in either orientation; all four possible shared
endpoints reduce to the adjacent-edge construction. -/
theorem cycle_through_named_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    {a b d e : V} (hab : G.Adj a b) (hde : G.Adj d e)
    (hne : s(a, b) ≠ s(d, e)) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(d, e) ∈ p.edges := by
  by_cases had : a = d
  · subst d
    have hbe : b ≠ e := by intro h; subst e; exact hne rfl
    obtain ⟨p, hp, hl, he, hf⟩ := cycle_through_adjacent_edges
      (by omega) hdegree hcodeg hab hde hbe
    exact ⟨b, p, hp, hl, he, hf⟩
  by_cases hae : a = e
  · subst e
    have hbd : b ≠ d := by intro h; subst d; exact hne Sym2.eq_swap
    obtain ⟨p, hp, hl, he, hf⟩ := cycle_through_adjacent_edges
      (by omega) hdegree hcodeg hab hde.symm hbd
    exact ⟨b, p, hp, hl, he, by simpa only [Sym2.eq_swap] using hf⟩
  by_cases hbd : b = d
  · subst d
    have hae : a ≠ e := by intro h; subst e; exact hne Sym2.eq_swap
    obtain ⟨p, hp, hl, he, hf⟩ := cycle_through_adjacent_edges
      (by omega) hdegree hcodeg hab.symm hde hae
    exact ⟨a, p, hp, hl, by simpa only [Sym2.eq_swap] using he, hf⟩
  by_cases hbe : b = e
  · subst e
    have had : a ≠ d := by intro h; subst d; exact hne rfl
    obtain ⟨p, hp, hl, he, hf⟩ := cycle_through_adjacent_edges
      (by omega) hdegree hcodeg hab.symm hde.symm had
    exact ⟨a, p, hp, hl, by simpa only [Sym2.eq_swap] using he,
      by simpa only [Sym2.eq_swap] using hf⟩
  obtain ⟨p, hp, hl, he, hf⟩ := cycle_through_disjoint_edges hk hdegree hcodeg
    hab hde had hae hbd hbe
  exact ⟨b, p, hp, hl, he, hf⟩

/-- Every pair of distinct graph edges is covered by an exact simple odd cycle.
The bound `2k-1` is sufficient, hence in particular the BCM auxiliary `10k` bound. -/
theorem cycle_through_two_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    (e f : G.edgeSet) (hne : e ≠ f) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      e.val ∈ p.edges ∧ f.val ∈ p.edges := by
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction f using Sym2.inductionOn with
    | _ d e =>
      exact cycle_through_named_edges hk hdegree hcodeg he hf
        (fun h => hne (Subtype.ext h))

/-- In the dense auxiliary graph, any coloring valid on the required cycle
must assign distinct colors to every graph edge. -/
theorem color_injective_of_codegree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hcodeg : ∀ x y : V, x ≠ y →
      2 * k - 1 ≤ (G.neighborFinset x ∩ G.neighborFinset y).card)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    Function.Injective c := by
  intro e f hef
  by_contra hne
  obtain ⟨u, p, hp, hlen, he, hf⟩ := cycle_through_two_edges hk hdegree hcodeg e f hne
  exact edgeColors_ne_of_isCycle c hc p hp hlen he hf hne hef

end Erdos809.LongOddCycles
