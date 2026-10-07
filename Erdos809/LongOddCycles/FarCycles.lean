module
public import Erdos809.LongOddCycles.DenseCycles

@[expose] public section

/-!
# Far-case exact cycles through a short-connected core

Shortest connectors are minimized between the two full endpoint sets. Their
opposite endpoints are therefore excluded from the connector support. A greedy
extension preserves both designated edges and a robust four-path closes it.
-/

namespace Erdos809.LongOddCycles

open SimpleGraph Source

variable {V K : Type*} {G : SimpleGraph V} {u v : V}

/-- A shortest connector meets either prescribed endpoint set only at its
respective endpoint. This statement allows intersecting sets and length zero. -/
theorem exists_shortest_connector [DecidableEq V] (S T : Set V) (L : ℕ)
    (hconn : ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ L) :
    ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ L ∧
      (∀ z ∈ S, z ∈ p.support → z = x) ∧
      (∀ z ∈ T, z ∈ p.support → z = y) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ x ∈ S, ∃ y ∈ T, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have hex : ∃ n, P n := by
    obtain ⟨x, hx, y, hy, p, hp, _⟩ := hconn
    exact ⟨p.length, x, hx, y, hy, p, hp, rfl⟩
  obtain ⟨x, hx, y, hy, p, hp, hlen⟩ := Nat.find_spec hex
  have hbound : Nat.find hex ≤ L := by
    obtain ⟨a, ha, b, hb, q, hq, hqLen⟩ := hconn
    exact (Nat.find_min' hex ⟨a, ha, b, hb, q, hq, rfl⟩).trans hqLen
  refine ⟨x, hx, y, hy, p, hp, by omega, ?_, ?_⟩
  · intro z hz hzp
    by_contra hzx
    have hmin : Nat.find hex ≤ (p.dropUntil z hzp).length :=
      Nat.find_min' hex ⟨z, hz, y, hy, p.dropUntil z hzp, hp.dropUntil hzp, rfl⟩
    have hpos : 0 < (p.takeUntil z hzp).length := by
      apply Nat.pos_of_ne_zero
      intro heq
      exact hzx (Walk.eq_of_length_eq_zero heq).symm
    have hsum := congrArg Walk.length (p.take_spec hzp)
    simp only [Walk.length_append] at hsum
    omega
  · intro z hz hzp
    by_contra hzy
    have hmin : Nat.find hex ≤ (p.takeUntil z hzp).length :=
      Nat.find_min' hex ⟨x, hx, z, hz, p.takeUntil z hzp, hp.takeUntil hzp, rfl⟩
    have hlt := p.length_takeUntil_lt hzp hzy
    omega

/-- A four-path robust against deletion closes every short enough prefix after
an exact greedy extension. The internal forbidden set has size `2k-4`. -/
theorem cycle_through_prefix_four [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    (p : G.Walk u v) (hp : p.IsPath) (hlen : p.length ≤ 2 * k - 3) :
    ∃ q : G.Walk u u, q.IsCycle ∧ q.length = 2 * k + 1 ∧ p.edges ⊆ q.edges := by
  obtain ⟨w, q, hq, hqlen, hsub⟩ := exists_path_extension p hp
    (2 * k - 3 - p.length) (by omega)
  have hqlen' : q.length = 2 * k - 3 := by omega
  have huw : u ≠ w := endpoints_ne_of_isPath hq (by omega)
  obtain ⟨r, hr, hrlen, hav⟩ := hrobust w u huw.symm (pathInterior q)
    (by rw [card_pathInterior hq huw, hqlen']; omega)
    (end_not_mem_pathInterior q) (start_not_mem_pathInterior q)
  refine ⟨q.append r, isCycle_append_of_avoiding_interior hq hr hav
    (by rw [hqlen', hrlen]; omega), by simp [hqlen', hrlen]; omega, ?_⟩
  intro e he
  simpa only [Walk.edges_append] using List.mem_append.mpr (Or.inl (hsub he))

/-- The adjacent-edge case has a connector of length zero and a two-edge prefix. -/
theorem far_cycle_adjacent [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    {a b d : V} (hab : G.Adj a b) (had : G.Adj a d) (hbd : b ≠ d) :
    ∃ p : G.Walk b b, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(a, d) ∈ p.edges := by
  let q : G.Walk b d := .cons hab.symm (.cons had .nil)
  have hq : q.IsPath := by
    simp [q, Walk.isPath_def, hab.ne.symm, had.ne, hbd]
  obtain ⟨p, hp, hlen, hsub⟩ := cycle_through_prefix_four hk hdegree hrobust q hq (by
    simp [q]; omega)
  exact ⟨p, hp, hlen, hsub (by simp [q, Sym2.eq_swap]), hsub (by simp [q])⟩

/-- Orient an edge from a chosen member of its full endpoint set. -/
lemma orient_edge {a b x : V} (hab : G.Adj a b) (hx : x = a ∨ x = b) :
    ∃ y, (y = a ∨ y = b) ∧ G.Adj x y ∧ s(x, y) = s(a, b) := by
  rcases hx with rfl | rfl
  · exact ⟨b, Or.inr rfl, hab, rfl⟩
  · exact ⟨a, Or.inl rfl, hab.symm, Sym2.eq_swap⟩

/-- Disjoint edges touching a short-connected core have a simple prefix of
length at most five containing both, hence close after an affordable extension. -/
theorem far_cycle_disjoint [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    (A : Set V) (hcore : ∀ x ∈ A, ∀ y ∈ A,
      ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3)
    {a b d e : V} (hab : G.Adj a b) (hde : G.Adj d e)
    (ha : a ∈ A ∨ b ∈ A) (hd : d ∈ A ∨ e ∈ A)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(d, e) ∈ p.edges := by
  obtain ⟨x₀, hx₀, hxA⟩ : ∃ x, (x = a ∨ x = b) ∧ x ∈ A := by
    rcases ha with ha | hb
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr rfl, hb⟩
  obtain ⟨z₀, hz₀, hzA⟩ : ∃ z, (z = d ∨ z = e) ∧ z ∈ A := by
    rcases hd with hd | he
    · exact ⟨d, Or.inl rfl, hd⟩
    · exact ⟨e, Or.inr rfl, he⟩
  obtain ⟨p₀, hp₀, hp₀len⟩ := hcore x₀ hxA z₀ hzA
  obtain ⟨x, hx, z, hz, p, hp, hplen, hleft, hright⟩ :=
    exists_shortest_connector (G := G) {a, b} {d, e} 3
      ⟨x₀, by simpa using hx₀, z₀, by simpa using hz₀, p₀, hp₀, hp₀len⟩
  obtain ⟨y, hy, hxy, hedge⟩ := orient_edge hab (by simpa using hx)
  obtain ⟨w, hw, hzw, hfedge⟩ := orient_edge hde (by simpa using hz)
  have hyp : y ∉ p.support := fun hym => hxy.ne (hleft y (by simpa using hy) hym).symm
  have hwp : w ∉ p.support := fun hwm => hzw.ne (hright w (by simpa using hw) hwm).symm
  have hyw : y ≠ w := by
    rcases hy with rfl | rfl <;> rcases hw with rfl | rfl <;> assumption
  let q : G.Walk y w := (p.cons hxy.symm).concat hzw
  have hq : q.IsPath := (hp.cons hyp).concat (by simp [hwp, hyw.symm]) hzw
  obtain ⟨r, hr, hrlen, hsub⟩ := cycle_through_prefix_four hk hdegree hrobust q hq (by
    simp only [q, Walk.length_concat, Walk.length_cons]; omega)
  refine ⟨y, r, hr, hrlen, hsub ?_, hsub ?_⟩
  · simp [q, Walk.edges_concat, ← hedge, Sym2.eq_swap]
  · simp [q, Walk.edges_concat, ← hfedge]

/-- Every pair of distinct named edges touching the core is covered, regardless
of their orientation or any common endpoint. -/
theorem far_cycle_named_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    (A : Set V) (hcore : ∀ x ∈ A, ∀ y ∈ A,
      ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3)
    {a b d e : V} (hab : G.Adj a b) (hde : G.Adj d e)
    (ha : a ∈ A ∨ b ∈ A) (hd : d ∈ A ∨ e ∈ A)
    (hne : s(a, b) ≠ s(d, e)) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      s(a, b) ∈ p.edges ∧ s(d, e) ∈ p.edges := by
  by_cases had : a = d
  · subst d
    have hbe : b ≠ e := by intro h; subst e; exact hne rfl
    obtain ⟨p, hp, hl, he, hf⟩ := far_cycle_adjacent hk hdegree hrobust hab hde hbe
    exact ⟨b, p, hp, hl, he, hf⟩
  by_cases hae : a = e
  · subst e
    have hbd : b ≠ d := by intro h; subst d; exact hne Sym2.eq_swap
    obtain ⟨p, hp, hl, he, hf⟩ := far_cycle_adjacent hk hdegree hrobust hab hde.symm hbd
    exact ⟨b, p, hp, hl, he, by simpa only [Sym2.eq_swap] using hf⟩
  by_cases hbd : b = d
  · subst d
    have hae : a ≠ e := by intro h; subst e; exact hne Sym2.eq_swap
    obtain ⟨p, hp, hl, he, hf⟩ := far_cycle_adjacent hk hdegree hrobust hab.symm hde hae
    exact ⟨a, p, hp, hl, by simpa only [Sym2.eq_swap] using he, hf⟩
  by_cases hbe : b = e
  · subst e
    have had : a ≠ d := by intro h; subst d; exact hne rfl
    obtain ⟨p, hp, hl, he, hf⟩ := far_cycle_adjacent hk hdegree hrobust hab.symm hde.symm had
    exact ⟨a, p, hp, hl, by simpa only [Sym2.eq_swap] using he,
      by simpa only [Sym2.eq_swap] using hf⟩
  exact far_cycle_disjoint hk hdegree hrobust A hcore hab hde ha hd had hae hbd hbe

/-- Every two distinct edges touching the short-connected core have an exact
simple odd-cycle witness in the original host. -/
theorem far_cycle_core_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    (A : Set V) (hcore : ∀ x ∈ A, ∀ y ∈ A,
      ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3)
    (e f : G.edgeSet) (he : ∃ x ∈ A, x ∈ e.val) (hf : ∃ x ∈ A, x ∈ f.val)
    (hne : e ≠ f) :
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 2 * k + 1 ∧
      e.val ∈ p.edges ∧ f.val ∈ p.edges := by
  rcases e with ⟨e, heG⟩
  rcases f with ⟨f, hfG⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction f using Sym2.inductionOn with
    | _ d e =>
      apply far_cycle_named_edges hk hdegree hrobust A hcore heG hfG
      · obtain ⟨x, hx, hxm⟩ := he
        have hx' : x = a ∨ x = b := by simpa using hxm
        rcases hx' with hxa | hxb
        · exact Or.inl (hxa ▸ hx)
        · exact Or.inr (hxb ▸ hx)
      · obtain ⟨x, hx, hxm⟩ := hf
        have hx' : x = d ∨ x = e := by simpa using hxm
        rcases hx' with hxd | hxe
        · exact Or.inl (hxd ▸ hx)
        · exact Or.inr (hxe ▸ hx)
      · exact fun h => hne (Subtype.ext h)

/-- All original-host edges incident with the short-connected core have
pairwise different colors under the required odd-cycle validity. -/
theorem far_color_injOn [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 3 ≤ G.minDegree)
    (hrobust : ∀ x y : V, x ≠ y → ∀ S : Finset V, S.card ≤ 2 * k - 4 →
      x ∉ S → y ∉ S → HasAvoidingPath G x y 4 S)
    (A : Set V) (hcore : ∀ x ∈ A, ∀ y ∈ A,
      ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    Set.InjOn c {e | ∃ x ∈ A, x ∈ e.val} := by
  intro e he f hf hef
  by_contra hne
  obtain ⟨u, p, hp, hlen, he, hf⟩ :=
    far_cycle_core_edges hk hdegree hrobust A hcore e f he hf hne
  exact edgeColors_ne_of_isCycle c hc p hp hlen he hf hne hef

end Erdos809.LongOddCycles
