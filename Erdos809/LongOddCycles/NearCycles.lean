module
public import Erdos809.LongOddCycles.FarCycles

@[expose] public section

/-!
# Adjustable cycles in the near case

A robust two-or-three-path closes the appropriate member of a pair of paths
whose lengths differ by one. Both designated edges survive every shortcut.
-/

namespace Erdos809.LongOddCycles

open SimpleGraph Source

variable {V K : Type*} {G : SimpleGraph V} {u v : V}

/-- Robust connectivity used only in the successful branch of the near-case
connectivity-or-palette alternative. Endpoints are distinct and excluded from F. -/
def RobustTwoOrThree (G : SimpleGraph V) (b : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ b → ∀ x y : V, x ≠ y → x ∉ F → y ∉ F →
    HasAvoidingPath G x y 2 F ∨ HasAvoidingPath G x y 3 F

/-- An adjustable prefix of any affordable length can be extended to the exact
long and short lengths. The same greedy tail is appended to both versions. -/
theorem extend_adjustable_prefix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    {e f : G.edgeSet} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hshort : q.length + 1 = p.length) (hlen : p.length ≤ 2 * k - 1)
    (hsub : q.support ⊆ p.support)
    (he : e.val ∈ p.edges) (hf : f.val ∈ p.edges)
    (he' : e.val ∈ q.edges) (hf' : f.val ∈ q.edges) :
    ∃ w, Nonempty (AdjustablePath k e f u w) := by
  let S := p.support.toFinset.erase v
  have hS : S.card = p.length := by
    rw [Finset.card_erase_of_mem (by simp : v ∈ p.support.toFinset),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
    omega
  obtain ⟨w, r, hr, hrlen, hav⟩ := exists_greedy_avoiding_path (G := G)
    (2 * k - 1 - p.length) S v (by simp [S]) (by rw [hS]; omega)
  have hpinter : ∀ x, x ∈ p.support → x ∈ r.support → x = v := by
    intro x hxp hxr
    by_contra hxv
    exact hav x hxr (by simp [S, hxp, hxv])
  have hqinter : ∀ x, x ∈ q.support → x ∈ r.support → x = v :=
    fun x hxq hxr => hpinter x (hsub hxq) hxr
  have hpl : (p.append r).length = 2 * k - 1 := by simp [hrlen]; omega
  refine ⟨w, ⟨{
    long := p.append r
    short := q.append r
    long_isPath := isPath_append hp hr hpinter
    short_isPath := isPath_append hq hr hqinter
    endpoints_ne := endpoints_ne_of_isPath (isPath_append hp hr hpinter) (by omega)
    long_length := hpl
    short_length := by simp [hrlen]; omega
    short_support := ?_
    first_long := by simp [Walk.edges_append, he]
    second_long := by simp [Walk.edges_append, hf]
    first_short := by simp [Walk.edges_append, he']
    second_short := by simp [Walk.edges_append, hf']
  }⟩⟩
  intro x hx
  simp only [Walk.support_append, List.mem_append] at hx ⊢
  exact hx.imp_left (fun hxq => hsub hxq)

/-- A shortenable prefix already suffices for separating its two designated
edge colors under robust near-case connectivity. -/
theorem colors_ne_of_adjustable_prefix [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {e f : G.edgeSet} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hshort : q.length + 1 = p.length) (hlen : p.length ≤ 2 * k - 1)
    (hsub : q.support ⊆ p.support)
    (he : e.val ∈ p.edges) (hf : f.val ∈ p.edges)
    (he' : e.val ∈ q.edges) (hf' : f.val ∈ q.edges)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c)
    (hef : e ≠ f) : c e ≠ c f := by
  obtain ⟨w, ⟨P⟩⟩ := extend_adjustable_prefix (by omega) hdegree p q hp hq
    hshort hlen hsub he hf he' hf'
  apply P.colors_ne (by omega) c hc _ hef
  apply hrobust (pathInterior P.long)
    (by rw [card_pathInterior P.long_isPath P.endpoints_ne, P.long_length]; omega)
    w u P.endpoints_ne.symm (end_not_mem_pathInterior _) (start_not_mem_pathInterior _)

/-- Any finite forbidden set smaller than a common-neighbor pool admits a
fresh common neighbor, with both adjacencies retained. -/
lemma exists_commonNeighbor_outside [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (a b : V) (F : Finset V)
    (hcard : F.card < (G.neighborFinset a ∩ G.neighborFinset b).card) :
    ∃ r, G.Adj a r ∧ G.Adj b r ∧ r ∉ F := by
  have hnot : ¬G.neighborFinset a ∩ G.neighborFinset b ⊆ F := fun h =>
    (Finset.card_le_card h).not_gt hcard
  obtain ⟨r, hr, hrF⟩ := Finset.not_subset.mp hnot
  exact ⟨r, (G.mem_neighborFinset a r).mp (Finset.mem_inter.mp hr).1,
    (G.mem_neighborFinset b r).mp (Finset.mem_inter.mp hr).2, hrF⟩

/-- The adjacent good-edge recipe. Its prefix has length six or seven, so at
k=4 the three-path branch uses a zero-length greedy extension. -/
theorem near_colors_adjacent [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b x y z : V} (hab : G.Adj a b)
    (hbook : 5 < (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    c ⟨s(x, y), hxy⟩ ≠ c ⟨s(x, z), hxz⟩ := by
  obtain ⟨r, har, hbr, hrF⟩ := exists_commonNeighbor_outside (G := G) a b {x, y, z} (by
    have hcard : ({x, y, z} : Finset V).card ≤ 3 := by
      have h1 := Finset.card_insert_le x ({y, z} : Finset V)
      have h2 := Finset.card_insert_le y ({z} : Finset V)
      simp only [Finset.card_singleton] at h2
      omega
    omega)
  have hrx : r ≠ x := fun h => hrF (by simp [h])
  have hry : r ≠ y := fun h => hrF (by simp [h])
  have hrz : r ≠ z := fun h => hrF (by simp [h])
  let F : Finset V := {x, y, b, r}
  have hF : F.card ≤ 5 * k := by
    have h1 := Finset.card_insert_le x ({y, b, r} : Finset V)
    have h2 := Finset.card_insert_le y ({b, r} : Finset V)
    have h3 := Finset.card_insert_le b ({r} : Finset V)
    simp only [Finset.card_singleton] at h3
    dsimp [F]
    omega
  obtain ⟨P, hP, hPlen, hav⟩ : ∃ P : G.Walk a z,
      P.IsPath ∧ P.length ≤ 3 ∧ ∀ w ∈ P.support, w ∉ F := by
    rcases hrobust F hF a z hza.symm
      (by simp [F, hxa.symm, hya.symm, hab.ne, har.ne])
      (by simp [F, hxz.ne.symm, hyz.symm, hzb, hrz.symm]) with
      ⟨P, hp, hl, hav⟩ | ⟨P, hp, hl, hav⟩
    · exact ⟨P, hp, by omega, hav⟩
    · exact ⟨P, hp, by omega, hav⟩
  have hxP : x ∉ P.support := fun h => hav x h (by simp [F])
  have hyP : y ∉ P.support := fun h => hav y h (by simp [F])
  have hbP : b ∉ P.support := fun h => hav b h (by simp [F])
  have hrP : r ∉ P.support := fun h => hav r h (by simp [F])
  let tail : G.Walk a y := (P.concat hxz.symm).concat hxy
  have htail : tail.IsPath := (hP.concat hxP hxz.symm).concat (by
    simp [Walk.support_concat, hyP, hxy.ne.symm]) hxy
  have hbTail : b ∉ tail.support := by
    simp [tail, Walk.support_concat, hbP, hxb.symm, hyb.symm]
  have hrTail : r ∉ tail.support := by
    simp [tail, Walk.support_concat, hrP, hrx, hry]
  let long : G.Walk r y := (tail.cons hab.symm).cons hbr.symm
  let short : G.Walk r y := tail.cons har.symm
  apply colors_ne_of_adjustable_prefix hk hdegree hrobust long short
    ((htail.cons hbTail).cons (by simp [hrTail, hbr.ne.symm])) (htail.cons hrTail)
    (by simp [long, short]) (by simp [long, tail]; omega) ?_
    (by simp [long, tail, Walk.edges_concat])
    (by simp [long, tail, Walk.edges_concat, Sym2.eq_swap])
    (by simp [short, tail, Walk.edges_concat])
    (by simp [short, tail, Walk.edges_concat, Sym2.eq_swap]) c hc ?_
  · intro w hw
    simp only [long, short, Walk.support_cons, List.mem_cons] at hw ⊢
    exact hw.imp_right Or.inr
  · intro heq
    have heq' := congrArg Subtype.val heq
    have : y = z := by simpa [hxz.ne] using heq'
    exact hyz this

/-- The disjoint-edge recipe when the opposite endpoints have a fresh common
neighbor. The long prefix has seven edges; its extension is zero at k=4. -/
theorem near_colors_common [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b x y z w t : V} (hab : G.Adj a b)
    (hbook : 5 < (G.neighborFinset a ∩ G.neighborFinset b).card)
    (haz : G.Adj a z) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (hyt : G.Adj y t) (hwt : G.Adj w t)
    (hta : t ≠ a) (htb : t ≠ b) (htx : t ≠ x) (htz : t ≠ z)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    c ⟨s(x, y), hxy⟩ ≠ c ⟨s(z, w), hzw⟩ := by
  obtain ⟨r, har, hbr, hrF⟩ := exists_commonNeighbor_outside (G := G) a b {x, y, z, w, t} (by
    have h1 := Finset.card_insert_le x ({y, z, w, t} : Finset V)
    have h2 := Finset.card_insert_le y ({z, w, t} : Finset V)
    have h3 := Finset.card_insert_le z ({w, t} : Finset V)
    have h4 := Finset.card_insert_le w ({t} : Finset V)
    simp only [Finset.card_singleton] at h4
    omega)
  have hrx : r ≠ x := fun h => hrF (by simp [h])
  have hry : r ≠ y := fun h => hrF (by simp [h])
  have hrz : r ≠ z := fun h => hrF (by simp [h])
  have hrw : r ≠ w := fun h => hrF (by simp [h])
  have hrt : r ≠ t := fun h => hrF (by simp [h])
  let long : G.Walk r x := .cons hbr.symm (.cons hab.symm (.cons haz
    (.cons hzw (.cons hwt (.cons hyt.symm (.cons hxy.symm .nil))))))
  let short : G.Walk r x := .cons har.symm (.cons haz
    (.cons hzw (.cons hwt (.cons hyt.symm (.cons hxy.symm .nil)))))
  have hlong : long.IsPath := by
    have := hab.ne; have := hxy.ne; have := hzw.ne; have := hyt.ne
    have := hwt.ne; have := har.ne; have := hbr.ne
    simp_all [long, Walk.isPath_def, ne_comm]
  have hshort : short.IsPath := by
    have := hxy.ne; have := hzw.ne; have := hyt.ne; have := hwt.ne; have := har.ne
    simp_all [short, Walk.isPath_def, ne_comm]
  apply colors_ne_of_adjustable_prefix hk hdegree hrobust long short hlong hshort
    (by simp [long, short]) (by simp [long]; omega) ?_
    (by simp [long, Sym2.eq_swap]) (by simp [long])
    (by simp [short, Sym2.eq_swap]) (by simp [short]) c hc ?_
  · intro v hv
    simp only [long, short, Walk.support_cons, List.mem_cons] at hv ⊢
    tauto
  · intro heq
    have := congrArg Subtype.val heq
    simp [hxz, hxw] at this

/-- The disjoint-edge recipe when a book vertex is adjacent to one opposite
endpoint. Its internal triangle is shortened while both end edges survive. -/
theorem near_colors_book_neighbor [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b x y z w r : V} (hab : G.Adj a b)
    (haz : G.Adj a z) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (har : G.Adj a r) (hbr : G.Adj b r) (hryAdj : G.Adj r y)
    (hrx : r ≠ x) (hry : r ≠ y) (hrz : r ≠ z) (hrw : r ≠ w)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    c ⟨s(x, y), hxy⟩ ≠ c ⟨s(z, w), hzw⟩ := by
  let long : G.Walk w x := .cons hzw.symm (.cons haz.symm (.cons hab
    (.cons hbr (.cons hryAdj (.cons hxy.symm .nil)))))
  let short : G.Walk w x := .cons hzw.symm (.cons haz.symm
    (.cons har (.cons hryAdj (.cons hxy.symm .nil))))
  have hlong : long.IsPath := by
    have := hab.ne; have := hxy.ne; have := hzw.ne; have := har.ne; have := hbr.ne
    simp_all [long, Walk.isPath_def, ne_comm]
  have hshort : short.IsPath := by
    have := hxy.ne; have := hzw.ne; have := har.ne
    simp_all [short, Walk.isPath_def, ne_comm]
  apply colors_ne_of_adjustable_prefix hk hdegree hrobust long short hlong hshort
    (by simp [long, short]) (by simp [long]; omega) ?_
    (by simp [long, Sym2.eq_swap]) (by simp [long, Sym2.eq_swap])
    (by simp [short, Sym2.eq_swap]) (by simp [short, Sym2.eq_swap]) c hc ?_
  · intro v hv
    simp only [long, short, Walk.support_cons, List.mem_cons] at hv ⊢
    tauto
  · intro heq
    have := congrArg Subtype.val heq
    simp [hxz, hxw] at this

/-- The two disjoint-edge recipes cover all possibilities. The book-cover
hypothesis is used exactly when the opposite common-neighbor set is small. -/
theorem near_colors_disjoint [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b x y z w : V} (hab : G.Adj a b)
    (hbook : 5 < (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hcover : ∀ y w : V, (G.neighborFinset y ∩ G.neighborFinset w).card ≤ 4 →
      (Finset.univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card + 4 <
        (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hax : G.Adj a x) (haz : G.Adj a z) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    c ⟨s(x, y), hxy⟩ ≠ c ⟨s(z, w), hzw⟩ := by
  by_cases hcommon : ∃ t, G.Adj y t ∧ G.Adj w t ∧ t ∉ ({a, b, x, z} : Finset V)
  · obtain ⟨t, hyt, hwt, ht⟩ := hcommon
    apply near_colors_common hk hdegree hrobust hab hbook haz hxy hzw
      hxz hxw hyz hyw hxa hxb hya hyb hza hzb hwa hwb hyt hwt
      (fun h => ht (by simp [h])) (fun h => ht (by simp [h]))
      (fun h => ht (by simp [h])) (fun h => ht (by simp [h])) c hc
  have hsmall : (G.neighborFinset y ∩ G.neighborFinset w).card ≤ 4 := by
    have hsub : G.neighborFinset y ∩ G.neighborFinset w ⊆ {a, b, x, z} := by
      intro t ht
      by_contra htf
      exact hcommon ⟨t, (G.mem_neighborFinset y t).mp (Finset.mem_inter.mp ht).1,
        (G.mem_neighborFinset w t).mp (Finset.mem_inter.mp ht).2, htf⟩
    have hcard := Finset.card_le_card hsub
    have h1 := Finset.card_insert_le a ({b, x, z} : Finset V)
    have h2 := Finset.card_insert_le b ({x, z} : Finset V)
    have h3 := Finset.card_insert_le x ({z} : Finset V)
    simp only [Finset.card_singleton] at h3
    omega
  let D := Finset.univ \ (G.neighborFinset y ∪ G.neighborFinset w)
  let F := D ∪ {x, y, z, w}
  obtain ⟨r, har, hbr, hrF⟩ := exists_commonNeighbor_outside (G := G) a b F (by
    have h1 := Finset.card_insert_le x ({y, z, w} : Finset V)
    have h2 := Finset.card_insert_le y ({z, w} : Finset V)
    have h3 := Finset.card_insert_le z ({w} : Finset V)
    simp only [Finset.card_singleton] at h3
    have h4 := Finset.card_union_le D ({x, y, z, w} : Finset V)
    have h5 := hcover y w hsmall
    change (D ∪ {x, y, z, w}).card < _
    change D.card + 4 < _ at h5
    omega)
  have hrx : r ≠ x := fun h => hrF (by simp [F, h])
  have hry : r ≠ y := fun h => hrF (by simp [F, h])
  have hrz : r ≠ z := fun h => hrF (by simp [F, h])
  have hrw : r ≠ w := fun h => hrF (by simp [F, h])
  have hradj : G.Adj y r ∨ G.Adj w r := by
    have hrD : r ∉ D := fun h => hrF (Finset.mem_union_left _ h)
    have hrD' : ¬G.Adj y r → G.Adj w r := by simpa [D] using hrD
    tauto
  rcases hradj with hyr | hwr
  · exact near_colors_book_neighbor hk hdegree hrobust hab haz hxy hzw
      hxz hxw hyz hyw hxa hxb hya hyb hza hzb hwa hwb har hbr hyr.symm
      hrx hry hrz hrw c hc
  · exact (near_colors_book_neighbor hk hdegree hrobust hab hax hzw hxy
      hxz.symm hyz.symm hxw.symm hyw.symm hza hzb hwa hwb hxa hxb hya hyb
      har hbr hwr.symm hrz hrw hrx hry c hc).symm

/-- Adjacent and disjoint cases together separate any two oriented good edges. -/
theorem near_colors_named [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b x y z w : V} (hab : G.Adj a b)
    (hbook : 5 < (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hcover : ∀ y w : V, (G.neighborFinset y ∩ G.neighborFinset w).card ≤ 4 →
      (Finset.univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card + 4 <
        (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hax : G.Adj a x) (haz : G.Adj a z) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) (hwa : w ≠ a) (hwb : w ≠ b)
    (hne : s(x, y) ≠ s(z, w))
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    c ⟨s(x, y), hxy⟩ ≠ c ⟨s(z, w), hzw⟩ := by
  by_cases hxz : x = z
  · subst z
    have hyw : y ≠ w := by intro h; subst w; exact hne rfl
    exact near_colors_adjacent hk hdegree hrobust hab hbook hxy hzw hyw
      hxa hxb hya hyb hwa hwb c hc
  by_cases hxw : x = w
  · subst w
    have hyz : y ≠ z := by intro h; subst z; exact hne Sym2.eq_swap
    have h := near_colors_adjacent hk hdegree hrobust hab hbook hxy hzw.symm hyz
      hxa hxb hya hyb hza hzb c hc
    simpa only [Sym2.eq_swap] using h
  by_cases hyz : y = z
  · subst z
    have hxw : x ≠ w := by intro h; subst w; exact hne Sym2.eq_swap
    have h := near_colors_adjacent hk hdegree hrobust hab hbook hxy.symm hzw hxw
      hya hyb hxa hxb hwa hwb c hc
    simpa only [Sym2.eq_swap] using h
  by_cases hyw : y = w
  · subst w
    have hxz : x ≠ z := by intro h; subst z; exact hne rfl
    have h := near_colors_adjacent hk hdegree hrobust hab hbook hxy.symm hzw.symm hxz
      hya hyb hxa hxb hza hzb c hc
    simpa only [Sym2.eq_swap] using h
  exact near_colors_disjoint hk hdegree hrobust hab hbook hcover hax haz hxy hzw
    hxz hxw hyz hyw hxa hxb hya hyb hza hzb hwa hwb c hc

/-- Orient a good original-host edge from an endpoint in the selected
neighborhood while retaining its exact edge value and endpoint exclusions. -/
lemma orient_good_edge [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (a b : V) (e : G.edgeSet)
    (he : (∃ x ∈ (G.neighborFinset a).erase b, x ∈ e.val) ∧
      a ∉ e.val ∧ b ∉ e.val) :
    ∃ x y, ∃ hxy : G.Adj x y,
      e = ⟨s(x, y), hxy⟩ ∧ G.Adj a x ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨⟨x, hx, hxe⟩, ha, hb⟩ := he
    have hau : u ≠ a := fun h => ha (by simp [← h])
    have hav : v ≠ a := fun h => ha (by simp [← h])
    have hbu : u ≠ b := fun h => hb (by simp [← h])
    have hbv : v ≠ b := fun h => hb (by simp [← h])
    have hax : G.Adj a x := (G.mem_neighborFinset a x).mp (Finset.mem_erase.mp hx).2
    have hxe' : x = u ∨ x = v := by simpa using hxe
    rcases hxe' with rfl | rfl
    · exact ⟨x, v, heG, rfl, hax, hau, hbu, hav, hbv⟩
    · exact ⟨x, u, heG.symm, Subtype.ext Sym2.eq_swap, hax, hav, hbv, hau, hbu⟩

/-- Every pair of good original-host edges has different colors. Good means
incident to `N(a) \ {b}` and incident to neither endpoint of the book edge. -/
theorem near_color_injOn [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {k : ℕ} (hk : 4 ≤ k) (hdegree : 2 * k - 1 ≤ G.minDegree)
    (hrobust : RobustTwoOrThree G (5 * k))
    {a b : V} (hab : G.Adj a b)
    (hbook : 5 < (G.neighborFinset a ∩ G.neighborFinset b).card)
    (hcover : ∀ y w : V, (G.neighborFinset y ∩ G.neighborFinset w).card ≤ 4 →
      (Finset.univ \ (G.neighborFinset y ∪ G.neighborFinset w)).card + 4 <
        (G.neighborFinset a ∩ G.neighborFinset b).card)
    (c : G.edgeSet → K) (hc : ValidCycleColoring (2 * k + 1) c) :
    Set.InjOn c {e | (∃ x ∈ (G.neighborFinset a).erase b, x ∈ e.val) ∧
      a ∉ e.val ∧ b ∉ e.val} := by
  intro e he f hf hef
  by_contra hne
  obtain ⟨x, y, hxy, heq, hax, hxa, hxb, hya, hyb⟩ := orient_good_edge a b e he
  obtain ⟨z, w, hzw, hfq, haz, hza, hzb, hwa, hwb⟩ := orient_good_edge a b f hf
  have hne' : s(x, y) ≠ s(z, w) := by
    intro h
    exact hne (by rw [heq, hfq]; exact Subtype.ext h)
  exact near_colors_named hk hdegree hrobust hab hbook hcover hax haz hxy hzw
    hxa hxb hya hyb hza hzb hwa hwb hne' c hc (by simpa [heq, hfq] using hef)

end Erdos809.LongOddCycles
