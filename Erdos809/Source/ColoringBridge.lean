/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Definitions
import Erdos809.Compatibility
import Erdos809.Source.RobustPaths
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# Original color classes and full retained-host compatibility

Every color inequality is certified by a seven-distinct-vertex copy in the
original graph. Retained walks may repeat vertices and need not be source paths.
-/

namespace Erdos809.Source

open SimpleGraph

variable {V K : Type*} {G H : SimpleGraph V}

/-- Evaluate a source coloring on an unordered edge with named endpoints. -/
def edgeColor (c : G.edgeSet → K) {u v : V} (h : G.Adj u v) : K := c ⟨s(u,v), h⟩

@[simp] theorem edgeColor_symm (c : G.edgeSet → K) {u v : V} (h : G.Adj u v) :
    edgeColor c h.symm = edgeColor c h := by simp [edgeColor, Sym2.eq_swap]

/-- Consecutive edges on seven distinct vertices define a non-induced C7 copy. -/
def sevenCycleCopy (f : Fin 7 → V) (hf : Function.Injective f)
    (ha : ∀ i : Fin 7, G.Adj (f i) (f (i+1))) : C7Copy G where
  toHom := {
    toFun := f
    map_rel' := by
      intro i j hij
      rw [cycleGraph_adj] at hij
      rcases hij with hij | hji
      · have hi : i = j+1 := (sub_eq_iff_eq_add').mp hij
        simpa only [hi] using (ha j).symm
      · have hj : j = i+1 := (sub_eq_iff_eq_add').mp hji
        simpa only [hj] using ha i
  }
  injective' := hf

/-- Distinct edges of an actual source seven-cycle must have distinct labels. -/
theorem edgeColor_ne_of_copy (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    (F : C7Copy G) {i j k l : Fin 7} (hij : (cycleGraph 7).Adj i j)
    (hkl : (cycleGraph 7).Adj k l) (hne : s(i,j) ≠ s(k,l)) :
    edgeColor c (F.toHom.map_rel hij) ≠ edgeColor c (F.toHom.map_rel hkl) := by
  intro heq
  have he : (⟨s(i,j), hij⟩ : (cycleGraph 7).edgeSet) = ⟨s(k,l), hkl⟩ := hc F heq
  exact hne (congrArg Subtype.val he)

/-- A simple five-path avoiding a wedge center forces the wedge colors apart. -/
theorem wedge_colors_ne_of_fivePath (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hpath : HasAvoidingPath G v w 5 {u}) : edgeColor c huv ≠ edgeColor c huw := by
  classical
  obtain ⟨p, hp, hlen, hav⟩ := hpath
  let f : Fin 7 → V := Fin.cons u (fun i : Fin 6 ↦ p.getVert i.val)
  have hf : Function.Injective f := by
    apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      exact hav _ (p.getVert_mem_support i.val) (by simpa only [Finset.mem_singleton] using hi)
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hij
  have hend : p.getVert 5 = w := by simpa only [hlen] using p.getVert_length
  have ha : ∀ i : Fin 7, G.Adj (f i) (f (i+1)) := by
    intro i
    fin_cases i
    · change G.Adj u (p.getVert 0)
      simpa only [Walk.getVert_zero] using huv
    · exact p.adj_getVert_succ (i := 0) (by omega)
    · exact p.adj_getVert_succ (i := 1) (by omega)
    · exact p.adj_getVert_succ (i := 2) (by omega)
    · exact p.adj_getVert_succ (i := 3) (by omega)
    · exact p.adj_getVert_succ (i := 4) (by omega)
    · change G.Adj (p.getVert 5) u
      simpa only [hend] using huw.symm
  have hn := edgeColor_ne_of_copy c hc (sevenCycleCopy f hf ha)
    (show (cycleGraph 7).Adj 0 1 by decide)
    (show (cycleGraph 7).Adj 0 6 by decide) (by decide)
  change c ⟨s(u, p.getVert 0), _⟩ ≠ c ⟨s(u, p.getVert 5), _⟩ at hn
  simpa only [Walk.getVert_zero, hend, edgeColor] using hn

/-- A vertex of the retained graph lies on a triangle. -/
def OnTriangle (H : SimpleGraph V) (u : V) : Prop :=
  ∃ a b, H.Adj u a ∧ H.Adj a b ∧ H.Adj b u

/-- Triangle at any of the three wedge vertices supplies a retained five-walk.
The displayed walks may repeat vertices, exactly as allowed by robust lifting. -/
theorem fiveWalk_of_wedge_triangle {u v w : V} (huv : H.Adj u v) (huw : H.Adj u w)
    (ht : OnTriangle H u ∨ OnTriangle H v ∨ OnTriangle H w) :
    ∃ p : H.Walk v w, p.length = 5 := by
  rcases ht with ⟨a, b, hua, hab, hbu⟩ | ⟨a, b, hva, hab, hbv⟩ | ⟨a, b, hwa, hab, hbw⟩
  · exact ⟨.cons huv.symm (.cons hua (.cons hab (.cons hbu (.cons huw .nil)))), rfl⟩
  · exact ⟨.cons hva (.cons hab (.cons hbv (.cons huv.symm (.cons huw .nil)))), rfl⟩
  · exact ⟨.cons huv.symm (.cons huw (.cons hwa (.cons hab (.cons hbw .nil)))), rfl⟩

/-- A monochromatic retained wedge has all three vertices outside all retained
triangles. No properness assumption is made on the original coloring. -/
theorem sameColor_wedge_trianglefree (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr : RobustAtLength G H 5 5)
    {u v w : V} (huv : H.Adj u v) (huw : H.Adj u w) (hvw : v ≠ w)
    (hcolor : edgeColor c (hHG huv) = edgeColor c (hHG huw)) :
    ¬ OnTriangle H u ∧ ¬ OnTriangle H v ∧ ¬ OnTriangle H w := by
  classical
  have hnone : ¬ (OnTriangle H u ∨ OnTriangle H v ∨ OnTriangle H w) := by
    intro ht
    have hp := hr hvw (fiveWalk_of_wedge_triangle huv huw ht) {u}
      (by simp) (by simpa using huv.ne.symm) (by simpa using huw.ne.symm)
    exact wedge_colors_ne_of_fivePath c hc (hHG huv) (hHG huw) hp hcolor
  exact ⟨fun h ↦ hnone (Or.inl h), fun h ↦ hnone (Or.inr (Or.inl h)),
    fun h ↦ hnone (Or.inr (Or.inr h))⟩

/-- On edges outside S, an original color has at most one edge at every vertex. -/
theorem sameColor_outside_wedge_leaves_eq (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr : RobustAtLength G H 5 5)
    {u v w : V} (huv : H.Adj u v) (huw : H.Adj u w)
    (hout : OnTriangle H u ∨ OnTriangle H v)
    (hcolor : edgeColor c (hHG huv) = edgeColor c (hHG huw)) : v = w := by
  by_contra hne
  obtain ⟨hu, hv, _⟩ := sameColor_wedge_trianglefree hHG c hc hr huv huw hne hcolor
  exact hout.elim hu hv

/-- Disjoint simple two- and three-paths, together with two connecting edges,
form a seven-cycle in the source and force those connecting edge colors apart. -/
theorem edge_colors_ne_of_twoThreePaths (c : G.edgeSet → K) (hc : ValidC7Coloring c)
    {a b x y : V} (hab : G.Adj a b) (hxy : G.Adj x y)
    (p : G.Walk a x) (hp : p.IsPath) (hplen : p.length = 2)
    (q : G.Walk b y) (hq : q.IsPath) (hqlen : q.length = 3)
    (hdis : ∀ z ∈ q.support, z ∉ p.support) :
    edgeColor c hab ≠ edgeColor c hxy := by
  let f : Fin 7 → V := Fin.append (fun i : Fin 4 ↦ q.getVert i.val)
    (fun i : Fin 3 ↦ p.reverse.getVert i.val)
  have hf : Function.Injective f := by
    apply Fin.append_injective_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact hq.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hij
    · intro i j hij
      apply Fin.ext
      exact hp.reverse.getVert_injOn (by simp only [Set.mem_setOf_eq, Walk.length_reverse]; omega)
        (by simp only [Set.mem_setOf_eq, Walk.length_reverse]; omega) hij
    · intro i j hij
      apply hdis _ (q.getVert_mem_support i.val)
      rw [hij]
      simpa only [Walk.support_reverse, List.mem_reverse] using
        p.reverse.getVert_mem_support j.val
  have hendp : p.reverse.getVert 2 = a := by
    simpa only [Walk.length_reverse, hplen] using p.reverse.getVert_length
  have hendq : q.getVert 3 = y := by simpa only [hqlen] using q.getVert_length
  have ha : ∀ i : Fin 7, G.Adj (f i) (f (i+1)) := by
    intro i
    fin_cases i
    · exact q.adj_getVert_succ (i := 0) (by omega)
    · exact q.adj_getVert_succ (i := 1) (by omega)
    · exact q.adj_getVert_succ (i := 2) (by omega)
    · change G.Adj (q.getVert 3) (p.reverse.getVert 0)
      simpa only [hendq, Walk.getVert_zero] using hxy.symm
    · exact p.reverse.adj_getVert_succ (i := 0) (by simp only [Walk.length_reverse, hplen]; decide)
    · exact p.reverse.adj_getVert_succ (i := 1) (by simp only [Walk.length_reverse, hplen]; decide)
    · change G.Adj (p.reverse.getVert 2) (q.getVert 0)
      simpa only [hendp, Walk.getVert_zero] using hab
  have hn := edgeColor_ne_of_copy c hc (sevenCycleCopy f hf ha)
    (show (cycleGraph 7).Adj 6 0 by decide)
    (show (cycleGraph 7).Adj 4 3 by decide) (by decide)
  change c ⟨s(p.reverse.getVert 2, q.getVert 0), _⟩ ≠
    c ⟨s(p.reverse.getVert 0, q.getVert 3), _⟩ at hn
  simpa only [Walk.getVert_zero, hendp, hendq, edgeColor] using hn

/-- Robust lifting is applied twice, forbidding both other endpoints first and
all three actual vertices of the first path second. -/
theorem edge_colors_ne_of_complementary_walks (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) {a b x y : V}
    (hab : H.Adj a b) (hxy : H.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (h2 : Walk2 H a x) (h3 : Walk3 H b y) :
    edgeColor c (hHG hab) ≠ edgeColor c (hHG hxy) := by
  classical
  obtain ⟨z, haz, hzx⟩ := h2
  obtain ⟨t, r, hbt, htr, hry⟩ := h3
  have hp2 : ∃ p : H.Walk a x, p.length = 2 := ⟨.cons haz (.cons hzx .nil), rfl⟩
  have hp3 : ∃ q : H.Walk b y, q.length = 3 := ⟨.cons hbt (.cons htr (.cons hry .nil)), rfl⟩
  obtain ⟨p, hp, hplen, hav⟩ := hr2 hax hp2 {b,y}
    (by simp [hby]) (by simp [hab.ne, hay]) (by simp [hbx.symm, hxy.ne])
  have hF : p.support.toFinset.card ≤ 5 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hplen]
    decide
  have hbF : b ∉ p.support.toFinset := by
    intro hb
    exact hav b (List.mem_toFinset.mp hb) (by simp)
  have hyF : y ∉ p.support.toFinset := by
    intro hy
    exact hav y (List.mem_toFinset.mp hy) (by simp)
  obtain ⟨q, hq, hqlen, hqav⟩ := hr3 hby hp3 p.support.toFinset hF hbF hyF
  exact edge_colors_ne_of_twoThreePaths c hc (hHG hab) (hHG hxy)
    p hp hplen q hq hqlen (fun z hz hzp ↦ hqav z hz (List.mem_toFinset.mpr hzp))

/-- Equal colors on disjoint retained edges imply all four full-host 23
compatibility exclusions. The paths certifying a forbidden pair live in G. -/
theorem sameColor_disjoint_compatible (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) {a b x y : V}
    (hab : H.Adj a b) (hxy : H.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hcolor : edgeColor c (hHG hab) = edgeColor c (hHG hxy)) :
    Compatible H a b x y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h2, h3⟩
    exact edge_colors_ne_of_complementary_walks hHG c hc hr2 hr3 hab hxy
      hax hay hbx hby h2 h3 hcolor
  · rintro ⟨h2, h3⟩
    apply edge_colors_ne_of_complementary_walks hHG c hc hr2 hr3 hab hxy.symm
      hay hax hby hbx h2 h3
    simpa only [edgeColor, Sym2.eq_swap] using hcolor
  · rintro ⟨h2, h3⟩
    apply edge_colors_ne_of_complementary_walks hHG c hc hr2 hr3 hab.symm hxy
      hbx hby hax hay h2 h3
    simpa only [edgeColor, Sym2.eq_swap] using hcolor
  · rintro ⟨h2, h3⟩
    apply edge_colors_ne_of_complementary_walks hHG c hc hr2 hr3 hab.symm hxy.symm
      hby hbx hay hax h2 h3
    simpa only [edgeColor, Sym2.eq_swap] using hcolor

private theorem outside_sameColor_first_endpoints_ne (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr : RobustAtLength G H 5 5)
    {a b x y : V} (hab : H.Adj a b) (hxy : H.Adj x y)
    (hout : OnTriangle H a ∨ OnTriangle H b) (hne : s(a,b) ≠ s(x,y))
    (hcolor : edgeColor c (hHG hab) = edgeColor c (hHG hxy)) : a ≠ x := by
  intro h
  subst x
  have hb := sameColor_outside_wedge_leaves_eq hHG c hc hr hab hxy hout hcolor
  exact hne (by rw [hb])

/-- Every original color restricted to outside-S edges is a matching.
Only the first edge needs the outside-S hypothesis for this pairwise result. -/
theorem sameColor_outside_edges_disjoint (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr : RobustAtLength G H 5 5)
    {a b x y : V} (hab : H.Adj a b) (hxy : H.Adj x y)
    (hout : OnTriangle H a ∨ OnTriangle H b) (hne : s(a,b) ≠ s(x,y))
    (hcolor : edgeColor c (hHG hab) = edgeColor c (hHG hxy)) :
    a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y := by
  refine ⟨outside_sameColor_first_endpoints_ne hHG c hc hr hab hxy hout hne hcolor,
    ?_, ?_, ?_⟩
  · apply outside_sameColor_first_endpoints_ne hHG c hc hr hab hxy.symm hout
    · simpa only [Sym2.eq_swap] using hne
    · simpa only [edgeColor, Sym2.eq_swap] using hcolor
  · apply outside_sameColor_first_endpoints_ne hHG c hc hr hab.symm hxy hout.symm
    · simpa only [Sym2.eq_swap] using hne
    · simpa only [edgeColor, Sym2.eq_swap] using hcolor
  · apply outside_sameColor_first_endpoints_ne hHG c hc hr hab.symm hxy.symm hout.symm
    · simpa only [Sym2.eq_swap] using hne
    · simpa only [edgeColor, Sym2.eq_swap] using hcolor

/-- The inherited original color classes on E(H) outside S satisfy precisely
the matching and full-host compatibility inputs of the finite theorem. -/
theorem sameColor_outside_pattern (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) (hr5 : RobustAtLength G H 5 5)
    {a b x y : V} (hab : H.Adj a b) (hxy : H.Adj x y)
    (hout : OnTriangle H a ∨ OnTriangle H b) (hne : s(a,b) ≠ s(x,y))
    (hcolor : edgeColor c (hHG hab) = edgeColor c (hHG hxy)) :
    (a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y) ∧ Compatible H a b x y := by
  obtain ⟨hax, hay, hbx, hby⟩ := sameColor_outside_edges_disjoint hHG c hc hr5
    hab hxy hout hne hcolor
  exact ⟨⟨hax, hay, hbx, hby⟩, sameColor_disjoint_compatible hHG c hc hr2 hr3 hab hxy hax hay hbx hby hcolor⟩

end Erdos809.Source
