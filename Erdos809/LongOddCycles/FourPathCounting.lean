module
public import Erdos809.Source.RobustPaths
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic

@[expose] public section

/-!
# The local obstruction to a simple four-path

The finite-set arguments in this file are the combinatorial portion of BCM
Lemma 3.2.  All neighborhoods refer to the original graph.
-/

namespace Erdos809.LongOddCycles

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Four specified edges form a simple four-path when the six nonconsecutive
vertex pairs are distinct. -/
lemma hasAvoidingPath_four {x a z b y : V}
    (hxa : G.Adj x a) (haz : G.Adj a z) (hzb : G.Adj z b) (hby : G.Adj b y)
    (hxz : x ≠ z) (hxb : x ≠ b) (hxy : x ≠ y)
    (hab : a ≠ b) (hay : a ≠ y) (hzy : z ≠ y) :
    Source.HasAvoidingPath G x y 4 ∅ := by
  refine ⟨.cons hxa (.cons haz (.cons hzb (.cons hby .nil))), ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp [hxa.ne, haz.ne, hzb.ne, hby.ne, hxz, hxb, hxy, hab, hay, hzy]
  · simp

/-- A missing four-path forbids an outside common neighbor between distinct
vertices of the two endpoint neighborhoods. -/
lemma no_four_path_common_neighbor {x y a b z : V} (hxy : x ≠ y)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hxa : G.Adj x a) (hay : a ≠ y)
    (hyb : G.Adj y b) (hbx : b ≠ x) (hab : a ≠ b)
    (hzx : z ≠ x) (hzy : z ≠ y) : ¬ (G.Adj a z ∧ G.Adj b z) := by
  rintro ⟨haz, hbz⟩
  exact hno (hasAvoidingPath_four hxa haz hbz.symm hyb.symm
    hzx.symm hbx.symm hxy hab hay hzy)

/-- Incidence double-counting for the degrees of a vertex set. -/
lemma sum_degrees_eq_sum_neighbor_inter (A : Finset V) :
    ∑ a ∈ A, G.degree a = ∑ z : V, (G.neighborFinset z ∩ A).card := by
  simp_rw [SimpleGraph.degree, Finset.card_eq_sum_ones]
  exact Finset.sum_comm' (by simp [and_comm, SimpleGraph.adj_comm])

/-- The common neighborhood contains at most one neighbor of each vertex
other than the two endpoints when there is no simple four-path. -/
lemma common_neighbor_inter_card_le_one {x y z : V} (hxy : x ≠ y)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅) (hzx : z ≠ x) (hzy : z ≠ y) :
    (G.neighborFinset z ∩ (G.neighborFinset x ∩ G.neighborFinset y)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  by_contra hab
  exact no_four_path_common_neighbor hxy hno ha.2.1 ha.2.2.ne.symm
    hb.2.2 hb.2.1.ne.symm hab hzx hzy ⟨ha.1.symm, hb.1.symm⟩

/-- Double-counting gives the common-neighborhood degree bound used when its
cardinality is at least two (the inequality itself holds without that restriction). -/
lemma sum_degrees_common_neighbors_le {x y : V} (hxy : x ≠ y)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅) :
    (∑ a ∈ G.neighborFinset x ∩ G.neighborFinset y, (G.degree a : ℝ)) ≤
      Fintype.card V - 2 + 2 * (G.neighborFinset x ∩ G.neighborFinset y).card := by
  let A := G.neighborFinset x ∩ G.neighborFinset y
  have hx : G.neighborFinset x ∩ A = A := by ext a; simp [A]
  have hy : G.neighborFinset y ∩ A = A := by ext a; simp [A]
  have hsum := sum_degrees_eq_sum_neighbor_inter (G := G) A
  have hsplit : ∑ z : V, (G.neighborFinset z ∩ A).card =
      (∑ z ∈ (Finset.univ \ {x, y}), (G.neighborFinset z ∩ A).card) + 2 * A.card := by
    have he : (Finset.univ \ {x, y}) ∪ ({x, y} : Finset V) = Finset.univ := by
      ext z; simp; tauto
    calc
      _ = ∑ z ∈ ((Finset.univ \ {x, y}) ∪ ({x, y} : Finset V)),
          (G.neighborFinset z ∩ A).card := congrArg (fun T : Finset V => ∑ z ∈ T, (G.neighborFinset z ∩ A).card) he.symm
      _ = _ := by
        rw [Finset.sum_union Finset.sdiff_disjoint]
        simp [hxy, hx, hy, two_mul]
  have hle : (∑ z ∈ (Finset.univ \ {x, y}), (G.neighborFinset z ∩ A).card) ≤
      (Finset.univ \ ({x, y} : Finset V)).card := by
    calc
      _ ≤ ∑ _z ∈ (Finset.univ \ ({x, y} : Finset V)), 1 := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' : z ≠ x ∧ z ≠ y := by simpa using hz
        exact common_neighbor_inter_card_le_one hxy hno hz'.1 hz'.2
      _ = _ := by simp
  have hcard : (Finset.univ \ ({x, y} : Finset V)).card + 2 = Fintype.card V := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({x, y} : Finset V))
    simpa [hxy] using this
  have hsumR : (∑ a ∈ A, (G.degree a : ℝ)) =
      (∑ z ∈ (Finset.univ \ {x, y}), (G.neighborFinset z ∩ A).card : ℕ) + 2 * (A.card : ℝ) := by
    exact_mod_cast hsum.trans hsplit
  have hleR : ((∑ z ∈ (Finset.univ \ {x, y}), (G.neighborFinset z ∩ A).card : ℕ) : ℝ) ≤
      ((Finset.univ \ ({x, y} : Finset V)).card : ℝ) := by exact_mod_cast hle
  have hcardR : ((Finset.univ \ ({x, y} : Finset V)).card : ℝ) + 2 = Fintype.card V := by
    exact_mod_cast hcard
  dsimp [A] at *
  linarith

/-- Inclusion-exclusion with an explicitly missing set. -/
lemma card_add_card_add_card_le_of_disjoint_union (A B C : Finset V)
    (hdis : Disjoint (A ∪ B) C) :
    A.card + B.card + C.card ≤ Fintype.card V + (A ∩ B).card := by
  have hu := Finset.card_le_univ ((A ∪ B) ∪ C)
  rw [Finset.card_union_of_disjoint hdis] at hu
  have hi := Finset.card_union_add_card_inter A B
  omega

/-- The degree estimate on vertices outside both endpoint neighborhoods in
BCM's partition, including all missing endpoint and diagonal contributions. -/
lemma degree_neither_add_degree_endpoint_le {x y z : V}
    (hxy : G.Adj x y) (horder : G.degree y ≤ G.degree x)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hzx : ¬ G.Adj x z) (hzy : ¬ G.Adj y z) :
    G.degree z + G.degree y + 1 ≤ Fintype.card V := by
  let L := (G.neighborFinset x).erase y
  let R := (G.neighborFinset y).erase x
  have hzxne : z ≠ x := by rintro rfl; exact hzy hxy.symm
  have hzyne : z ≠ y := by rintro rfl; exact hzx hxy
  have hL : L.card + 1 = G.degree x := by
    exact Finset.card_erase_add_one (by simpa using hxy)
  have hR : R.card + 1 = G.degree y := by
    exact Finset.card_erase_add_one (by simpa using hxy.symm)
  have hC : ({x, y, z} : Finset V).card = 3 := by
    simp [hxy.ne, hzxne.symm, hzyne.symm]
  have hdisL : Disjoint (G.neighborFinset z ∪ L) {x, y, z} := by
    apply Finset.disjoint_left.mpr
    intro w hw hwC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwC
    rcases hwC with rfl | rfl | rfl
    · exact hzx (show G.Adj z w from by simpa [L] using hw).symm
    · exact hzy (show G.Adj z w from by simpa [L] using hw).symm
    · simpa [L, hzx] using hw
  have hdisR : Disjoint (G.neighborFinset z ∪ R) {x, y, z} := by
    apply Finset.disjoint_left.mpr
    intro w hw hwC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwC
    rcases hwC with rfl | rfl | rfl
    · exact hzx (show G.Adj z w from by simpa [R] using hw).symm
    · exact hzy (show G.Adj z w from by simpa [R] using hw).symm
    · simpa [R, hzy] using hw
  by_cases hex : ∃ a ∈ L, G.Adj z a
  · obtain ⟨a, ha, hza⟩ := hex
    have hinter : (G.neighborFinset z ∩ R).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b hb c hc
      have hb' : b = a := by
        by_contra hba
        have hxa : G.Adj x a := by simpa [L] using (Finset.mem_erase.mp ha).2
        have hay : a ≠ y := (Finset.mem_erase.mp ha).1
        have hyb : G.Adj y b := by simpa [R] using (Finset.mem_erase.mp (Finset.mem_inter.mp hb).2).2
        have hbx : b ≠ x := (Finset.mem_erase.mp (Finset.mem_inter.mp hb).2).1
        have hzb : G.Adj z b := by simpa using (Finset.mem_inter.mp hb).1
        exact no_four_path_common_neighbor hxy.ne hno hxa hay hyb hbx (Ne.symm hba)
          hzxne hzyne ⟨hza.symm, hzb.symm⟩
      have hc' : c = a := by
        by_contra hca
        have hxa : G.Adj x a := by simpa [L] using (Finset.mem_erase.mp ha).2
        have hay : a ≠ y := (Finset.mem_erase.mp ha).1
        have hyc : G.Adj y c := by simpa [R] using (Finset.mem_erase.mp (Finset.mem_inter.mp hc).2).2
        have hcx : c ≠ x := (Finset.mem_erase.mp (Finset.mem_inter.mp hc).2).1
        have hzc : G.Adj z c := by simpa using (Finset.mem_inter.mp hc).1
        exact no_four_path_common_neighbor hxy.ne hno hxa hay hyc hcx (Ne.symm hca)
          hzxne hzyne ⟨hza.symm, hzc.symm⟩
      exact hb'.trans hc'.symm
    have hcount := card_add_card_add_card_le_of_disjoint_union
      (G.neighborFinset z) R {x, y, z} hdisR
    rw [G.card_neighborFinset_eq_degree, hC] at hcount
    omega
  · have hempty : G.neighborFinset z ∩ L = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hex ⟨a, (Finset.mem_inter.mp ha).2,
        by simpa using (Finset.mem_inter.mp ha).1⟩
    have hcount := card_add_card_add_card_le_of_disjoint_union
      (G.neighborFinset z) L {x, y, z} hdisL
    rw [G.card_neighborFinset_eq_degree, hC, hempty, Finset.card_empty] at hcount
    omega

/-- Opposite exclusive-neighborhood vertices have disjoint neighborhoods
when the endpoint four-path is absent. -/
lemma degree_add_degree_le_of_exclusive_neighbors {x y a b : V}
    (hxy : x ≠ y) (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hxa : G.Adj x a) (hay : a ≠ y) (hya : ¬ G.Adj y a)
    (hyb : G.Adj y b) (hbx : b ≠ x) (hxb : ¬ G.Adj x b) :
    G.degree a + G.degree b ≤ Fintype.card V := by
  have hab : a ≠ b := by rintro rfl; exact hxb hxa
  have hdis : Disjoint (G.neighborFinset a) (G.neighborFinset b) := by
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    have haz : G.Adj a z := by simpa using hza
    have hbz : G.Adj b z := by simpa using hzb
    by_cases hzx : z = x
    · subst z
      exact hxb hbz.symm
    by_cases hzy : z = y
    · subst z
      exact hya haz.symm
    exact no_four_path_common_neighbor hxy hno hxa hay hyb hbx hab hzx hzy ⟨haz, hbz⟩
  simpa only [Finset.card_union_of_disjoint hdis, G.card_neighborFinset_eq_degree]
    using Finset.card_le_univ (G.neighborFinset a ∪ G.neighborFinset b)

/-- An exclusive-neighborhood vertex and a nonadjacent opposite-neighborhood
vertex also have total degree at most the order: their sole possible common
neighbor is paid for by the missing vertex in the union of neighborhoods. -/
lemma degree_add_degree_le_of_nonadjacent_neighbors {x y a b : V}
    (hxy : x ≠ y) (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hxa : G.Adj x a) (hay : a ≠ y) (hya : ¬ G.Adj y a)
    (hyb : G.Adj y b) (hbx : b ≠ x) (hab : a ≠ b) (hnab : ¬ G.Adj a b) :
    G.degree a + G.degree b ≤ Fintype.card V := by
  have hinter : (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
    calc
      _ ≤ ({x} : Finset V).card := Finset.card_le_card (by
        intro z hz
        simp only [Finset.mem_singleton]
        by_contra hzx
        have haz : G.Adj a z := by simpa using (Finset.mem_inter.mp hz).1
        have hbz : G.Adj b z := by simpa using (Finset.mem_inter.mp hz).2
        by_cases hzy : z = y
        · subst z; exact hya haz.symm
        exact no_four_path_common_neighbor hxy hno hxa hay hyb hbx hab hzx hzy ⟨haz, hbz⟩)
      _ = 1 := Finset.card_singleton _
  have hdis : Disjoint (G.neighborFinset a ∪ G.neighborFinset b) {b} := by
    simp [Finset.disjoint_singleton_right, hnab]
  have hcount := card_add_card_add_card_le_of_disjoint_union
    (G.neighborFinset a) (G.neighborFinset b) {b} hdis
  simp only [G.card_neighborFinset_eq_degree, Finset.card_singleton] at hcount
  omega

/-- The singleton common-neighborhood case has a stronger degree bound than
the uniform incidence estimate. -/
lemma degree_common_singleton_add_endpoint_le {x y a : V}
    (hxy : G.Adj x y) (horder : G.degree y ≤ G.degree x)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hunique : ∀ u, G.Adj x u → G.Adj y u → u = a) :
    G.degree a + G.degree y ≤ Fintype.card V + 1 := by
  let L := (G.neighborFinset x).erase y
  let R := (G.neighborFinset y).erase x
  have hL : L.card + 1 = G.degree x :=
    Finset.card_erase_add_one (by simpa using hxy)
  have hR : R.card + 1 = G.degree y :=
    Finset.card_erase_add_one (by simpa using hxy.symm)
  by_cases hex : ∃ u ∈ L, G.Adj a u
  · obtain ⟨u, hu, hau⟩ := hex
    have hdis : Disjoint (G.neighborFinset a) R := by
      apply Finset.disjoint_left.mpr
      intro v hav hv
      have hav' : G.Adj a v := by simpa using hav
      have hvx : v ≠ x := (Finset.mem_erase.mp hv).1
      have hyv : G.Adj y v := by simpa using (Finset.mem_erase.mp hv).2
      have huy : u ≠ y := (Finset.mem_erase.mp hu).1
      have hxu : G.Adj x u := by simpa using (Finset.mem_erase.mp hu).2
      have huv : u ≠ v := by
        rintro rfl
        exact hau.ne (hunique u hxu hyv).symm
      exact no_four_path_common_neighbor hxy.ne hno hxu huy hyv hvx huv
        hxa.ne.symm hya.ne.symm ⟨hau.symm, hav'.symm⟩
    have hcount := Finset.card_le_univ (G.neighborFinset a ∪ R)
    rw [Finset.card_union_of_disjoint hdis, G.card_neighborFinset_eq_degree] at hcount
    omega
  · have hdis : Disjoint (G.neighborFinset a) L := by
      apply Finset.disjoint_left.mpr
      intro u hau hu
      exact hex ⟨u, hu, by simpa using hau⟩
    have hcount := Finset.card_le_univ (G.neighborFinset a ∪ L)
    rw [Finset.card_union_of_disjoint hdis, G.card_neighborFinset_eq_degree] at hcount
    omega

/-- BCM's common-neighborhood estimate with the repaired real degree parameter.
The empty and singleton cases are treated separately, without interpreting a
strict real bound above two as an integer bound of three. -/
lemma sum_degrees_common_neighbors_repaired {x y : V}
    (hxy : G.Adj x y) (horder : G.degree y ≤ G.degree x)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (b : ℝ) (hb : 3 ≤ b) (hbhalf : b ≤ (Fintype.card V : ℝ) / 2)
    (hby : b ≤ (G.degree y : ℝ)) :
    (∑ z ∈ G.neighborFinset x ∩ G.neighborFinset y, (G.degree z : ℝ)) ≤
      ((G.neighborFinset x ∩ G.neighborFinset y).card - 1 : ℝ) * (b - 1) +
        ((Fintype.card V : ℝ) - b) + 3 := by
  let A := G.neighborFinset x ∩ G.neighborFinset y
  by_cases hA0 : A.card = 0
  · have he : A = ∅ := Finset.card_eq_zero.mp hA0
    change (∑ z ∈ A, (G.degree z : ℝ)) ≤ ((A.card : ℝ) - 1) * (b - 1) + ((Fintype.card V : ℝ) - b) + 3
    rw [he]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    linarith
  by_cases hA1 : A.card = 1
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hA1
    have ham : a ∈ A := by rw [ha]; simp
    have ham' : G.Adj x a ∧ G.Adj y a := by simpa [A] using ham
    have hbound := degree_common_singleton_add_endpoint_le hxy horder hno ham'.1 ham'.2
      (fun u hxu hyu => by
        have hu : u ∈ A := by simp [A, hxu, hyu]
        simpa [ha] using hu)
    have hboundR : (G.degree a : ℝ) + G.degree y ≤ (Fintype.card V : ℝ) + 1 := by
      exact_mod_cast hbound
    change (∑ z ∈ A, (G.degree z : ℝ)) ≤ ((A.card : ℝ) - 1) * (b - 1) + ((Fintype.card V : ℝ) - b) + 3
    rw [ha]
    simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, sub_self, zero_mul,
      zero_add]
    linarith
  · have hA2 : (2 : ℝ) ≤ A.card := by exact_mod_cast (show 2 ≤ A.card by omega)
    have hbound := sum_degrees_common_neighbors_le hxy.ne hno
    change (∑ z ∈ A, (G.degree z : ℝ)) ≤ (Fintype.card V : ℝ) - 2 + 2 * A.card at hbound
    change (∑ z ∈ A, (G.degree z : ℝ)) ≤ ((A.card : ℝ) - 1) * (b - 1) + ((Fintype.card V : ℝ) - b) + 3
    nlinarith [mul_nonneg (by linarith : 0 ≤ (A.card : ℝ) - 2) (by linarith : 0 ≤ b - 3)]

/-- Each vertex in the exclusive x-neighborhood has degree at most n-b.
A nonempty opposite exclusive neighborhood supplies the witness directly;
otherwise at least two common neighbors supply a nonadjacent witness. -/
lemma degree_exclusive_le_complement_min_degree {x y a : V}
    (hxy : G.Adj x y) (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (hxa : G.Adj x a) (hay : a ≠ y) (hya : ¬ G.Adj y a)
    (hdy : 3 ≤ G.degree y) (b : ℝ) (hdegree : ∀ v, b ≤ (G.degree v : ℝ)) :
    (G.degree a : ℝ) ≤ (Fintype.card V : ℝ) - b := by
  let R := (G.neighborFinset y).erase x
  have hR : R.card + 1 = G.degree y :=
    Finset.card_erase_add_one (by simpa using hxy.symm)
  by_cases hex : ∃ w ∈ R, ¬ G.Adj x w
  · obtain ⟨w, hw, hxw⟩ := hex
    have hyw : G.Adj y w := by simpa using (Finset.mem_erase.mp hw).2
    have hwx : w ≠ x := (Finset.mem_erase.mp hw).1
    have hcount := degree_add_degree_le_of_exclusive_neighbors hxy.ne hno hxa hay hya hyw hwx hxw
    have hcountR : (G.degree a : ℝ) + G.degree w ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hcount
    have := hdegree w
    linarith
  · have hRsub : R ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
      intro w hw
      have hyw : G.Adj y w := by simpa using (Finset.mem_erase.mp hw).2
      have hxw : G.Adj x w := by by_contra h; exact hex ⟨w, hw, h⟩
      simp [hxw, hyw]
    have hsmall : (G.neighborFinset a ∩ R).card ≤ 1 := by
      exact (Finset.card_le_card (Finset.inter_subset_inter_left hRsub)).trans
        (common_neighbor_inter_card_le_one hxy.ne hno hxa.ne.symm hay)
    have hnot : ¬ R ⊆ G.neighborFinset a := by
      intro hsub
      have he : G.neighborFinset a ∩ R = R := Finset.inter_eq_right.mpr hsub
      rw [he] at hsmall
      omega
    obtain ⟨w, hw, haw⟩ := Finset.not_subset.mp hnot
    have hyw : G.Adj y w := by simpa using (Finset.mem_erase.mp hw).2
    have hwx : w ≠ x := (Finset.mem_erase.mp hw).1
    have haw' : ¬ G.Adj a w := by simpa using haw
    have hane : a ≠ w := by rintro rfl; exact hya hyw
    have hcount := degree_add_degree_le_of_nonadjacent_neighbors hxy.ne hno
      hxa hay hya hyw hwx hane haw'
    have hcountR : (G.degree a : ℝ) + G.degree w ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hcount
    have := hdegree w
    linarith

/- The following partition assembly was produced with Aristotle project
`ec45033d-b277-4d87-9995-a82b886c0752`, then checked locally against the pinned
Lean/mathlib environment and refactored to the independently implemented local
counting lemmas above. -/
/-- BCM Lemma 3.2 finite combinatorial partition estimate. -/
theorem no_four_path_degree_sum_bound {x y : V}
    (hxy : G.Adj x y) (horder : G.degree y ≤ G.degree x)
    (hno : ¬ Source.HasAvoidingPath G x y 4 ∅)
    (b : ℝ) (hb : 3 ≤ b) (hbhalf : b ≤ (Fintype.card V : ℝ) / 2)
    (hdegree : ∀ v, b ≤ (G.degree v : ℝ)) :
    2 * (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ)^2 -
      2*b*((Fintype.card V : ℝ)-b) + 2*((Fintype.card V : ℝ)-b) -
      (Fintype.card V : ℝ) + 4 := by
  -- the partition
  set n := Fintype.card V with hn
  set Nx := G.neighborFinset x with hNx
  set Ny := G.neighborFinset y with hNy
  set A := Nx ∩ Ny with hA
  set X := (Nx \ A).erase y with hX
  set Y := (Ny \ A).erase x with hY
  set S := Finset.univ \ (Nx ∪ Ny) with hS
  have memA : ∀ v, v ∈ A ↔ G.Adj x v ∧ G.Adj y v := by
    intro v; simp [A, Nx, Ny]
  have memX : ∀ v, v ∈ X ↔ G.Adj x v ∧ ¬ G.Adj y v ∧ v ≠ y := by
    intro v; simp [X, A, Nx, Ny]; tauto
  have memY : ∀ v, v ∈ Y ↔ G.Adj y v ∧ ¬ G.Adj x v ∧ v ≠ x := by
    intro v; simp [Y, A, Nx, Ny]; tauto
  have memS : ∀ v, v ∈ S ↔ ¬ G.Adj x v ∧ ¬ G.Adj y v := by
    intro v; simp [S, Nx, Ny]
  have hyNx : y ∈ Nx \ A := by simp [A, Nx, Ny, hxy]
  have hxNy : x ∈ Ny \ A := by simp [A, Nx, Ny, hxy.symm]
  have hANx : A ⊆ Nx := Finset.inter_subset_left
  have hANy : A ⊆ Ny := Finset.inter_subset_right
  have hdx : Nx.card = G.degree x := G.card_neighborFinset_eq_degree x
  have hdy : Ny.card = G.degree y := G.card_neighborFinset_eq_degree y
  -- cardinalities
  have cardX : X.card + A.card + 1 = G.degree x := by
    have h1 : X.card + 1 = (Nx \ A).card := Finset.card_erase_add_one hyNx
    have h2 : (Nx \ A).card + A.card = Nx.card := Finset.card_sdiff_add_card_eq_card hANx
    omega
  have cardY : Y.card + A.card + 1 = G.degree y := by
    have h1 : Y.card + 1 = (Ny \ A).card := Finset.card_erase_add_one hxNy
    have h2 : (Ny \ A).card + A.card = Ny.card := Finset.card_sdiff_add_card_eq_card hANy
    omega
  have cardS : S.card + G.degree x + G.degree y = n + A.card := by
    have h1 : S.card + (Nx ∪ Ny).card = (Finset.univ : Finset V).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Nx ∪ Ny))
    have h2 : (Nx ∪ Ny).card + A.card = Nx.card + Ny.card :=
      Finset.card_union_add_card_inter Nx Ny
    rw [Finset.card_univ] at h1
    omega
  -- the degree sum decomposition
  have hsum : 2 * G.edgeFinset.card = ∑ v ∈ S, G.degree v + G.degree x + G.degree y +
      ∑ v ∈ A, G.degree v + ∑ v ∈ X, G.degree v + ∑ v ∈ Y, G.degree v := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    have h1 : ∑ v ∈ S, G.degree v + ∑ v ∈ Nx ∪ Ny, G.degree v = ∑ v, G.degree v :=
      Finset.sum_sdiff (f := fun v => G.degree v) (Finset.subset_univ (Nx ∪ Ny))
    have h2 : ∑ v ∈ Nx ∪ Ny, G.degree v + ∑ v ∈ A, G.degree v =
        ∑ v ∈ Nx, G.degree v + ∑ v ∈ Ny, G.degree v :=
      Finset.sum_union_inter (f := fun v => G.degree v) (s₁ := Nx) (s₂ := Ny)
    have h3 : ∑ v ∈ Nx \ A, G.degree v + ∑ v ∈ A, G.degree v = ∑ v ∈ Nx, G.degree v :=
      Finset.sum_sdiff (f := fun v => G.degree v) hANx
    have h4 : ∑ v ∈ Ny \ A, G.degree v + ∑ v ∈ A, G.degree v = ∑ v ∈ Ny, G.degree v :=
      Finset.sum_sdiff (f := fun v => G.degree v) hANy
    have h5 : G.degree y + ∑ v ∈ X, G.degree v = ∑ v ∈ Nx \ A, G.degree v :=
      Finset.add_sum_erase (Nx \ A) (fun v => G.degree v) hyNx
    have h6 : G.degree x + ∑ v ∈ Y, G.degree v = ∑ v ∈ Ny \ A, G.degree v :=
      Finset.add_sum_erase (Ny \ A) (fun v => G.degree v) hxNy
    omega
  -- real-valued parameters
  have hdyb : b ≤ (G.degree y : ℝ) := hdegree y
  have hXY : Y.card ≤ X.card := by omega
  -- estimate for S
  have estS : ∑ v ∈ S, (G.degree v : ℝ) ≤ S.card * (n - G.degree y - 1) := by
    have := Finset.sum_le_card_nsmul S (fun v => (G.degree v : ℝ))
      ((n : ℝ) - G.degree y - 1) (by
        intro z hz
        rw [memS] at hz
        have hzx : z ≠ x := by rintro rfl; exact hz.2 hxy.symm
        have hzy : z ≠ y := by rintro rfl; exact hz.1 hxy
        have := degree_neither_add_degree_endpoint_le hxy horder hno hz.1 hz.2
        have : ((G.degree z + G.degree y + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
        push_cast at this
        linarith)
    simpa [nsmul_eq_mul] using this
  -- estimate for A
  have estA : ∑ v ∈ A, (G.degree v : ℝ) ≤ (A.card - 1) * (b - 1) + (n - b) + 3 := by
    exact sum_degrees_common_neighbors_repaired hxy horder hno b hb hbhalf hdyb
  -- estimate for X and Y
  have estXY : ∑ v ∈ X, (G.degree v : ℝ) + ∑ v ∈ Y, (G.degree v : ℝ) ≤
      ((G.degree x : ℝ) - G.degree y) * (n - b) + ((G.degree y : ℝ) - A.card - 1) * n := by
    have cX : (X.card : ℝ) + A.card + 1 = G.degree x := by exact_mod_cast cardX
    have cY : (Y.card : ℝ) + A.card + 1 = G.degree y := by exact_mod_cast cardY
    rcases X.eq_empty_or_nonempty with hXe | hXne
    · have hYe : Y = ∅ := by
        rw [← Finset.card_eq_zero]
        have := Finset.card_eq_zero.mpr hXe
        omega
      rw [hXe, hYe] at *
      simp only [Finset.sum_empty] at *
      nlinarith
    · obtain ⟨z₀, hz₀X, hz₀max⟩ := Finset.exists_max_image X (fun v => G.degree v) hXne
      have hz₀ := (memX z₀).mp hz₀X
      have hsX : ∑ v ∈ X, (G.degree v : ℝ) ≤ X.card * G.degree z₀ := by
        have := Finset.sum_le_card_nsmul X (fun v => (G.degree v : ℝ)) (G.degree z₀ : ℝ)
          (fun v hv => by
            change (G.degree v : ℝ) ≤ _
            exact_mod_cast hz₀max v hv)
        simpa [nsmul_eq_mul] using this
      have hsY : ∑ v ∈ Y, (G.degree v : ℝ) ≤ Y.card * ((n : ℝ) - G.degree z₀) := by
        have := Finset.sum_le_card_nsmul Y (fun v => (G.degree v : ℝ)) ((n : ℝ) - G.degree z₀)
          (by
            intro w hw
            rw [memY] at hw
            have h := degree_add_degree_le_of_exclusive_neighbors hxy.ne hno hz₀.1 hz₀.2.2 hz₀.2.1
              hw.1 hw.2.2 hw.2.1
            have : ((G.degree z₀ + G.degree w : ℕ) : ℝ) ≤ n := by exact_mod_cast h
            push_cast at this
            linarith)
        simpa [nsmul_eq_mul] using this
      have hmax : (G.degree z₀ : ℝ) ≤ n - b := by
        apply degree_exclusive_le_complement_min_degree hxy hno hz₀.1 hz₀.2.2 hz₀.2.1
        · exact_mod_cast (show (3 : ℝ) ≤ G.degree y from le_trans hb hdyb)
        · exact hdegree
      have hXYr : (Y.card : ℝ) ≤ X.card := by exact_mod_cast hXY
      nlinarith [mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hXYr)]
  -- assembly
  have hsumR : 2 * (G.edgeFinset.card : ℝ) = ∑ v ∈ S, (G.degree v : ℝ) + G.degree x +
      G.degree y + ∑ v ∈ A, (G.degree v : ℝ) + ∑ v ∈ X, (G.degree v : ℝ) +
      ∑ v ∈ Y, (G.degree v : ℝ) := by
    exact_mod_cast hsum
  have cS : (S.card : ℝ) + G.degree x + G.degree y = n + A.card := by exact_mod_cast cardS
  have cY : (Y.card : ℝ) + A.card + 1 = G.degree y := by exact_mod_cast cardY
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hn2b : 0 ≤ (n : ℝ) - 2 * b := by linarith
  rw [hsumR]
  nlinarith [mul_nonneg hS0 (show (0 : ℝ) ≤ G.degree y - b + 2 by linarith),
    mul_nonneg (sub_nonneg.mpr hdyb) hn2b]


end Erdos809.LongOddCycles
