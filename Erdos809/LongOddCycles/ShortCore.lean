import Erdos809.LongOddCycles.ScalarBounds
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The strict-density specialization of BCM Lemma 3.1. The short connections
are in the original host, not necessarily in the induced graph on the core. -/

noncomputable section
namespace Erdos809.LongOddCycles
open SimpleGraph Finset

private def ShortConnection {V : Type*} (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ p : G.Walk x y, p.length ≤ 3

private lemma ShortConnection.symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : ShortConnection G x y) : ShortConnection G y x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

private lemma ShortConnection.refl {V : Type*} (G : SimpleGraph V) (x : V) :
    ShortConnection G x x := ⟨.nil, by simp⟩

private def closedNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  insert x (G.neighborFinset x)

private lemma closedNeighbors_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (closedNeighbors G x).card = G.degree x + 1 := by
  simp [closedNeighbors]

private lemma closedNeighbors_walk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hy : y ∈ closedNeighbors G x) : ∃ p : G.Walk x y, p.length ≤ 1 := by
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact ⟨.nil, by simp⟩
  · exact ⟨.cons (G.mem_neighborFinset x y |>.mp hy) .nil, by simp⟩

private lemma closedNeighbors_short {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {y z : V}
    (hy : y ∈ closedNeighbors G x) (hz : z ∈ closedNeighbors G x) :
    ShortConnection G y z := by
  obtain ⟨p, hp⟩ := closedNeighbors_walk G hy
  obtain ⟨q, hq⟩ := closedNeighbors_walk G hz
  exact ⟨p.reverse.append q, by simp only [Walk.length_append, Walk.length_reverse]; omega⟩

private lemma bad_pair_separation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hbad : ¬ShortConnection G x y) :
    Disjoint (closedNeighbors G x) (closedNeighbors G y) ∧
      ∀ u ∈ closedNeighbors G x, ∀ v ∈ closedNeighbors G y, ¬G.Adj u v := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    obtain ⟨p, hp⟩ := closedNeighbors_walk G hz1
    obtain ⟨q, hq⟩ := closedNeighbors_walk G hz2
    apply hbad
    exact ⟨p.append q.reverse, by simp only [Walk.length_append, Walk.length_reverse]; omega⟩
  · intro u hu v hv huv
    obtain ⟨p, hp⟩ := closedNeighbors_walk G hu
    obtain ⟨q, hq⟩ := closedNeighbors_walk G hv
    apply hbad
    exact ⟨p.append (.cons huv q.reverse), by
      simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse]; omega⟩

private lemma degree_add_forbidden_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (B : Finset V)
    (hv : v ∉ B) (hB : ∀ w ∈ B, ¬G.Adj v w) :
    G.degree v + B.card + 1 ≤ Fintype.card V := by
  have hd : Disjoint (G.neighborFinset v) (insert v B) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have hadj := G.mem_neighborFinset v w |>.mp hw
    rcases mem_insert.mp hw' with rfl | hw'
    · exact hadj.ne rfl
    · exact hB w hw' hadj
  have hc := Finset.card_le_card (Finset.subset_univ (G.neighborFinset v ∪ insert v B))
  rw [Finset.card_union_of_disjoint hd, Finset.card_insert_of_notMem hv,
    G.card_neighborFinset_eq_degree, Finset.card_univ] at hc
  omega

private lemma shortCore_degree_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private lemma shortCore_edge_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  have h := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ =>
    show (G.degree v : ℝ) ≤ Fintype.card V by exact_mod_cast (G.degree_lt_card_verts v).le)
  rw [shortCore_degree_sum G] at h
  simp only [sum_const, card_univ, nsmul_eq_mul] at h
  nlinarith

private lemma exists_max_bad_pair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbad : ∃ x y, ¬ShortConnection G x y) :
    ∃ x y, ¬ShortConnection G x y ∧ G.degree x ≤ G.degree y ∧
      ∀ u v, ¬ShortConnection G u v →
        min (G.degree u) (G.degree v) ≤ G.degree x := by
  classical
  let P : Finset (V × V) := univ.filter (fun p => ¬ShortConnection G p.1 p.2)
  have hP : P.Nonempty := by
    obtain ⟨x, y, hxy⟩ := hbad
    exact ⟨(x, y), by simp [P, hxy]⟩
  obtain ⟨p, hp, hmax⟩ := P.exists_max_image
    (fun p => min (G.degree p.1) (G.degree p.2)) hP
  have hxy : ¬ShortConnection G p.1 p.2 := (mem_filter.mp hp).2
  have hmax' : ∀ u v, ¬ShortConnection G u v →
      min (G.degree u) (G.degree v) ≤ min (G.degree p.1) (G.degree p.2) := by
    intro u v huv
    exact hmax (u, v) (by simp [P, huv])
  by_cases hord : G.degree p.1 ≤ G.degree p.2
  · refine ⟨p.1, p.2, hxy, hord, ?_⟩
    simpa only [min_eq_left hord] using hmax'
  · refine ⟨p.2, p.1, fun h => hxy h.symm, by omega, ?_⟩
    simpa only [min_eq_right (show G.degree p.2 ≤ G.degree p.1 by omega)] using hmax'

private lemma shortCore_partition_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (Δ X : ℝ)
    (hA : ∀ v ∈ A, (G.degree v : ℝ) ≤ Δ)
    (hB : ∀ v, v ∉ A → (G.degree v : ℝ) ≤ X) :
    2 * (G.edgeFinset.card : ℝ) ≤
      (A.card : ℝ) * Δ + ((Fintype.card V : ℝ) - A.card) * X := by
  have hp : ∀ v, (G.degree v : ℝ) ≤ X + (if v ∈ A then Δ - X else 0) := by
    intro v
    by_cases hv : v ∈ A
    · simp only [hv, if_true]
      linarith [hA v hv]
    · simp only [hv, if_false, add_zero]
      exact hB v hv
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  rw [shortCore_degree_sum G] at hsum
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    ← Finset.sum_filter] at hsum
  simp only [filter_mem_eq_inter, univ_inter] at hsum
  nlinarith

private lemma bad_pair_degree_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (hbad : ¬ShortConnection G x y) (hord : G.degree x ≤ G.degree y) :
    let S := univ \ (closedNeighbors G x ∪ closedNeighbors G y)
    0 ≤ (Fintype.card V : ℝ) - 2 * G.degree x - 2 ∧
    (S.card : ℝ) ≤ (Fintype.card V : ℝ) - 2 * G.degree x - 2 ∧
    ∀ v, v ∉ S → (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) - G.degree x - 2 := by
  classical
  let S := univ \ (closedNeighbors G x ∪ closedNeighbors G y)
  change 0 ≤ (Fintype.card V : ℝ) - 2 * G.degree x - 2 ∧
    (S.card : ℝ) ≤ (Fintype.card V : ℝ) - 2 * G.degree x - 2 ∧ _
  obtain ⟨hdis, hcross⟩ := bad_pair_separation G hbad
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (closedNeighbors G x ∪ closedNeighbors G y))
  rw [card_union_of_disjoint hdis, closedNeighbors_card G x,
    closedNeighbors_card G y, card_univ] at hcard
  have hcardR : (S.card : ℝ) + G.degree x + G.degree y + 2 = Fintype.card V := by
    dsimp [S]
    exact_mod_cast (by omega :
      (univ \ (closedNeighbors G x ∪ closedNeighbors G y)).card + G.degree x + G.degree y + 2 = Fintype.card V)
  have hordR : (G.degree x : ℝ) ≤ G.degree y := by exact_mod_cast hord
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, ?_⟩
  intro v hv
  have hvD : v ∈ closedNeighbors G x ∪ closedNeighbors G y := by
    by_contra hnot
    apply hv
    exact mem_sdiff.mpr ⟨mem_univ _, hnot⟩
  rcases mem_union.mp hvD with hvx | hvy
  · have hvnot : v ∉ closedNeighbors G y := fun hvy => (disjoint_left.mp hdis) hvx hvy
    have hdegree := degree_add_forbidden_le G v (closedNeighbors G y) hvnot
      (fun w hw => hcross v hvx w hw)
    rw [closedNeighbors_card G y] at hdegree
    have hdegreeR : (G.degree v : ℝ) + (G.degree y + 1) + 1 ≤ Fintype.card V := by
      exact_mod_cast hdegree
    linarith
  · have hvnot : v ∉ closedNeighbors G x := fun hvx => (disjoint_left.mp hdis) hvx hvy
    have hdegree := degree_add_forbidden_le G v (closedNeighbors G x) hvnot
      (fun w hw h => hcross w hw v hvy h.symm)
    rw [closedNeighbors_card G x] at hdegree
    have hdegreeR : (G.degree v : ℝ) + (G.degree x + 1) + 1 ≤ Fintype.card V := by
      exact_mod_cast hdegree
    linarith

private lemma shortCore_three_degree_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B S : Finset V) (Δ X H : ℝ)
    (hHΔ : H ≤ Δ) (hmax : ∀ v, (G.degree v : ℝ) ≤ Δ)
    (hB : ∀ v ∈ B, (G.degree v : ℝ) ≤ X)
    (hD : ∀ v, v ∉ S → (G.degree v : ℝ) ≤ H) :
    2 * (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) * H +
      (B.card : ℝ) * (X - H) + (S.card : ℝ) * (Δ - H) := by
  have hp : ∀ v, (G.degree v : ℝ) ≤ H +
      (if v ∈ B then X - H else 0) + (if v ∈ S then Δ - H else 0) := by
    intro v
    by_cases hvB : v ∈ B <;> by_cases hvS : v ∈ S <;>
      simp only [hvB, hvS, if_true, if_false, add_zero]
    · linarith [hB v hvB]
    · linarith [hB v hvB]
    · linarith [hmax v]
    · exact hD v hvS
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
  rw [shortCore_degree_sum G] at hsum
  simpa only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    Finset.sum_ite_mem_eq, sum_const, nsmul_eq_mul] using hsum

/-- BCM Lemma 3.1 above the quarter-density threshold. The connections in the
conclusion are simple paths in the original graph, with length at most three. -/
theorem shortCore {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : (Fintype.card V : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ)) :
    ∃ A : Finset V,
      (Fintype.card V : ℝ) / 2 +
        Real.sqrt ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) ^ 2 / 4) ≤ A.card ∧
      ∀ x ∈ A, ∀ y ∈ A, ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3 := by
  classical
  let n : ℝ := Fintype.card V
  let m : ℝ := G.edgeFinset.card
  let Δ : ℝ := G.maxDegree
  let c : ℝ := n / 2 + Real.sqrt (m - n ^ 2 / 4)
  let d : ℝ := n - c
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hmupper : m ≤ n ^ 2 / 2 := shortCore_edge_bound G
  have hn : 0 < n := by
    by_contra! hn'
    have hnzero : n = 0 := by linarith
    have hcardzero : Fintype.card V = 0 := by
      exact_mod_cast (show (Fintype.card V : ℝ) = 0 from hnzero)
    have hedgezero : G.edgeFinset.card = 0 := by
      have := G.card_edgeFinset_le_card_choose_two
      simp only [hcardzero, Nat.choose_zero_succ] at this
      omega
    have hmzero : m = 0 := by simp [m, hedgezero]
    change n ^ 2 / 4 < m at hm
    rw [hnzero, hmzero] at hm
    norm_num at hm
  have hnNat : 0 < Fintype.card V := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card V from hn)
  letI : Nonempty V := Fintype.card_pos_iff.mp hnNat
  obtain ⟨hd0, hdc, hcn, hcd, hprod⟩ := shortCore_strict_parameters n m hn0 hm.le hmupper
  change 0 ≤ d at hd0
  change d ≤ c at hdc
  change c ≤ n at hcn
  change c + d = n at hcd
  change 2 * m = n ^ 2 - 2 * c * d at hprod
  have hmax : ∀ v, (G.degree v : ℝ) ≤ Δ := by
    intro v
    dsimp [Δ]
    exact_mod_cast G.degree_le_maxDegree v
  have hsummax : 2 * m ≤ n * Δ := by
    have hh := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hmax v)
    rw [shortCore_degree_sum G] at hh
    simpa [n, m] using hh
  have hΔhalf : n / 2 < Δ := by
    by_contra! hΔ
    have hmul := mul_le_mul_of_nonneg_left hΔ hn0
    change n ^ 2 / 4 < m at hm
    nlinarith
  have hcHalf : 0 ≤ 2 * c - n := by dsimp [c]; nlinarith [Real.sqrt_nonneg (m - n ^ 2 / 4)]
  have hconvert : ∀ A : Finset V, c ≤ A.card →
      (∀ x ∈ A, ∀ y ∈ A, ShortConnection G x y) →
      ∃ A : Finset V, c ≤ A.card ∧
        ∀ x ∈ A, ∀ y ∈ A, ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 3 := by
    intro A hA hconn
    refine ⟨A, hA, ?_⟩
    intro x hx y hy
    obtain ⟨p, hp⟩ := hconn x hx y hy
    exact ⟨p.bypass, p.bypass_isPath, p.length_bypass_le.trans hp⟩
  change ∃ A : Finset V, c ≤ A.card ∧ _
  by_cases hlarge : c ≤ Δ + 1
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    apply hconvert (closedNeighbors G v)
    · rw [closedNeighbors_card]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (show c ≤ (G.degree v : ℝ) + 1 by simpa [Δ, hv] using hlarge)
    · exact fun x hx y hy => closedNeighbors_short G v hx hy
  have hΔc : Δ ≤ c - 1 := by linarith
  by_cases hall : ∀ x y, ShortConnection G x y
  · exact hconvert univ (by simpa [n] using hcn) (fun x _ y _ => hall x y)
  push_neg at hall
  obtain ⟨x, y, hxy, hord, hpairmax⟩ := exists_max_bad_pair G hall
  let X : ℝ := G.degree x
  let A : Finset V := univ.filter (fun v => G.degree x < G.degree v)
  let B : Finset V := univ \ A
  have hBdegree : ∀ v ∈ B, (G.degree v : ℝ) ≤ X := by
    intro v hv
    have : G.degree v ≤ G.degree x := by simpa [B, A] using hv
    dsimp [X]
    exact_mod_cast this
  have hAconn : ∀ u ∈ A, ∀ v ∈ A, ShortConnection G u v := by
    intro u hu v hv
    by_contra huv
    have hle := hpairmax u v huv
    have hux : G.degree x < G.degree u := by simpa [A] using hu
    have hvx : G.degree x < G.degree v := by simpa [A] using hv
    omega
  apply hconvert A _ hAconn
  by_contra! hAc
  have hABNat := card_sdiff_add_card_eq_card (subset_univ A)
  have hAB : (B.card : ℝ) + A.card = n := by
    dsimp [B, n]
    exact_mod_cast hABNat
  have hBd : d ≤ (B.card : ℝ) := by linarith
  have hAn : (A.card : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (show A.card ≤ Fintype.card V by simpa using card_le_card (subset_univ A))
  have hX : n - Δ - 2 < X := by
    by_contra! hX
    have hcount := shortCore_partition_degree_bound G A Δ X
      (fun v _ => hmax v) (fun v hv => hBdegree v (by simp [B, hv]))
    change 2 * m ≤ (A.card : ℝ) * Δ + (n - A.card) * X at hcount
    have hreplaceX := mul_le_mul_of_nonneg_left hX (show 0 ≤ n - A.card by linarith)
    have hreplaceA := mul_le_mul_of_nonneg_right hAc.le (show 0 ≤ 2 * Δ + 2 - n by linarith)
    have hcount' : 2 * m ≤ c * Δ + (n - c) * (n - Δ - 2) := by nlinarith
    exact shortCore_strict_first_contradiction n m c d Δ hn hcd hprod hcHalf hΔc hcount'
  let S : Finset V := univ \ (closedNeighbors G x ∪ closedNeighbors G y)
  let H : ℝ := n - X - 2
  obtain ⟨hden, hScard, hD⟩ := bad_pair_degree_bounds G x y hxy hord
  change 0 ≤ n - 2 * X - 2 at hden
  change (S.card : ℝ) ≤ n - 2 * X - 2 at hScard
  change ∀ v, v ∉ S → (G.degree v : ℝ) ≤ H at hD
  have hXH : X ≤ H := by dsimp [H]; linarith
  have hHΔ : H ≤ Δ := by dsimp [H]; linarith
  have hcount := shortCore_three_degree_bounds G B S Δ X H hHΔ hmax hBdegree hD
  change 2 * m ≤ n * H + (B.card : ℝ) * (X - H) + (S.card : ℝ) * (Δ - H) at hcount
  have hreplaceB := mul_le_mul_of_nonpos_right hBd (show X - H ≤ 0 by linarith)
  have hreplaceS := mul_le_mul_of_nonneg_right hScard (show 0 ≤ Δ - H by linarith)
  have hcount' : 2 * m ≤ (Δ - d) * (n - 2 * X - 2) + 2 * (X + 1) * (n - X - 2) := by
    dsimp [H] at *
    nlinarith
  exact shortCore_strict_final_contradiction n m c d Δ X hn hcd hprod hden hΔc hcount'

end Erdos809.LongOddCycles
