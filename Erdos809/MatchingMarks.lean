import Erdos809.Matching
import Erdos809.Sectors

/-! Turn the usage of one actual matching into fractional edge marks. The
unordered endpoint injection prevents duplicate indices from exceeding a host
edge's capacity. Zero vertex weights are allowed and handled explicitly. -/

namespace Erdos809.TriangularMatching

open Finset VertexWeights
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]
variable {G : SimpleGraph V} {x : VertexWeights V} (y : TriangularMatching G x E)

open Classical in
noncomputable def edgeUsage (e : Sym2 V) : ℝ :=
  ∑ i, if s(y.left i, y.right i) = e then y.usage i else 0

theorem edgeUsage_nonneg (e : Sym2 V) : 0 ≤ y.edgeUsage e := by
  classical
  exact sum_nonneg fun i _ => by split_ifs; exact y.usage_nonneg i; exact le_refl _

theorem edgeUsage_at (hinj : Function.Injective (fun i => s(y.left i, y.right i)))
    (i : E) : y.edgeUsage s(y.left i, y.right i) = y.usage i := by
  classical
  unfold edgeUsage
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (hinj h))
  · simp

theorem edgeUsage_eq_zero {e : Sym2 V}
    (h : ¬ ∃ i, s(y.left i, y.right i) = e) : y.edgeUsage e = 0 := by
  classical
  exact sum_eq_zero fun i _ => if_neg (fun hi => h ⟨i, hi⟩)

theorem edgeUsage_support {e : Sym2 V} (h : 0 < y.edgeUsage e) :
    ∃ i, s(y.left i, y.right i) = e := by
  by_contra hn
  rw [y.edgeUsage_eq_zero hn] at h
  exact lt_irrefl 0 h

theorem edgeUsage_le_capacity
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    y.edgeUsage s(u, v) ≤ x.capacity u v := by
  classical
  by_cases he : ∃ i, s(y.left i, y.right i) = s(u, v)
  · obtain ⟨i, hi⟩ := he
    have hc : x.capacity (y.left i) (y.right i) = x.capacity u v :=
      congrArg x.edgeCapacity hi
    rw [← hi, y.edgeUsage_at hinj]
    exact (y.usage_le_capacity i).trans_eq hc
  · rw [y.edgeUsage_eq_zero he]
    exact mul_nonneg (x.nonneg u) (x.nonneg v)

theorem edgeUsage_zero_of_not_triangular {u v : V} (h : ¬ Triangular G u v) :
    y.edgeUsage s(u, v) = 0 := by
  apply y.edgeUsage_eq_zero
  rintro ⟨i, hi⟩
  rcases Sym2.eq_iff.mp hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact h (hu ▸ hv ▸ y.triangular i)
  · have ht := y.triangular i
    rw [hu, hv] at ht
    exact h ⟨ht.1.symm, walk2_symm G ht.2⟩

variable [DecidableRel G.Adj]

theorem sum_edgeUsage_mul (f : Sym2 V → ℝ) :
    (∑ e ∈ G.edgeFinset, y.edgeUsage e * f e) =
      ∑ i, y.usage i * f s(y.left i, y.right i) := by
  classical
  simp only [edgeUsage, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have he : s(y.left i, y.right i) ∈ G.edgeFinset :=
    G.mem_edgeFinset.mpr (y.triangular i).1
  simp only [ite_mul, zero_mul, sum_ite_eq, he, if_true]

theorem sum_edgeUsage : (∑ e ∈ G.edgeFinset, y.edgeUsage e) = y.mass := by
  simpa only [mul_one, mass] using y.sum_edgeUsage_mul (fun _ => 1)

omit [DecidableRel G.Adj] in
noncomputable def markProbability (u v : V) : ℝ :=
  y.edgeUsage s(u,v) / x.capacity u v

omit [DecidableRel G.Adj] in
theorem markProbability_nonneg (u v : V) : 0 ≤ y.markProbability u v :=
  div_nonneg (y.edgeUsage_nonneg _) (mul_nonneg (x.nonneg u) (x.nonneg v))

omit [DecidableRel G.Adj] in
theorem markProbability_le_one
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    y.markProbability u v ≤ 1 := by
  exact div_le_one_of_le₀ (y.edgeUsage_le_capacity hinj u v)
    (mul_nonneg (x.nonneg u) (x.nonneg v))

omit [DecidableRel G.Adj] in
theorem markProbability_symm (u v : V) : y.markProbability u v = y.markProbability v u := by
  simp only [markProbability, Sym2.eq_swap (a := u), VertexWeights.capacity,
    mul_comm (x.weight u)]

omit [DecidableRel G.Adj] in
theorem capacity_mul_markProbability
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (u v : V) :
    x.capacity u v * y.markProbability u v = y.edgeUsage s(u,v) := by
  unfold markProbability
  by_cases hc : x.capacity u v = 0
  · have hz : y.edgeUsage s(u,v) = 0 :=
      le_antisymm (by simpa only [hc] using y.edgeUsage_le_capacity hinj u v)
        (y.edgeUsage_nonneg _)
    simp only [hc, hz, zero_div, mul_zero]
  · exact mul_div_cancel₀ _ hc

omit [DecidableRel G.Adj] in
theorem markProbability_zero_of_not_triangular {u v : V} (h : ¬ Triangular G u v) :
    y.markProbability u v = 0 := by
  rw [markProbability, y.edgeUsage_zero_of_not_triangular h, zero_div]

theorem markProbability_total
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) :
    x.edgeSum G y.markProbability = 2 * y.mass := by
  have h₁ := sum_darts_eq_twice_edges G y.edgeUsage
  have h₂ := sum_darts_eq_sum_adj G (fun u v => y.edgeUsage s(u,v))
  change (∑ d : G.Dart, y.edgeUsage s(d.fst,d.snd)) = _ at h₁
  rw [h₂, y.sum_edgeUsage] at h₁
  rw [← h₁]
  unfold edgeSum
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v
  · simp only [h, if_true]
    exact y.capacity_mul_markProbability hinj u v
  · simp only [h, if_false]

theorem markProbability_ordered_total
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) :
    (∑ u, ∑ v, x.weight u * x.weight v * y.markProbability u v) = 2 * y.mass := by
  rw [← y.markProbability_total hinj]
  unfold edgeSum
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v
  · simp only [h, if_true]
  · have hz := y.markProbability_zero_of_not_triangular (fun ht => h ht.1)
    simp only [h, if_false, hz, mul_zero]

omit [DecidableRel G.Adj] in
theorem markProbability_used_union_bound [DecidableEq V]
    (hinj : Function.Injective (fun i => s(y.left i, y.right i)))
    {δ : ℝ} (hmin : x.MinDegreeAtLeast G δ) {u v : V}
    (hpos : 0 < y.markProbability u v) :
    x.mass (neighbors G u ∪ neighbors G v) ≤ 1 - δ := by
  have hepos : 0 < y.edgeUsage s(u,v) := by
    have hne : y.edgeUsage s(u,v) ≠ 0 := by
      intro hz
      simp only [markProbability, hz, zero_div, lt_self_iff_false] at hpos
    exact lt_of_le_of_ne (y.edgeUsage_nonneg _) hne.symm
  obtain ⟨i, hi⟩ := y.edgeUsage_support hepos
  have hiused : 0 < y.usage i := by
    rwa [← hi, y.edgeUsage_at hinj] at hepos
  have hb := y.used_union_bound hmin hiused
  rcases Sym2.eq_iff.mp hi with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · simpa only [hu, hv] using hb
  · simpa only [hu, hv, union_comm] using hb

theorem markProbability_edge_sum
    (hinj : Function.Injective (fun i => s(y.left i, y.right i)))
    (f : Sym2 V → ℝ) :
    x.edgeSum G (fun u v => y.markProbability u v * f s(u,v)) =
      2 * ∑ i, y.usage i * f s(y.left i, y.right i) := by
  have h₁ := sum_darts_eq_twice_edges G (fun e => y.edgeUsage e * f e)
  have h₂ := sum_darts_eq_sum_adj G (fun u v => y.edgeUsage s(u,v) * f s(u,v))
  change (∑ d : G.Dart, y.edgeUsage s(d.fst,d.snd) * f s(d.fst,d.snd)) = _ at h₁
  rw [h₂, y.sum_edgeUsage_mul] at h₁
  rw [← h₁]
  unfold edgeSum
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases h : G.Adj u v
  · simp only [h, if_true, ← mul_assoc]
    rw [show x.weight u * x.weight v = x.capacity u v from rfl,
      y.capacity_mul_markProbability hinj]
  · simp only [h, if_false]

omit [DecidableRel G.Adj] in
noncomputable def markedDegree (v : V) : ℝ := ∑ u, x.weight u * y.markProbability u v

theorem markedDegree_sum
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (f : V → ℝ) :
    (∑ v, x.weight v * y.markedDegree v * f v) =
      ∑ i, y.usage i * (f (y.left i) + f (y.right i)) := by
  classical
  let q (u v : V) := x.weight u * x.weight v * y.markProbability u v
  have hsym (u v : V) : q u v = q v u := by
    dsimp only [q]
    rw [y.markProbability_symm u v, mul_comm (x.weight u)]
  have hright : (∑ u, ∑ v, q u v * f v) =
      ∑ v, x.weight v * y.markedDegree v * f v := by
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    simp only [markedDegree, mul_sum, sum_mul]
    apply sum_congr rfl
    intro u _
    dsimp only [q]
    ring
  have hleft : (∑ u, ∑ v, q u v * f u) =
      ∑ v, x.weight v * y.markedDegree v * f v := by
    rw [sum_comm]
    simpa only [hsym] using hright
  have hfull : x.edgeSum G (fun u v => y.markProbability u v * (f u + f v)) =
      ∑ u, ∑ v, q u v * (f u + f v) := by
    unfold edgeSum
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    by_cases h : G.Adj u v
    · simp only [h, if_true, q, mul_assoc]
    · have hz := y.markProbability_zero_of_not_triangular (fun ht => h ht.1)
      simp only [h, if_false, q, hz, mul_zero, zero_mul]
  have he := y.markProbability_edge_sum hinj (endpointSum f)
  simp only [endpointSum_mk] at he
  rw [hfull] at he
  simp_rw [mul_add, sum_add_distrib] at he
  rw [hleft, hright] at he
  simp_rw [mul_add, sum_add_distrib]
  linarith

theorem markedDegree_rootLoad
    (hinj : Function.Injective (fun i => s(y.left i, y.right i))) (w : V) :
    (∑ v, x.weight v * y.markedDegree v * if G.Adj w v then 1 else 0) =
      y.rootLoad w := by
  classical
  rw [y.markedDegree_sum hinj]
  unfold rootLoad
  apply sum_congr rfl
  intro i _
  by_cases hl : G.Adj w (y.left i) <;> by_cases hr : G.Adj w (y.right i) <;>
    simp [rootIncidence, hl, hr]

end Erdos809.TriangularMatching
