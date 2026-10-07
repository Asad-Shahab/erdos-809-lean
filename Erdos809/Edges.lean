module
/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
public import Erdos809.WeightedIdentities
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Relating unordered host edges to oriented weighted sums. -/

namespace Erdos809

open Finset
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

noncomputable def edgeLeft (e : G.edgeSet) : V := e.val.out.1
noncomputable def edgeRight (e : G.edgeSet) : V := e.val.out.2

theorem edge_endpoints (e : G.edgeSet) : s(edgeLeft G e, edgeRight G e) = e.val := by
  exact e.val.out_eq

theorem edge_endpoints_adj (e : G.edgeSet) : G.Adj (edgeLeft G e) (edgeRight G e) := by
  have he := e.property
  rw [← edge_endpoints G e] at he
  exact he

def dartPairEquiv : G.Dart ≃ {p : V × V // G.Adj p.1 p.2} where
  toFun d := ⟨d.toProd, d.adj⟩
  invFun p := ⟨p.val, p.property⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- Every unordered edge has exactly two orientations, including for a weighted sum. -/
theorem sum_darts_eq_twice_edges (f : Sym2 V → ℝ) :
    (∑ d : G.Dart, f d.edge) = 2 * ∑ e ∈ G.edgeFinset, f e := by
  classical
  have hfiber := sum_fiberwise_of_maps_to' (s := univ) (t := G.edgeFinset)
    (g := SimpleGraph.Dart.edge)
    (fun d _ => G.mem_edgeFinset.mpr d.edge_mem) f
  rw [← hfiber]
  calc
    _ = ∑ e ∈ G.edgeFinset, 2 * f e := by
      apply sum_congr rfl
      intro e he
      rw [sum_const, G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he)]
      simp
    _ = _ := (mul_sum ..).symm

theorem sum_darts_eq_sum_adj (f : V → V → ℝ) :
    (∑ d : G.Dart, f d.fst d.snd) = ∑ u, ∑ v, if G.Adj u v then f u v else 0 := by
  classical
  calc
    _ = ∑ p : {p : V × V // G.Adj p.1 p.2}, f p.val.1 p.val.2 :=
      Fintype.sum_equiv (dartPairEquiv G) _ _ (fun _ => rfl)
    _ = ∑ p ∈ univ.filter (fun p : V × V => G.Adj p.1 p.2), f p.1 p.2 := by
      symm
      exact sum_subtype _ (by simp) _
    _ = _ := by rw [sum_filter, Fintype.sum_prod_type]

namespace VertexWeights

variable (x : VertexWeights V)

/-- Capacity on unordered edges, independent of a chosen orientation. -/
noncomputable def edgeCapacity : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => x.weight u * x.weight v, fun _ _ => mul_comm _ _⟩

@[simp] theorem edgeCapacity_mk (u v : V) :
    x.edgeCapacity s(u,v) = x.weight u * x.weight v := rfl

omit [DecidableRel G.Adj] in
theorem edgeCapacity_endpoints (e : G.edgeSet) :
    x.edgeCapacity e.val = x.capacity (edgeLeft G e) (edgeRight G e) := by
  rw [← edge_endpoints G e]
  rfl

theorem sum_edgeCapacity : (∑ e ∈ G.edgeFinset, x.edgeCapacity e) = x.edgeMass G := by
  have h₁ := sum_darts_eq_twice_edges G x.edgeCapacity
  have h₂ := sum_darts_eq_sum_adj G (fun u v => x.weight u * x.weight v)
  have h₃ := x.edgeSum_one G
  simp only [edgeSum, mul_one] at h₃
  change (∑ d : G.Dart, x.weight d.fst * x.weight d.snd) = _ at h₁
  rw [h₂, h₃] at h₁
  linarith

/-- The same orientation count for an arbitrary function of unordered edges. -/
theorem sum_edgeCapacity_mul (f : Sym2 V → ℝ) :
    2 * (∑ e ∈ G.edgeFinset, x.edgeCapacity e * f e) =
      x.edgeSum G (fun u v => f s(u,v)) := by
  have h₁ := sum_darts_eq_twice_edges G (fun e => x.edgeCapacity e * f e)
  have h₂ := sum_darts_eq_sum_adj G (fun u v => x.weight u * x.weight v * f s(u,v))
  change (∑ d : G.Dart, x.weight d.fst * x.weight d.snd * f s(d.fst,d.snd)) = _ at h₁
  rw [h₂] at h₁
  simpa only [edgeSum] using h₁.symm

end VertexWeights
end Erdos809
