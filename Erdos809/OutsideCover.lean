module
public import Erdos809.SectorCover
public import Erdos809.TriangularCover
public import Erdos809.FreeSector

@[expose] public section

/-!
# Exact whole-pattern covers of the actual outside edge set

All sectors and compatibility relations are evaluated in the unchanged full
host. The triangular index is a subtype of actual unordered outside edges,
so its endpoint map is injective. Nonnegative vertex weights suffice.
-/

noncomputable section

namespace Erdos809

open Finset VertexWeights
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Actual outside edges which are triangular in the full host. -/
abbrev OutsideTriangularEdge :=
  {e : (outsideSector G).edgeSet //
    Triangular G (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)}

/-- Actual outside edges which are nontriangular in the full host. -/
abbrev OutsideNontriangularEdge :=
  {e : (outsideSector G).edgeSet //
    ¬ Triangular G (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)}

private def triangularEdgeEquiv : OutsideTriangularEdge G ≃ (triangularSector G).edgeSet where
  toFun e := ⟨e.val.val, by
    rw [← edge_endpoints (outsideSector G) e.val]
    exact e.property⟩
  invFun e := ⟨⟨e.val, SimpleGraph.edgeSet_mono (triangularSector_le_outside G) e.property⟩, by
    have he := e.property
    rw [← edge_endpoints (outsideSector G)
      ⟨e.val, SimpleGraph.edgeSet_mono (triangularSector_le_outside G) e.property⟩] at he
    exact he⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def nontriangularEdgeMap (e : OutsideNontriangularEdge G) :
    (nontriangularSector G).edgeSet :=
  ⟨e.val.val, by
    rw [← edge_endpoints (outsideSector G) e.val]
    exact ⟨(edge_endpoints_adj (outsideSector G) e.val).1,
      fun h => e.property ⟨(edge_endpoints_adj (outsideSector G) e.val).1, h⟩⟩⟩

omit [Fintype V] in
private theorem nontriangularEdgeMap_injective :
    Function.Injective (nontriangularEdgeMap G) := by
  intro e f h
  exact Subtype.ext (Subtype.ext
    (congrArg (fun a : (nontriangularSector G).edgeSet => a.val) h))

private theorem sum_edgeSet_eq (H : SimpleGraph V) (f : Sym2 V → ℝ) :
    (∑ e : H.edgeSet, f e.val) = ∑ e ∈ H.edgeFinset, f e := by
  symm
  exact Finset.sum_subtype _ (by simp) _

theorem outside_triangular_capacity_sum (x : VertexWeights V) :
    (∑ e : OutsideTriangularEdge G,
      x.capacity (edgeLeft (outsideSector G) e.val) (edgeRight (outsideSector G) e.val)) =
      x.edgeMass (triangularSector G) := by
  calc
    _ = ∑ e : (triangularSector G).edgeSet, x.edgeCapacity e.val := by
      apply Fintype.sum_equiv (triangularEdgeEquiv G)
      intro e
      exact (x.edgeCapacity_endpoints (outsideSector G) e.val).symm
    _ = _ := by rw [sum_edgeSet_eq, x.sum_edgeCapacity]

/-- Free-sector edges contribute zero to every private-resource price, so the
outside nontriangular sum equals the full-host resource objective. -/
theorem outside_resource_objective (x : VertexWeights V) (w : V) :
    (∑ e : OutsideNontriangularEdge G,
      x.capacity (edgeLeft (outsideSector G) e.val) (edgeRight (outsideSector G) e.val) *
        if Resource G (edgeLeft (outsideSector G) e.val)
          (edgeRight (outsideSector G) e.val) w then (1 : ℝ) else 0) =
      x.resourceObjective G w := by
  let g (e : (nontriangularSector G).edgeSet) : ℝ :=
    x.capacity (edgeLeft (nontriangularSector G) e) (edgeRight (nontriangularSector G) e) *
      if Resource G (edgeLeft (nontriangularSector G) e)
        (edgeRight (nontriangularSector G) e) w then 1 else 0
  have hz (e : (nontriangularSector G).edgeSet)
      (he : e ∉ Set.range (nontriangularEdgeMap G)) : g e = 0 := by
    have hresource : ¬ Resource G (edgeLeft (nontriangularSector G) e)
        (edgeRight (nontriangularSector G) e) w := by
      intro hr
      have hadj := edge_endpoints_adj (nontriangularSector G) e
      have hout : (outsideSector G).Adj (edgeLeft (nontriangularSector G) e)
          (edgeRight (nontriangularSector G) e) :=
        ⟨hadj.1, fun hf => free_edge_resource_empty G hf.1 hf.2 w hr⟩
      let eo : (outsideSector G).edgeSet := ⟨e.val, by
        rw [← edge_endpoints (nontriangularSector G) e]
        exact hout⟩
      have hnot : ¬ Triangular G (edgeLeft (outsideSector G) eo)
          (edgeRight (outsideSector G) eo) := fun h => hadj.2 h.2
      exact he ⟨⟨eo, hnot⟩, rfl⟩
    simp only [g, if_neg hresource, mul_zero]
  calc
    _ = ∑ e : (nontriangularSector G).edgeSet, g e :=
      Fintype.sum_of_injective (nontriangularEdgeMap G)
        (nontriangularEdgeMap_injective G) _ g hz (fun _ => rfl)
    _ = ∑ e : (nontriangularSector G).edgeSet,
        x.edgeCapacity e.val * endpointSum (fun v => if Triangular G w v then 1 else 0) e.val := by
      apply sum_congr rfl
      intro e _
      have hF := (edge_endpoints_adj (nontriangularSector G) e).2
      dsimp only [g]
      rw [resource_indicator_eq G hF, x.edgeCapacity_endpoints (nontriangularSector G) e]
      rw [← edge_endpoints (nontriangularSector G) e, endpointSum_mk]
    _ = x.resourceObjective G w := by
      rw [sum_edgeSet_eq (nontriangularSector G)
        (fun e => x.edgeCapacity e * endpointSum (fun v => if Triangular G w v then 1 else 0) e),
        x.resource_objective_identity]

omit [Fintype V] in
private theorem sectorEdges_pairwise {E P : Type*} [Fintype E] [DecidableEq E]
    (u v : E → V) (edges : P → Finset E) (side : E → Prop)
    (hpattern : ∀ p, (edges p : Set E).Pairwise
      (fun e f => Compatible G (u e) (v e) (u f) (v f))) :
    ∀ p, (ExactPatternCover.sectorEdges (edges := edges) side p : Set {e // side e}).Pairwise
      (fun e f => Compatible G (u e.val) (v e.val) (u f.val) (v f.val)) := by
  intro p e he f hf hne
  change e ∈ ExactPatternCover.sectorEdges (edges := edges) side p at he
  change f ∈ ExactPatternCover.sectorEdges (edges := edges) side p at hf
  have he' : e.val ∈ edges p := by
    simpa only [ExactPatternCover.sectorEdges, mem_filter, mem_univ, true_and] using he
  have hf' : f.val ∈ edges p := by
    simpa only [ExactPatternCover.sectorEdges, mem_filter, mem_univ, true_and] using hf
  exact hpattern p he' hf' (fun h => hne (Subtype.ext h))

/-- Every exact whole-pattern outside cover splits into triangular and
nontriangular costs. One actual triangular matching witnesses the triangular
bound, and the same nontriangular cost pays every full-host resource root. -/
theorem outsideCover_decomposition (x : VertexWeights V) {δ : ℝ}
    (hδ : 1 / 3 < δ) (hmin : x.MinDegreeAtLeast G δ)
    {P : Type*} [Fintype P]
    (edges : P → Finset (outsideSector G).edgeSet)
    (hpattern : ∀ p, (edges p : Set (outsideSector G).edgeSet).Pairwise
      (fun e f => Compatible G
        (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e)
        (edgeLeft (outsideSector G) f) (edgeRight (outsideSector G) f)))
    (cover : ExactPatternCover
      (fun e => x.capacity (edgeLeft (outsideSector G) e) (edgeRight (outsideSector G) e))
      edges) :
    ∃ (y : TriangularMatching G x (OutsideTriangularEdge G)) (PT PF : ℝ),
      Function.Injective (fun e => s(y.left e, y.right e)) ∧
      0 ≤ PT ∧ 0 ≤ PF ∧ cover.cost = PT + PF ∧
      x.edgeMass (triangularSector G) - y.value ≤ PT ∧
      ∀ w, x.resourceObjective G w ≤ PF := by
  let u := edgeLeft (outsideSector G)
  let v := edgeRight (outsideSector G)
  let side (e : (outsideSector G).edgeSet) : Prop := Triangular G (u e) (v e)
  let tag (p : P) : Prop := ∃ e ∈ edges p, side e
  have hedge (e : (outsideSector G).edgeSet) : G.Adj (u e) (v e) :=
    (edge_endpoints_adj (outsideSector G) e).1
  have hhom : ∀ p e, e ∈ edges p → (side e ↔ tag p) :=
    triangular_pattern_homogeneous x G hδ hmin u v edges hedge hpattern
  let tEdges := ExactPatternCover.sectorEdges (edges := edges) side
  let fEdges := ExactPatternCover.sectorEdges (edges := edges) (fun e => ¬ side e)
  let tCover := cover.sectorCover side tag hhom
  let fCover := cover.sectorCover (fun e => ¬ side e) (fun p => ¬ tag p)
    (fun p e he => not_congr (hhom p e he))
  have htPattern := sectorEdges_pairwise G u v edges side hpattern
  have hfPattern := sectorEdges_pairwise G u v edges (fun e => ¬ side e) hpattern
  let y : TriangularMatching G x (OutsideTriangularEdge G) :=
    triangularCoverMatching x G hδ hmin (fun e => u e.val) (fun e => v e.val)
      (fun e => e.property) tEdges htPattern tCover
  have hinj : Function.Injective (fun e => s(y.left e, y.right e)) := by
    intro e f he
    change s(u e.val, v e.val) = s(u f.val, v f.val) at he
    rw [edge_endpoints, edge_endpoints] at he
    exact Subtype.ext (Subtype.ext he)
  have htCost : x.edgeMass (triangularSector G) - y.value ≤ tCover.cost := by
    have h := triangularCoverMatching_cost_bound x G hδ hmin
      (fun e => u e.val) (fun e => v e.val) (fun e => e.property) tEdges htPattern tCover
    rw [outside_triangular_capacity_sum] at h
    exact h
  have hfCost (w : V) : x.resourceObjective G w ≤ fCover.cost := by
    have h := resource_price_bound x G hδ hmin (fun e => u e.val) (fun e => v e.val)
      (fun e => hedge e.val) (fun e h => e.property ⟨hedge e.val, h⟩)
      (fun e => x.capacity (u e.val) (v e.val)) fEdges hfPattern fCover w
    rw [outside_resource_objective] at h
    exact h
  refine ⟨y, tCover.cost, fCover.cost, hinj, ?_, ?_, ?_, htCost, hfCost⟩
  · exact sum_nonneg fun p _ => tCover.nonneg p
  · exact sum_nonneg fun p _ => fCover.nonneg p
  · exact (cover.sectorCover_cost_add_complement side tag hhom).symm

end Erdos809
