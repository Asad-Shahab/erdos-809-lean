import Erdos809.Sectors

/-! The free sector consists of full-host edges whose two endpoints lie in no
triangle. Its complement is the actual edge domain of the palette theorem. -/

namespace Erdos809

variable {V : Type*} (G : SimpleGraph V)

def freeSector : SimpleGraph V where
  Adj u v := G.Adj u v ∧ TriangleFreeVertex G u ∧ TriangleFreeVertex G v
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def outsideSector : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (TriangleFreeVertex G u ∧ TriangleFreeVertex G v)
  symm := fun _ _ h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2, h'.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem freeSector_le : freeSector G ≤ G := fun _ _ h => h.1
theorem outsideSector_le : outsideSector G ≤ G := fun _ _ h => h.1

@[simp] theorem outsideSector_adj {u v : V} :
    (outsideSector G).Adj u v ↔
      G.Adj u v ∧ ¬ (TriangleFreeVertex G u ∧ TriangleFreeVertex G v) := Iff.rfl

@[simp] theorem freeSector_adj {u v : V} :
    (freeSector G).Adj u v ↔
      G.Adj u v ∧ TriangleFreeVertex G u ∧ TriangleFreeVertex G v := Iff.rfl

theorem triangularSector_le_outside : triangularSector G ≤ outsideSector G := by
  intro u v h
  exact ⟨h.1, fun hf => hf.1 v h⟩

theorem freeSector_le_nontriangular : freeSector G ≤ nontriangularSector G := by
  intro u v h
  exact ⟨h.1, fun hw => h.2.1 v ⟨h.1, hw⟩⟩

theorem freeSector_resource_zero {u v : V} (h : (freeSector G).Adj u v) (w : V) :
    ¬ Resource G u v w := free_edge_resource_empty G h.2.1 h.2.2 w

namespace VertexWeights

open Finset
open scoped BigOperators

variable [Fintype V] (x : VertexWeights V)

theorem edgeMass_triangular_add_nontriangular :
    x.edgeMass (triangularSector G) + x.edgeMass (nontriangularSector G) =
      x.edgeMass G := by
  classical
  have hs : x.edgeSum (triangularSector G) (fun _ _ => 1) +
      x.edgeSum (nontriangularSector G) (fun _ _ => 1) =
      x.edgeSum G (fun _ _ => 1) := by
    unfold edgeSum
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases ha : G.Adj u v <;> by_cases ht : Walk2 G u v <;>
      simp [triangularSector, nontriangularSector, Triangular, ha, ht]
  rw [x.edgeSum_one, x.edgeSum_one, x.edgeSum_one] at hs
  linarith

theorem edgeMass_free_add_outside :
    x.edgeMass (freeSector G) + x.edgeMass (outsideSector G) = x.edgeMass G := by
  classical
  have hs : x.edgeSum (freeSector G) (fun _ _ => 1) +
      x.edgeSum (outsideSector G) (fun _ _ => 1) =
      x.edgeSum G (fun _ _ => 1) := by
    unfold edgeSum
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases ha : G.Adj u v <;> by_cases hu : TriangleFreeVertex G u <;>
      by_cases hv : TriangleFreeVertex G v <;> simp [ha, hu, hv]
  rw [x.edgeSum_one, x.edgeSum_one, x.edgeSum_one] at hs
  linarith

end VertexWeights
end Erdos809
