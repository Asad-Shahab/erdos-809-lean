module
/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
public import Erdos809.Edges
public import Erdos809.Patterns

@[expose] public section

/-! The triangular and nontriangular sectors of the unchanged full host, and
the exact identification of the private-resource objective with q(w). -/

namespace Erdos809

open Finset
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

def triangularSector : SimpleGraph V where
  Adj := Triangular G
  symm := ⟨fun _ _ h => ⟨h.1.symm, walk2_symm G h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def nontriangularSector : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ Walk2 G u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 (walk2_symm G h')⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem triangularSector_le : triangularSector G ≤ G := fun _ _ h => h.1
theorem nontriangularSector_le : nontriangularSector G ≤ G := fun _ _ h => h.1

/-- A symmetric endpoint function on unordered edges. -/
noncomputable def endpointSum (f : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => f u + f v, fun _ _ => add_comm _ _⟩

@[simp] theorem endpointSum_mk (f : V → ℝ) (u v : V) :
    endpointSum f s(u,v) = f u + f v := rfl

open Classical in
/-- On a nontriangular edge the two resource incidences cannot overlap. -/
theorem resource_indicator_eq {u v w : V} (hF : ¬ Walk2 G u v) :
    (if Resource G u v w then (1 : ℝ) else 0) =
      (if Triangular G w u then 1 else 0) + (if Triangular G w v then 1 else 0) := by
  classical
  have hsym (a b : V) : Triangular G a b ↔ Triangular G b a :=
    ⟨fun h => ⟨h.1.symm, walk2_symm G h.2⟩,
      fun h => ⟨h.1.symm, walk2_symm G h.2⟩⟩
  have hn : ¬ (Triangular G w u ∧ Triangular G w v) :=
    fun h => hF ⟨w, h.1.1.symm, h.2.1⟩
  unfold Resource
  rw [hsym u w, hsym v w]
  by_cases hu : Triangular G w u <;> by_cases hv : Triangular G w v <;> simp_all

namespace VertexWeights

variable [Fintype V] (x : VertexWeights V)

/-- The root objective q(w), with nontriangular degree measured in the full host. -/
noncomputable def resourceObjective (w : V) : ℝ := by
  classical
  exact ∑ v, x.weight v * x.degree (nontriangularSector G) v *
    if Triangular G w v then 1 else 0

open Classical in
theorem resource_objective_identity (w : V) :
    (∑ e ∈ (nontriangularSector G).edgeFinset,
      x.edgeCapacity e * endpointSum (fun v => if Triangular G w v then 1 else 0) e) =
      x.resourceObjective G w := by
  classical
  let f : V → ℝ := fun v => if Triangular G w v then 1 else 0
  have h := x.sum_edgeCapacity_mul (nontriangularSector G) (endpointSum f)
  simp only [endpointSum_mk] at h
  rw [x.edgeSum_add, x.edgeSum_swap (nontriangularSector G) (fun u _ => f u),
    x.edgeSum_left] at h
  change 2 * _ = (∑ u, x.weight u * x.degree (nontriangularSector G) u * f u) +
    (∑ u, x.weight u * x.degree (nontriangularSector G) u * f u) at h
  change _ = ∑ u, x.weight u * x.degree (nontriangularSector G) u * f u
  linarith

end VertexWeights
end Erdos809
