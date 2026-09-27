/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Source.ColoringBridgeCopy
import Erdos809.Patterns

/-!
# Exact covers from the original used-color palette

The class index type is the actual image of the source coloring. A class whose
edges all disappeared may be empty; retaining its cost only increases the
objective, so no unsupported recoloring or palette-preservation claim is needed.
-/

namespace Erdos809.Source

open SimpleGraph Finset
open scoped BigOperators

variable {V K E : Type*} {G H : SimpleGraph V}

/-- The retained members of one original color class. -/
noncomputable def sourceColorClass [Fintype E] (c : G.edgeSet → K)
    (F : E → G.edgeSet) (p : Set.range c) : Finset E := by
  classical
  exact Finset.univ.filter (fun e ↦ c (F e) = p.val)

/-- Each retained edge belongs to exactly one indexed original color class. -/
theorem mem_sourceColorClass [Fintype E] (c : G.edgeSet → K) (F : E → G.edgeSet)
    (p : Set.range c) (e : E) : e ∈ sourceColorClass c F p ↔ c (F e) = p.val := by
  classical
  simp [sourceColorClass]

/-- Give each actually used source color the same nonnegative amount. -/
noncomputable def sourceColorCover [Fintype E] [DecidableEq E] (c : G.edgeSet → K)
    [Fintype (Set.range c)] (F : E → G.edgeSet) (w : ℝ) (hw : 0 ≤ w) :
    ExactPatternCover (fun _ : E ↦ w) (sourceColorClass c F) := by
  classical
  refine ⟨fun _ ↦ w, fun _ ↦ hw, ?_⟩
  intro e
  let pe : Set.range c := ⟨c (F e), ⟨F e, rfl⟩⟩
  have heq (p : Set.range c) : e ∈ sourceColorClass c F p ↔ p = pe := by
    rw [mem_sourceColorClass, Subtype.ext_iff]
    exact eq_comm
  simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The cover cost counts actual source colors, including classes with no
retained edge, and is exactly the source palette size times the common amount. -/
theorem sourceColorCover_cost [Fintype E] [DecidableEq E] (c : G.edgeSet → K)
    [Fintype (Set.range c)] (F : E → G.edgeSet) (w : ℝ) (hw : 0 ≤ w) :
    (sourceColorCover c F w hw).cost = (usedColors c : ℝ) * w := by
  have hcard : Fintype.card (Set.range c) = usedColors c :=
    (Nat.card_eq_fintype_card).symm
  simp [ExactPatternCover.cost, sourceColorCover, hcard]

/-- Endpoint-indexed retained edges, viewed as edges of the original source. -/
def retainedSourceEdges (hHG : H ≤ G) (u v : E → V)
    (hedge : ∀ e, H.Adj (u e) (v e)) : E → G.edgeSet :=
  fun e ↦ ⟨s(u e,v e), hHG (hedge e)⟩

/-- Every original outside-S class is a full retained-host compatible matching. -/
theorem sourceColorClass_pattern [Fintype E] (hHG : H ≤ G) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) (hr5 : RobustAtLength G H 5 5)
    (u v : E → V) (hedge : ∀ e, H.Adj (u e) (v e))
    (hinj : Function.Injective (fun e ↦ s(u e,v e)))
    (hout : ∀ e, OnTriangle H (u e) ∨ OnTriangle H (v e)) (p : Set.range c) :
    (sourceColorClass c (retainedSourceEdges hHG u v hedge) p : Set E).Pairwise
      (fun e f ↦ (u e ≠ u f ∧ u e ≠ v f ∧ v e ≠ u f ∧ v e ≠ v f) ∧
        Compatible H (u e) (v e) (u f) (v f)) := by
  intro e he f hf hef
  have hec := (mem_sourceColorClass c _ p e).mp he
  have hfc := (mem_sourceColorClass c _ p f).mp hf
  exact sameColor_outside_pattern hHG c hc hr2 hr3 hr5 (hedge e) (hedge f) (hout e)
    (fun h ↦ hef (hinj h)) (hec.trans hfc.symm)

/-- Source edges indexed by a pruned graph copied into the spanning cleaner. -/
def prunedSourceEdges {W : Type*} {J : SimpleGraph W} (hHG : H ≤ G) (F : Copy J H)
    (u v : E → W) (hedge : ∀ e, J.Adj (u e) (v e)) : E → G.edgeSet :=
  fun e ↦ ⟨s(F (u e), F (v e)), hHG (F.toHom.map_rel (hedge e))⟩

/-- The same exact original-color class system gives compatible matchings on
the pruned host, while every robust lifting hypothesis still refers to H and G. -/
theorem sourceColorClass_pattern_copy [Fintype E] {W : Type*} {J : SimpleGraph W}
    (hHG : H ≤ G) (F : Copy J H) (c : G.edgeSet → K)
    (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) (hr5 : RobustAtLength G H 5 5)
    (u v : E → W) (hedge : ∀ e, J.Adj (u e) (v e))
    (hinj : Function.Injective (fun e ↦ s(u e, v e)))
    (hout : ∀ e, OnTriangle J (u e) ∨ OnTriangle J (v e)) (p : Set.range c) :
    (sourceColorClass c (prunedSourceEdges hHG F u v hedge) p : Set E).Pairwise
      (fun e f ↦ (u e ≠ u f ∧ u e ≠ v f ∧ v e ≠ u f ∧ v e ≠ v f) ∧
        Compatible J (u e) (v e) (u f) (v f)) := by
  intro e he f hf hef
  have hec := (mem_sourceColorClass c _ p e).mp he
  have hfc := (mem_sourceColorClass c _ p f).mp hf
  exact sameColor_outside_pattern_copy hHG F c hc hr2 hr3 hr5 (hedge e) (hedge f)
    (hout e) (fun h ↦ hef (hinj h)) (hec.trans hfc.symm)


/-- The source-bridge triangle predicate agrees with the finite-theorem free
vertex predicate; both refer to the retained host H. -/
theorem onTriangle_iff_not_triangleFree [Fintype V] {u : V} :
    OnTriangle H u ↔ ¬ TriangleFreeVertex H u := by
  classical
  constructor
  · rintro ⟨a, b, hua, hab, hbu⟩ hfree
    exact hfree a ⟨hua, b, hbu.symm, hab.symm⟩
  · intro hnot
    by_contra hn
    apply hnot
    intro w hw
    obtain ⟨huw, z, huz, hzw⟩ := hw
    exact hn ⟨w, z, huw, hzw.symm, huz.symm⟩

end Erdos809.Source
