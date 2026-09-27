/-
Copyright (c) 2026 Asad Shahab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asad Shahab
-/
import Erdos809.Source.ColoringBridge

/-!
# Transport the original-color bridge through vertex pruning

The robust spanning cleaner stays on the original vertex type. A pruned graph
maps into that cleaner by a graph copy. Lifted paths still live in the original
source, and are never required to avoid every pruned vertex.
-/

namespace Erdos809.Source

open SimpleGraph

variable {V W K : Type*} {G H : SimpleGraph V} {J : SimpleGraph W}

theorem walk2_map (f : J →g H) {u v : W} (h : Walk2 J u v) :
    Walk2 H (f u) (f v) := by
  obtain ⟨z, huz, hzv⟩ := h
  exact ⟨f z, f.map_rel huz, f.map_rel hzv⟩

theorem walk3_map (f : J →g H) {u v : W} (h : Walk3 J u v) :
    Walk3 H (f u) (f v) := by
  obtain ⟨z, t, huz, hzt, htv⟩ := h
  exact ⟨f z, f t, f.map_rel huz, f.map_rel hzt, f.map_rel htv⟩

/-- Deleting retained edges or vertices cannot introduce a forbidden walk pair. -/
theorem compatible_comap (f : J →g H) {u v a b : W}
    (h : Compatible H (f u) (f v) (f a) (f b)) : Compatible J u v a b :=
  ⟨fun ⟨p, q⟩ ↦ h.1 ⟨walk2_map f p, walk3_map f q⟩,
    fun ⟨p, q⟩ ↦ h.2.1 ⟨walk2_map f p, walk3_map f q⟩,
    fun ⟨p, q⟩ ↦ h.2.2.1 ⟨walk2_map f p, walk3_map f q⟩,
    fun ⟨p, q⟩ ↦ h.2.2.2 ⟨walk2_map f p, walk3_map f q⟩⟩

theorem OnTriangle.map (f : J →g H) {u : W} (h : OnTriangle J u) :
    OnTriangle H (f u) := by
  obtain ⟨a, b, hua, hab, hbu⟩ := h
  exact ⟨f a, f b, f.map_rel hua, f.map_rel hab, f.map_rel hbu⟩

/-- Original-color compatible matchings survive arbitrary pruning of the robust
cleaner. Source and pruned graph vertex types may be different. -/
theorem sameColor_outside_pattern_copy (hHG : H ≤ G) (F : Copy J H)
    (c : G.edgeSet → K) (hc : ValidC7Coloring c) (hr2 : RobustAtLength G H 2 5)
    (hr3 : RobustAtLength G H 3 5) (hr5 : RobustAtLength G H 5 5)
    {a b x y : W} (hab : J.Adj a b) (hxy : J.Adj x y)
    (hout : OnTriangle J a ∨ OnTriangle J b) (hne : s(a, b) ≠ s(x, y))
    (hcolor : edgeColor c (hHG (F.toHom.map_rel hab)) =
      edgeColor c (hHG (F.toHom.map_rel hxy))) :
    (a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y) ∧ Compatible J a b x y := by
  have hne' : s(F a, F b) ≠ s(F x, F y) := by
    intro he
    apply hne
    apply Sym2.map.injective F.injective
    exact he
  have hout' : OnTriangle H (F a) ∨ OnTriangle H (F b) :=
    hout.elim (fun h ↦ Or.inl (h.map F.toHom)) (fun h ↦ Or.inr (h.map F.toHom))
  obtain ⟨⟨hax, hay, hbx, hby⟩, hcomp⟩ := sameColor_outside_pattern hHG c hc hr2 hr3 hr5
    (F.toHom.map_rel hab) (F.toHom.map_rel hxy) hout' hne' hcolor
  exact ⟨⟨fun h ↦ hax (congrArg F h), fun h ↦ hay (congrArg F h),
    fun h ↦ hbx (congrArg F h), fun h ↦ hby (congrArg F h)⟩,
    compatible_comap F.toHom hcomp⟩

end Erdos809.Source
