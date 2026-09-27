import Erdos809.LongOddCycles.Definitions
import Erdos809.UpperBound

namespace Erdos809
open SimpleGraph

private theorem not_reachable_sum_inl_inr_compat {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} (v : V) (w : W) :
    ¬(G ⊕g H).Reachable (.inl v) (.inr w) := by
  rintro ⟨p⟩
  have hs : ∀ x : V ⊕ W, x ∉ Set.range .inl ↔ x ∈ Set.range .inr := by simp
  obtain ⟨⟨d, hadj⟩, _, hd1, hd2⟩ := p.exists_boundary_dart
    (Set.range .inl) (by simp) (by simp)
  simp only [hs] at hadj hd1 hd2
  obtain ⟨v', hv'⟩ := hd1
  obtain ⟨w', hw'⟩ := hd2
  rw [← hv', ← hw'] at hadj
  simp [SimpleGraph.sum] at hadj

theorem cycleCopy_one_side {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {ℓ : ℕ} (hℓ : 0 < ℓ) (F : CycleCopy ℓ (G ⊕g H)) :
    (∀ i, ∃ v, F i = Sum.inl v) ∨ (∀ i, ∃ w, F i = Sum.inr w) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ)
  have hr (i : Fin (r+1)) : (G ⊕g H).Reachable (F 0) (F i) :=
    ((cycleGraph_connected (n := r)).preconnected 0 i).map F.toHom
  cases h0 : F 0 with
  | inl v =>
    left
    intro i
    cases hi : F i with
    | inl u => exact ⟨u, rfl⟩
    | inr w => exact False.elim (not_reachable_sum_inl_inr_compat v w (h0 ▸ hi ▸ hr i))
  | inr w =>
    right
    intro i
    cases hi : F i with
    | inr u => exact ⟨u, rfl⟩
    | inl v => exact False.elim (not_reachable_sum_inl_inr_compat v w (h0 ▸ hi ▸ (hr i).symm))

theorem twoCliquesColoring_valid_cycle {ℓ a b : ℕ} (hℓ : 0 < ℓ) (hba : b ≤ a) :
    ValidCycleColoring ℓ (twoCliquesColoring hba) := by
  intro F
  have hi : Function.Injective ((twoCliquesPaletteHom hba).comp F.toHom) := by
    intro i j hij
    apply F.injective
    change F i = F j
    change Sum.elim id (Fin.castLE hba) (F i) =
      Sum.elim id (Fin.castLE hba) (F j) at hij
    rcases cycleCopy_one_side hℓ F with h | h
    · obtain ⟨u, hu⟩ := h i
      obtain ⟨v, hv⟩ := h j
      rw [hu, hv] at hij ⊢
      exact congrArg Sum.inl hij
    · obtain ⟨u, hu⟩ := h i
      obtain ⟨v, hv⟩ := h j
      rw [hu, hv] at hij ⊢
      exact congrArg Sum.inr (Fin.ext (congrArg (fun x : Fin a ↦ x.val) hij))
  have he := Hom.mapEdgeSet.injective ((twoCliquesPaletteHom hba).comp F.toHom) hi
  intro e f hef
  apply he
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change Sym2.map (twoCliquesPaletteHom hba) (Sym2.map F.toHom e.val) =
    Sym2.map (twoCliquesPaletteHom hba) (Sym2.map F.toHom f.val) at hv
  exact (Sym2.map_map (g := twoCliquesPaletteHom hba) (f := F.toHom) e.val).symm.trans
    (hv.trans (Sym2.map_map (g := twoCliquesPaletteHom hba) (f := F.toHom) f.val))

theorem cycleUpperBoundAt_of_sizes {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℝ} {n a b : ℕ}
    (hab : a + b = n) (hba : b ≤ a)
    (hm : exactThreshold n ≤ a.choose 2 + b.choose 2)
    (hc : (a.choose 2 : ℝ) ≤ (1 / 8 + ε) * (n : ℝ) ^ 2) : CycleUpperBoundAt ℓ ε n := by
  classical
  let e : (Fin a ⊕ Fin b) ≃ Fin n := finSumFinEquiv.trans (finCongr hab)
  let G := (twoCliques a b).map e.toEmbedding
  let I : twoCliques a b ≃g G := Iso.map e _
  let c : G.edgeSet → (⊤ : SimpleGraph (Fin a)).edgeSet :=
    twoCliquesColoring hba ∘ I.symm.toCopy.mapEdgeSet
  let enc : (⊤ : SimpleGraph (Fin a)).edgeSet → ℕ :=
    fun x ↦ (Fintype.equivFin _ x).val
  have henc : Function.Injective enc :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  have hcvalid : ValidCycleColoring ℓ c := (twoCliquesColoring_valid_cycle hℓ hba).comap _
  refine ⟨G, enc ∘ c, ?_, hcvalid.postcomp henc, ?_⟩
  · have he : EdgeCount G = EdgeCount (twoCliques a b) :=
      Nat.card_congr I.symm.mapEdgeSet
    rwa [he, twoCliques_edgeCount]
  · rw [usedColors_postcomp c henc]
    have hcu : usedColors c ≤ a.choose 2 :=
      (usedColors_comap_le _ _).trans (twoCliquesColoring_usedColors_le hba)
    exact (Nat.cast_le.mpr hcu).trans hc

theorem cycle_asymptoticUpperBound {ℓ : ℕ} (hℓ : 0 < ℓ) :
    CycleAsymptoticUpperBound ℓ := by
  intro ε hε
  let δ : ℝ := min ε (1 / 8)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (16 / δ^2)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnR : 16 / δ^2 ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  obtain ⟨a, b, hab, hba, hm, hc⟩ :=
    upper_clique_sizes hδ (min_le_left _ _) (min_le_right _ _) hnR
  exact cycleUpperBoundAt_of_sizes hℓ hab hba hm hc

end Erdos809
