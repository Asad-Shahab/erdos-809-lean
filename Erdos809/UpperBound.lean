module
public import Erdos809.Definitions
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Erdos809

open SimpleGraph

/-- The disjoint-union reachability fact, supplied locally for mathlib 4.28. -/
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

/-- The edge bijection for disjoint unions, supplied locally for mathlib 4.28. -/
private noncomputable def edgeSetSumEquiv_compat {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W} :
    (G ⊕g H).edgeSet ≃ G.edgeSet ⊕ H.edgeSet := by
  let f : G.edgeSet ⊕ H.edgeSet → (G ⊕g H).edgeSet :=
    Sum.elim Embedding.sumInl.toHom.mapEdgeSet Embedding.sumInr.toHom.mapEdgeSet
  refine (Equiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro e e' h
    rcases e with e | e <;> rcases e' with e' | e'
    · exact congrArg Sum.inl (Embedding.sumInl.mapEdgeSet.injective h)
    · rcases e with ⟨⟨u, v⟩, he⟩
      rcases e' with ⟨⟨x, y⟩, he'⟩
      have hh := congrArg Subtype.val h
      change s(Sum.inl u, Sum.inl v) = s(Sum.inr x, Sum.inr y) at hh
      simp only [Sym2.eq_iff, Sum.inl_ne_inr, false_and, or_self] at hh
    · rcases e with ⟨⟨u, v⟩, he⟩
      rcases e' with ⟨⟨x, y⟩, he'⟩
      have hh := congrArg Subtype.val h
      change s(Sum.inr u, Sum.inr v) = s(Sum.inl x, Sum.inl y) at hh
      simp only [Sym2.eq_iff, Sum.inr_ne_inl, false_and, or_self] at hh
    · exact congrArg Sum.inr (Embedding.sumInr.mapEdgeSet.injective h)
  · rintro ⟨⟨u | u, v | v⟩, h⟩
    · exact ⟨.inl ⟨s(u,v), h⟩, rfl⟩
    · simp [SimpleGraph.sum] at h
    · simp [SimpleGraph.sum] at h
    · exact ⟨.inr ⟨s(u,v), h⟩, rfl⟩

/-- A connected seven-cycle lies in exactly one side of a disjoint union. -/
theorem c7Copy_one_side {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (F : C7Copy (G ⊕g H)) :
    (∀ i, ∃ v, F i = Sum.inl v) ∨ (∀ i, ∃ w, F i = Sum.inr w) := by
  have hr (i : Fin 7) : (G ⊕g H).Reachable (F 0) (F i) :=
    ((cycleGraph_connected (n := 6)).preconnected 0 i).map F.toHom
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

/-- Two cliques, with the exact number `a + b` of vertices. -/
abbrev twoCliques (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  (⊤ : SimpleGraph (Fin a)) ⊕g (⊤ : SimpleGraph (Fin b))

/-- The smaller clique uses the initial vertices of the larger palette clique. -/
def twoCliquesPaletteHom {a b : ℕ} (hba : b ≤ a) :
    twoCliques a b →g (⊤ : SimpleGraph (Fin a)) where
  toFun := Sum.elim id (Fin.castLE hba)
  map_rel' := by
    rintro (u | u) (v | v) h
    · exact h
    · simp [twoCliques] at h
    · simp [twoCliques] at h
    · change u ≠ v at h
      change Fin.castLE hba u ≠ Fin.castLE hba v
      intro he
      exact h (Fin.ext (congrArg (fun x : Fin a ↦ x.val) he))

/-- Reuse the same edge palette between the disjoint cliques. -/
def twoCliquesColoring {a b : ℕ} (hba : b ≤ a) :
    (twoCliques a b).edgeSet → (⊤ : SimpleGraph (Fin a)).edgeSet :=
  (twoCliquesPaletteHom hba).mapEdgeSet

theorem twoCliquesColoring_valid {a b : ℕ} (hba : b ≤ a) :
    ValidC7Coloring (twoCliquesColoring hba) := by
  intro F
  have hi : Function.Injective ((twoCliquesPaletteHom hba).comp F.toHom) := by
    intro i j hij
    apply F.injective
    change F i = F j
    change Sum.elim id (Fin.castLE hba) (F i) =
      Sum.elim id (Fin.castLE hba) (F j) at hij
    rcases c7Copy_one_side F with h | h
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

theorem twoCliques_edgeCount (a b : ℕ) :
    EdgeCount (twoCliques a b) = a.choose 2 + b.choose 2 := by
  classical
  unfold EdgeCount twoCliques
  rw [Nat.card_congr edgeSetSumEquiv_compat, Nat.card_sum]
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card,
    card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem twoCliquesColoring_usedColors_le {a b : ℕ} (hba : b ≤ a) :
    usedColors (twoCliquesColoring hba) ≤ a.choose 2 := by
  classical
  convert usedColors_le_card (twoCliquesColoring hba) using 1
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card,
    card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- Transfer the finite disjoint-clique witness to the canonical vertex set `Fin n`. -/
theorem upperBoundAt_of_sizes {ε : ℝ} {n a b : ℕ} (hab : a + b = n) (hba : b ≤ a)
    (hm : exactThreshold n ≤ a.choose 2 + b.choose 2)
    (hc : (a.choose 2 : ℝ) ≤ (1/8 + ε) * (n : ℝ)^2) : UpperBoundAt ε n := by
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
  have hcvalid : ValidC7Coloring c := (twoCliquesColoring_valid hba).comap _
  refine ⟨G, enc ∘ c, ?_, hcvalid.postcomp henc, ?_⟩
  · have he : EdgeCount G = EdgeCount (twoCliques a b) :=
      Nat.card_congr I.symm.mapEdgeSet
    rwa [he, twoCliques_edgeCount]
  · rw [usedColors_postcomp c henc]
    have hcu : usedColors c ≤ a.choose 2 :=
      (usedColors_comap_le _ _).trans (twoCliquesColoring_usedColors_le hba)
    exact (Nat.cast_le.mpr hcu).trans hc

set_option maxHeartbeats 400000 in
/-- A fixed small linear imbalance suffices after an epsilon-dependent cutoff.
This avoids using a selected sequence of orders or an interpolation argument. -/
theorem upper_clique_sizes {ε δ : ℝ} (hδ : 0 < δ)
    (hδε : δ ≤ ε) (hδsmall : δ ≤ 1/8) {n : ℕ}
    (hn : 16 / δ ^ 2 ≤ (n : ℝ)) :
    ∃ a b : ℕ, a + b = n ∧ b ≤ a ∧
      exactThreshold n ≤ a.choose 2 + b.choose 2 ∧
      (a.choose 2 : ℝ) ≤ (1/8 + ε) * (n : ℝ)^2 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hδsq : 0 < δ^2 := sq_pos_of_pos hδ
  have hsize : 16 ≤ δ^2 * (n : ℝ) := by
    have := (div_le_iff₀ hδsq).mp hn
    nlinarith
  have hδone : δ ≤ 1 := by linarith
  have hδsqle : δ^2 ≤ δ := by nlinarith
  have hδn : 16 ≤ δ * (n : ℝ) :=
    hsize.trans (mul_le_mul_of_nonneg_right hδsqle hn0)
  have hn16 : 16 ≤ (n : ℝ) :=
    hδn.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hδone) hn0])
  let a : ℕ := ⌊(1/2 + δ) * (n : ℝ)⌋₊
  let b : ℕ := n - a
  have ha : a ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hab : a + b = n := Nat.add_sub_of_le ha
  have habR : (a : ℝ) + (b : ℝ) = n := by exact_mod_cast hab
  have hau : (a : ℝ) ≤ (1/2 + δ) * (n : ℝ) :=
    Nat.floor_le (by positivity)
  have hal : (1/2 + δ) * (n : ℝ) < (a : ℝ) + 1 := Nat.lt_floor_add_one _
  have hadiff : δ * (n : ℝ) / 2 ≤ (a : ℝ) - (n : ℝ)/2 := by nlinarith
  have hba : b ≤ a := by exact_mod_cast (show (b : ℝ) ≤ a by nlinarith)
  have hdiff0 : 0 ≤ (a : ℝ) - (n : ℝ)/2 := by nlinarith
  have hsq : δ^2 * (n : ℝ)^2 / 4 ≤ ((a : ℝ) - (n : ℝ)/2)^2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (n : ℝ)/2 - δ * (n : ℝ)/2)]
  have hbig : (n : ℝ)/2 + 1 ≤ δ^2 * (n : ℝ)^2 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsize) hn0]
  have hm : (n : ℝ)^2/4 + 1 ≤ (a.choose 2 : ℝ) + (b.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two]
    nlinarith [sq_nonneg ((a : ℝ) + (b : ℝ) - (n : ℝ))]
  have hthresh : (exactThreshold n : ℝ) ≤ (n : ℝ)^2/4 + 1 := by
    have hd : ((n * n / 4 : ℕ) : ℝ) ≤ (n : ℝ)^2/4 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_two] using
        (Nat.cast_div_le (m := n*n) (n := 4) (α := ℝ))
    simp only [exactThreshold, Nat.cast_add, Nat.cast_one]
    linarith
  have hmNat : exactThreshold n ≤ a.choose 2 + b.choose 2 := by
    exact_mod_cast hthresh.trans hm
  have hupper : (a.choose 2 : ℝ) ≤ (1/8 + ε) * (n : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have hsquare : (a : ℝ)^2 ≤ ((1/2 + δ) * (n : ℝ))^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hau) (show 0 ≤ (1/2+δ)*(n:ℝ)+(a:ℝ) by positivity)]
    have hcoef : (1/2+δ)^2/2 ≤ 1/8+ε := by nlinarith only [hδsqle, hδε]
    have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n:ℝ))
    nlinarith only [ha0, hsquare, this]
  exact ⟨a, b, hab, hba, hmNat, hupper⟩

/-- The all-integer asymptotic upper bound, proved with actual eligible finite hosts. -/
theorem asymptoticUpperBound : AsymptoticUpperBound := by
  intro ε hε
  let δ : ℝ := min ε (1/8)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (16 / δ^2)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnR : 16 / δ^2 ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  obtain ⟨a, b, hab, hba, hm, hc⟩ :=
    upper_clique_sizes hδ (min_le_left _ _) (min_le_right _ _) hnR
  exact upperBoundAt_of_sizes hab hba hm hc

end Erdos809
