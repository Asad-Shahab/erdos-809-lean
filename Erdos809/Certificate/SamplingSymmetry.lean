module
public import Erdos809.Certificate.PairRelabel

@[expose] public section

/-! Exchangeability of the finite colored sampling law. The theorem reindexes
both vertex choices and independent marks on pairs of sample positions. -/

namespace Erdos809.Certificate

variable {V : Type*} [Fintype V]

theorem typeWeight_relabel (x : VertexWeights V) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (v : Fin n → V) :
    typeWeight x (v ∘ σ) = typeWeight x v :=
  Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem sampleWeight_relabel (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → V)
    (color : Fin n → Fin n → Fin 4) (hcolor : ∀ i j, color i j = color j i) :
    sampleWeight x κ (v ∘ σ) (fun e => color (σ e.1.1) (σ e.1.2)) =
      sampleWeight x κ v (fun e => color e.1.1 e.1.2) := by
  unfold sampleWeight
  rw [typeWeight_relabel]
  congr 1
  exact prod_pairPosition_relabel n (fun i j => κ.prob (v i) (v j) (color i j))
    (fun i j => (hκ (v i) (v j) (color i j)).trans
      (congrArg (κ.prob (v j) (v i)) (hcolor i j))) σ

noncomputable def coloredDensity (x : VertexWeights V) (κ : ColorKernel V)
    {n : ℕ} (color : Fin n → Fin n → Fin 4) : ℝ :=
  ∑ v : Fin n → V, sampleWeight x κ v (fun e => color e.1.1 e.1.2)

theorem coloredDensity_nonnegative (x : VertexWeights V) (κ : ColorKernel V)
    {n : ℕ} (color : Fin n → Fin n → Fin 4) : 0 ≤ coloredDensity x κ color :=
  Finset.sum_nonneg fun v _ => sampleWeight_nonnegative x κ v _

theorem coloredDensity_relabel (x : VertexWeights V) (κ : ColorKernel V)
    (hκ : ∀ u v c, κ.prob u v c = κ.prob v u c)
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (color : Fin n → Fin n → Fin 4) (hcolor : ∀ i j, color i j = color j i) :
    coloredDensity x κ (fun i j => color (σ i) (σ j)) = coloredDensity x κ color := by
  let e : (Fin n → V) ≃ (Fin n → V) :=
    { toFun := fun v => v ∘ σ
      invFun := fun v => v ∘ σ.symm
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp }
  unfold coloredDensity
  calc
    _ = ∑ v : Fin n → V,
        sampleWeight x κ (v ∘ σ) (fun e => color (σ e.1.1) (σ e.1.2)) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := Finset.sum_congr rfl fun v _ => sampleWeight_relabel x κ hκ σ v color hcolor

end Erdos809.Certificate
