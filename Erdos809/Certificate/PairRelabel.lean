module
public import Erdos809.Certificate.Sampling
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-! Reindex fresh independent marks on unordered pairs of sample positions.
The proof constructs the permutation of increasing endpoint pairs explicitly.
Aristotle supplied the proof; local Lean kernel validation is authoritative.
-/

namespace Erdos809.Certificate

theorem prod_pairPosition_relabel {M : Type*} [CommMonoid M]
    (n : ℕ) (f : Fin n → Fin n → M)
    (hsymm : ∀ i j, f i j = f j i) (σ : Equiv.Perm (Fin n)) :
    (∏ e : PairPosition n, f (σ e.1.1) (σ e.1.2)) =
      ∏ e : PairPosition n, f e.1.1 e.1.2 := by
  let g : Equiv.Perm (Fin n) → PairPosition n → PairPosition n := fun τ e =>
    ⟨(min (τ e.1.1) (τ e.1.2), max (τ e.1.1) (τ e.1.2)), by
      have : τ e.1.1 ≠ τ e.1.2 := fun h => (ne_of_lt e.2) (τ.injective h)
      simp only
      rcases lt_or_gt_of_ne this with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact h
      · rw [min_eq_right h.le, max_eq_left h.le]; exact h⟩
  have key : ∀ τ : Equiv.Perm (Fin n), ∀ e, g τ⁻¹ (g τ e) = e := by
    intro τ ⟨⟨a, b⟩, hab⟩
    have hne : τ a ≠ τ b := fun h => (ne_of_lt hab) (τ.injective h)
    apply Subtype.ext
    rcases lt_or_gt_of_ne hne with h | h
    · have hab' : a ≤ b := hab.le
      simp [g, min_eq_left h.le, max_eq_right h.le, hab']
    · have hab' : a ≤ b := hab.le
      simp [g, min_eq_right h.le, max_eq_left h.le, hab']
  have key' : ∀ e, g σ (g σ⁻¹ e) = e := by
    intro e
    have := key σ⁻¹ e
    rwa [inv_inv] at this
  let E : PairPosition n ≃ PairPosition n :=
    ⟨g σ, g σ⁻¹, key σ, key'⟩
  apply Fintype.prod_equiv E
  rintro ⟨⟨a, b⟩, hab⟩
  have hne : σ a ≠ σ b := fun h => (ne_of_lt hab) (σ.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · simp [E, g, min_eq_left h.le, max_eq_right h.le]
  · simp [E, g, min_eq_right h.le, max_eq_left h.le, hsymm (σ a)]

end Erdos809.Certificate
