import Erdos809.Certificate.Sampling
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Four-color graphs on five sampled positions

The ten independent colors belong to pairs of positions, even if sampled
positions later receive equal host vertices. Colors 0, 1, 2, 3 represent
nonedges, nontriangular edges, unselected triangular edges, and selected
triangular edges respectively. The ordering is the frozen verifier's
lexicographic list 01,02,03,04,12,13,14,23,24,34.
-/

namespace Erdos809.Certificate

abbrev LocalGraph := PairPosition 5 → Fin 4

namespace LocalGraph

/-- Symmetric extension to all ordered position pairs, with diagonal zero. -/
def color (g : LocalGraph) (i j : Fin 5) : Fin 4 :=
  if h : i < j then g ⟨(i, j), h⟩
  else if h : j < i then g ⟨(j, i), h⟩ else 0

@[simp] theorem color_diagonal (g : LocalGraph) (i : Fin 5) : color g i i = 0 := by
  simp [color]

theorem color_symm (g : LocalGraph) (i j : Fin 5) : color g i j = color g j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [color, h, not_lt_of_ge h.le]
  · rfl
  · simp [color, h, not_lt_of_ge h.le]

@[simp] theorem color_pair (g : LocalGraph) (e : PairPosition 5) :
    color g e.val.1 e.val.2 = g e := by
  simp [color, e.property]

/-- No triangle of nonzero colors may contain an edge of color 1. Quantifying
over ordered triples automatically covers every placement of the color 1. -/
def Admissible (g : LocalGraph) : Prop :=
  ∀ i j k : Fin 5, color g i j = 1 → color g i k = 0 ∨ color g j k = 0

instance (g : LocalGraph) : Decidable (Admissible g) :=
  inferInstanceAs (Decidable (∀ i j k : Fin 5,
    color g i j = 1 → color g i k = 0 ∨ color g j k = 0))

/-- Pull a graph back along a permutation of its five positions. -/
def relabel (g : LocalGraph) (σ : Equiv.Perm (Fin 5)) : LocalGraph :=
  fun e => color g (σ e.val.1) (σ e.val.2)

@[simp] theorem color_relabel (g : LocalGraph) (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    color (relabel g σ) i j = color g (σ i) (σ j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [color, h, relabel]
  · simp
  · simp only [color, not_lt_of_ge h.le, ↓reduceDIte, h, relabel]
    exact color_symm g _ _

@[simp] theorem relabel_one (g : LocalGraph) : relabel g 1 = g := by
  funext e
  exact color_pair g e

theorem relabel_mul (g : LocalGraph) (σ τ : Equiv.Perm (Fin 5)) :
    relabel (relabel g σ) τ = relabel g (σ * τ) := by
  funext e
  exact color_relabel g σ _ _

theorem admissible_relabel_iff (g : LocalGraph) (σ : Equiv.Perm (Fin 5)) :
    Admissible (relabel g σ) ↔ Admissible g := by
  constructor
  · intro h i j k hij
    have h' := h (σ.symm i) (σ.symm j) (σ.symm k)
    simpa only [color_relabel, Equiv.apply_symm_apply] using h' (by simpa using hij)
  · intro h i j k hij
    simpa only [color_relabel] using h (σ i) (σ j) (σ k) (by simpa using hij)

/-- Pair at a frozen lexicographic coordinate. -/
def pairAt : Fin 10 → PairPosition 5 :=
  ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩, ⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩,
    ⟨(1, 4), by decide⟩, ⟨(2, 3), by decide⟩, ⟨(2, 4), by decide⟩,
    ⟨(3, 4), by decide⟩]

/-- Inverse frozen coordinate, computed without any choice principle. -/
def pairIndex (e : PairPosition 5) : Fin 10 :=
  match e.val.1.val, e.val.2.val with
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2 | 0, 4 => 3
  | 1, 2 => 4 | 1, 3 => 5 | 1, 4 => 6
  | 2, 3 => 7 | 2, 4 => 8 | _, _ => 9

/-- Exact ordering equivalence with the ten pairs used in the frozen data. -/
def lexPairEquiv : Fin 10 ≃ PairPosition 5 where
  toFun := pairAt
  invFun := pairIndex
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def ofDigits (d : Fin 10 → Fin 4) : LocalGraph := fun e => d (pairIndex e)
def digits (g : LocalGraph) : Fin 10 → Fin 4 := fun i => g (pairAt i)

@[simp] theorem digits_ofDigits (d : Fin 10 → Fin 4) : digits (ofDigits d) = d := by
  funext i
  exact congrArg d (lexPairEquiv.left_inv i)

@[simp] theorem ofDigits_digits (g : LocalGraph) : ofDigits (digits g) = g := by
  funext e
  exact congrArg g (lexPairEquiv.right_inv e)

/-- Base-four enumeration, with the first frozen coordinate as the least
significant digit. This order affects only enumeration, not graph semantics. -/
def codeEquiv : LocalGraph ≃ Fin (4 ^ 10) where
  toFun g := finFunctionFinEquiv (digits g)
  invFun c := ofDigits (finFunctionFinEquiv.symm c)
  left_inv g := by simp
  right_inv c := by
    simp only [digits_ofDigits]
    exact finFunctionFinEquiv.apply_symm_apply c

/-- Every graph on five positions occurs in the explicit base-four universe. -/
theorem exists_code (g : LocalGraph) : ∃ c : Fin (4 ^ 10), codeEquiv.symm c = g :=
  codeEquiv.symm.surjective g

end LocalGraph
end Erdos809.Certificate
