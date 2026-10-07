module
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Scalar inequalities for the Bucić--Chen--Ma longer odd-cycle argument.

All variables in this file are real numbers. Graph orders, edge counts, and
minimum degrees are cast to these variables by the graph-theoretic modules.
-/

noncomputable section

namespace Erdos809.LongOddCycles

/-- The one-sided induction potential, distinct from the C₇ potential. -/
def bcmPotential (n m : ℝ) : ℝ :=
  m / 2 + n / 2 * Real.sqrt (m - n ^ 2 / 4)

/-- Quadratic appearing at the end of the repaired exact-four-path proof. -/
def fourPathPolynomial (n b : ℝ) : ℝ :=
  n ^ 2 - 2 * b * (n - b) + 2 * (n - b) - n + 4

lemma bcmPotential_lower (n m : ℝ) (hn : 0 ≤ n) (hm : n ^ 2 / 4 ≤ m) :
    n ^ 2 / 8 ≤ bcmPotential n m := by
  have := mul_nonneg hn (Real.sqrt_nonneg (m - n ^ 2 / 4))
  unfold bcmPotential
  nlinarith

lemma surplus_sqrt_le_half (n m : ℝ) (hn : 0 ≤ n) (hm : m ≤ n ^ 2 / 2) :
    Real.sqrt (m - n ^ 2 / 4) ≤ n / 2 := by
  apply (Real.sqrt_le_iff).2
  constructor <;> nlinarith

lemma bcmPotential_upper (n m : ℝ) (hn : 0 ≤ n) (hm : m ≤ n ^ 2 / 2) :
    bcmPotential n m ≤ n ^ 2 / 2 := by
  have ht := surplus_sqrt_le_half n m hn hm
  have := mul_le_mul_of_nonneg_left ht hn
  unfold bcmPotential
  nlinarith

lemma bcmPotential_base (n m M ε : ℝ) (hn : 0 ≤ n) (hnM : n ≤ M)
    (hε : 0 ≤ ε) (hm : m ≤ n ^ 2 / 2) :
    bcmPotential n m - ε * n ^ 2 - M ^ 2 / 2 ≤ 0 := by
  have hpot := bcmPotential_upper n m hn hm
  have : 0 ≤ ε * n ^ 2 := mul_nonneg hε (sq_nonneg n)
  nlinarith

/-- An ineligible deleted host yields a degree bound directly, without applying
induction or taking a positive square root of the deleted surplus. -/
lemma degree_of_deleted_ineligible (n m d : ℝ)
    (hdel : m - d ≤ (n - 1) ^ 2 / 4) :
    m - n ^ 2 / 4 + n / 2 - 1 / 4 ≤ d := by
  nlinarith

lemma near_degree_of_deleted_ineligible (n m d a : ℝ) (hn : 0 ≤ n)
    (ha : 0 ≤ a) (hm : n ^ 2 / 4 < m)
    (hdel : m - d ≤ (n - 1) ^ 2 / 4) :
    n / 2 - a * n - 1 / 2 < d := by
  have hd := degree_of_deleted_ineligible n m d hdel
  have := mul_nonneg ha hn
  linarith

lemma deleted_eligible_of_large_surplus (n m d : ℝ)
    (hs : n ≤ m - n ^ 2 / 4) (hd : d ≤ n - 1) (hn : 0 ≤ n) :
    (n - 1) ^ 2 / 4 < m - d := by
  nlinarith

/-- Every denominator and radicand in the rationalized induction estimate is
strictly positive. The estimate also includes the zero-surplus endpoint. -/
lemma rationalized_sqrt_gap (t ε : ℝ) (ht : 0 ≤ t)
    (hε : 0 ≤ ε) (hεsmall : ε < 1 / 2) :
    0 < (t + 1 / 2) ^ 2 - 2 * ε * t ∧
    0 < t + 1 / 2 + Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t) ∧
    t + 1 / 2 - Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t) =
      (2 * ε * t) / (t + 1 / 2 + Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t)) ∧
    t + 1 / 2 - Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t) ≤ 2 * ε := by
  have hr : 0 < (t + 1 / 2) ^ 2 - 2 * ε * t := by
    have := mul_nonneg ht (show 0 ≤ 1 - 2 * ε by linarith)
    nlinarith [sq_nonneg t]
  have hs := Real.sqrt_nonneg ((t + 1 / 2) ^ 2 - 2 * ε * t)
  have hsq := Real.sq_sqrt hr.le
  have hden : 0 < t + 1 / 2 + Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t) := by
    linarith
  have hid : t + 1 / 2 - Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t) =
      (2 * ε * t) / (t + 1 / 2 + Real.sqrt ((t + 1 / 2) ^ 2 - 2 * ε * t)) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    nlinarith
  refine ⟨hr, hden, hid, ?_⟩
  rw [hid]
  apply (div_le_iff₀ hden).2
  have := mul_nonneg hε hs
  nlinarith

/-- The terminal minimum-degree estimate obtained when deleting a vertex does
not decrease the penalized potential. No estimate is made on an ineligible
smaller host here; that case has its separate direct lemma above. -/
lemma induction_degree_comparison (n m d ε C : ℝ)
    (hn : 1 ≤ n) (hm : n ^ 2 / 4 < m) (hmupper : m ≤ n ^ 2 / 2)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100)
    (hcompare : bcmPotential (n - 1) (m - d) - ε * (n - 1) ^ 2 - C <
      bcmPotential n m - ε * n ^ 2 - C) :
    n / 2 - Real.sqrt (m - n ^ 2 / 4) - 1 / 2 +
      2 * ε * Real.sqrt (m - n ^ 2 / 4) < d := by
  set t := Real.sqrt (m - n ^ 2 / 4) with htdef
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = m - n ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have htn : t ≤ n / 2 := surplus_sqrt_le_half n m (by linarith) hmupper
  obtain ⟨hr, hden, hid, hgap⟩ := rationalized_sqrt_gap t ε ht hε.le (by linarith)
  by_contra! hd
  have hrad : (t + 1 / 2) ^ 2 - 2 * ε * t ≤
      (m - d) - (n - 1) ^ 2 / 4 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  have hmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ n - 1 by linarith)
  have hgapmul := mul_le_mul_of_nonneg_left hgap (show 0 ≤ n - 1 by linarith)
  have htnmul := mul_le_mul_of_nonneg_left htn hε.le
  have hnε : 0 < ε * n := mul_pos hε (by linarith)
  unfold bcmPotential at hcompare
  rw [← htdef] at hcompare
  nlinarith

lemma near_degree_of_comparison (n m d ε C : ℝ)
    (hn : 1 ≤ n) (hm : n ^ 2 / 4 < m) (hmupper : m ≤ n ^ 2 / 2)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100)
    (hnear : m - n ^ 2 / 4 < ε ^ 6 * n ^ 2)
    (hcompare : bcmPotential (n - 1) (m - d) - ε * (n - 1) ^ 2 - C <
      bcmPotential n m - ε * n ^ 2 - C) :
    n / 2 - ε ^ 3 * n - 1 / 2 < d := by
  have hd := induction_degree_comparison n m d ε C hn hm hmupper hε hεsmall hcompare
  have htn : Real.sqrt (m - n ^ 2 / 4) ≤ ε ^ 3 * n := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith only [hnear]
  have := mul_nonneg hε.le (Real.sqrt_nonneg (m - n ^ 2 / 4))
  linarith

lemma fourPathThreshold_pos (n m : ℝ) (hn : 0 < n)
    (hm : m ≤ n * (n - 1) / 2) :
    2 < n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2 := by
  have ht : Real.sqrt (m - n ^ 2 / 4) < n / 2 := by
    apply (Real.sqrt_lt' (by linarith)).2
    nlinarith
  linarith

lemma fourPathParameter_le_half (n m : ℝ) (hn : 6 ≤ n)
    (hm : n ^ 2 / 4 + 4 ≤ m) :
    max 3 (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2) ≤ n / 2 := by
  have hs : 2 ≤ Real.sqrt (m - n ^ 2 / 4) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  apply max_le <;> linarith

lemma fourPathPolynomial_sub (n a b : ℝ) :
    fourPathPolynomial n b - fourPathPolynomial n a =
      2 * (b - a) * (b + a - n - 1) := by
  unfold fourPathPolynomial
  ring

lemma fourPathPolynomial_antitone (n a b : ℝ)
    (hab : a ≤ b) (ha : a ≤ n / 2) (hb : b ≤ n / 2) :
    fourPathPolynomial n b ≤ fourPathPolynomial n a := by
  have hp : 2 * (b - a) * (b + a - n - 1) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · linarith
    · linarith
  rw [← fourPathPolynomial_sub] at hp
  linarith

lemma fourPathPolynomial_threshold (n m : ℝ) (hm : n ^ 2 / 4 ≤ m) :
    fourPathPolynomial n (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2) =
      2 * m + 8 - 6 * Real.sqrt (m - n ^ 2 / 4) := by
  have hs := Real.sq_sqrt (show 0 ≤ m - n ^ 2 / 4 by linarith)
  unfold fourPathPolynomial
  nlinarith

lemma fourPathPolynomial_le (n m : ℝ) (hn : 6 ≤ n)
    (hm : n ^ 2 / 4 + 4 ≤ m) :
    fourPathPolynomial n (max 3 (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2)) ≤
      2 * m - 4 := by
  have hb := fourPathParameter_le_half n m hn hm
  have hs : 2 ≤ Real.sqrt (m - n ^ 2 / 4) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hmono := fourPathPolynomial_antitone n
    (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2)
    (max 3 (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2))
    (le_max_right _ _) (by linarith) hb
  rw [fourPathPolynomial_threshold n m (by linarith)] at hmono
  linarith

lemma fourPathPolynomial_contradiction (n m : ℝ) (hn : 6 ≤ n)
    (hm : n ^ 2 / 4 + 4 ≤ m)
    (hcount : 2 * m ≤
      fourPathPolynomial n (max 3 (n / 2 - Real.sqrt (m - n ^ 2 / 4) + 2))) :
    False := by
  have := fourPathPolynomial_le n m hn hm
  linarith

/-- Scalar endgame of the maximum-degree branch in BCM Lemma 3.1. -/
lemma shortCore_first_scalar (n m C₁ C₂ Δ : ℝ)
    (hadd : C₁ + C₂ = n) (hprod : C₁ * C₂ = n * (n - 1) / 2 - m)
    (hcoef : 0 < 2 * C₁ - n)
    (hcount : 2 * m ≤ Δ * (2 * C₁ - n) + (n - 2) * (n - C₁)) :
    C₁ - 1 ≤ Δ := by
  have hC₂ : C₂ = n - C₁ := by linarith
  rw [hC₂] at hprod
  by_contra! hΔ
  have hmul := mul_pos (show 0 < C₁ - 1 - Δ by linarith) hcoef
  nlinarith

/-- Scalar endgame of the separated-neighborhood branch in BCM Lemma 3.1.
The strict sign of the denominator is exposed as a hypothesis. -/
lemma shortCore_final_scalar (n m C₁ C₂ Δ X : ℝ)
    (hadd : C₁ + C₂ = n) (hprod : C₁ * C₂ = n * (n - 1) / 2 - m)
    (hden : 0 < n - 2 * X - 2)
    (hcount : 2 * m ≤ (Δ - C₂) * (n - 2 * X - 2) +
      2 * (X + 1) * (n - X - 2)) :
    C₁ - 1 ≤ Δ := by
  have hC₂ : C₂ = n - C₁ := by linarith
  rw [hC₂] at hprod
  by_contra! hΔ
  have hmul := mul_pos (show 0 < C₁ - 1 - Δ by linarith) hden
  rw [hC₂] at hcount
  nlinarith [sq_nonneg (n - C₁ - 1 - X)]

lemma shortCore_parameters (n m : ℝ) (hn : 0 ≤ n)
    (hmlower : n ^ 2 / 4 ≤ m) (hmupper : m ≤ n * (n - 1) / 2) :
    let C₁ := n / 2 + Real.sqrt (m - n ^ 2 / 4 + n / 2)
    let C₂ := n - C₁
    0 ≤ C₂ ∧ C₂ ≤ C₁ ∧ C₁ ≤ n ∧ C₁ + C₂ = n ∧
      C₁ * C₂ = n * (n - 1) / 2 - m := by
  dsimp
  have hs := Real.sqrt_nonneg (m - n ^ 2 / 4 + n / 2)
  have hsq := Real.sq_sqrt (show 0 ≤ m - n ^ 2 / 4 + n / 2 by linarith)
  have hupper : Real.sqrt (m - n ^ 2 / 4 + n / 2) ≤ n / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_⟩
  nlinarith

/-- The incident-edge complement count gives exactly the BCM potential. -/
lemma incident_edge_potential (n m A e : ℝ) (hn : 0 ≤ n)
    (hm : n ^ 2 / 4 ≤ m) (hA : n / 2 + Real.sqrt (m - n ^ 2 / 4) ≤ A)
    (hAn : A ≤ n) (hcount : m - (n - A) ^ 2 / 2 ≤ e) :
    bcmPotential n m ≤ e := by
  have hs := Real.sqrt_nonneg (m - n ^ 2 / 4)
  have hsq := Real.sq_sqrt (show 0 ≤ m - n ^ 2 / 4 by linarith)
  have hprod := mul_nonneg (show 0 ≤ n / 2 - Real.sqrt (m - n ^ 2 / 4) - (n - A) by linarith)
    (show 0 ≤ n / 2 - Real.sqrt (m - n ^ 2 / 4) + (n - A) by linarith)
  unfold bcmPotential
  nlinarith

lemma bcmPotential_near_upper (n m a : ℝ) (hn : 0 ≤ n) (ha : 0 ≤ a)
    (hnear : m - n ^ 2 / 4 ≤ a ^ 2 * n ^ 2) :
    bcmPotential n m ≤ n ^ 2 / 8 + (a ^ 2 + a) * n ^ 2 / 2 := by
  have hsqrt : Real.sqrt (m - n ^ 2 / 4) ≤ a * n := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg ha hn, by nlinarith only [hnear]⟩
  have hmul := mul_le_mul_of_nonneg_left hsqrt hn
  unfold bcmPotential
  nlinarith

/-- Shared absorption step for the dense-neighborhood and good-edge counts. -/
lemma near_palette_absorption (n m a k ε q : ℝ) (hn : 0 ≤ n) (ha : 0 ≤ a)
    (hnear : m - n ^ 2 / 4 ≤ a ^ 2 * n ^ 2)
    (habsorb : (5 * a / 2 + a ^ 2 / 2) * n ^ 2 + 10 * k * n ≤ ε * n ^ 2)
    (hcount : n ^ 2 / 8 - 2 * a * n ^ 2 - 10 * k * n ≤ q) :
    bcmPotential n m - ε * n ^ 2 ≤ q := by
  have hpot := bcmPotential_near_upper n m a hn ha hnear
  nlinarith

/-- The strict-density short-core argument can use the weaker square root
sqrt(m - n²/4), leaving a positive `n` of slack in its contradiction. -/
lemma shortCore_strict_first_contradiction (n m c d Δ : ℝ)
    (hn : 0 < n) (hadd : c + d = n) (hprod : 2 * m = n ^ 2 - 2 * c * d)
    (hcoef : 0 ≤ 2 * c - n) (hΔ : Δ ≤ c - 1)
    (hcount : 2 * m ≤ c * Δ + (n - c) * (n - Δ - 2)) : False := by
  have hd : d = n - c := by linarith
  rw [hd] at hprod
  have hmul := mul_nonneg (show 0 ≤ c - 1 - Δ by linarith) hcoef
  nlinarith

lemma shortCore_strict_final_contradiction (n m c d Δ X : ℝ)
    (hn : 0 < n) (hadd : c + d = n) (hprod : 2 * m = n ^ 2 - 2 * c * d)
    (hcoef : 0 ≤ n - 2 * X - 2) (hΔ : Δ ≤ c - 1)
    (hcount : 2 * m ≤ (Δ - d) * (n - 2 * X - 2) +
      2 * (X + 1) * (n - X - 2)) : False := by
  have hd : d = n - c := by linarith
  rw [hd] at hprod hcount
  have hmul := mul_nonneg (show 0 ≤ c - 1 - Δ by linarith) hcoef
  nlinarith [sq_nonneg (n - c - X - 1)]

lemma shortCore_strict_parameters (n m : ℝ) (hn : 0 ≤ n)
    (hmlower : n ^ 2 / 4 ≤ m) (hmupper : m ≤ n ^ 2 / 2) :
    let c := n / 2 + Real.sqrt (m - n ^ 2 / 4)
    let d := n - c
    0 ≤ d ∧ d ≤ c ∧ c ≤ n ∧ c + d = n ∧
      2 * m = n ^ 2 - 2 * c * d := by
  dsimp
  have hs := Real.sqrt_nonneg (m - n ^ 2 / 4)
  have hsq := Real.sq_sqrt (show 0 ≤ m - n ^ 2 / 4 by linarith)
  have hupper := surplus_sqrt_le_half n m hn hmupper
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_⟩
  nlinarith

lemma sqrt_sub_gap_le (s r : ℝ) (hr : 0 ≤ r) (hs : r ≤ s) :
    Real.sqrt s - Real.sqrt (s - r) ≤ Real.sqrt r := by
  have hsq1 := Real.sq_sqrt (show 0 ≤ s - r by linarith)
  have hsq2 := Real.sq_sqrt hr
  have hnon1 := Real.sqrt_nonneg (s - r)
  have hnon2 := Real.sqrt_nonneg r
  have hprod := mul_nonneg hnon1 hnon2
  have hbound : Real.sqrt s ≤ Real.sqrt (s - r) + Real.sqrt r := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  linarith

lemma near_neighborhood_product (n k a L R : ℝ) (hn : 0 ≤ n)
    (hk : 4 ≤ k) (ha : 0 ≤ a)
    (hL : n / 2 - a * n - 3 / 2 - 5 * k ≤ L)
    (hR : n / 2 - 3 * a * n - 10 * k - 5 / 2 ≤ R)
    (hL0 : 0 ≤ n / 2 - a * n - 6 * k)
    (hR0 : 0 ≤ n / 2 - 3 * a * n - 11 * k) :
    n ^ 2 / 8 - 2 * a * n ^ 2 - 10 * k * n ≤ L * R / 2 := by
  have hL' : n / 2 - a * n - 6 * k ≤ L := by linarith
  have hR' : n / 2 - 3 * a * n - 11 * k ≤ R := by linarith
  have hp := mul_le_mul hL' hR' hR0 (show 0 ≤ L by linarith)
  have han : 0 ≤ a * n := mul_nonneg ha hn
  have hakn : 0 ≤ a * k * n := by positivity
  have hkn : 0 ≤ k * n := by positivity
  have hann : 0 ≤ a * n ^ 2 := by positivity
  have haknn : 0 ≤ a * k * n := by positivity
  nlinarith [sq_nonneg (a * n), sq_nonneg k]

lemma near_good_edge_product (n k a d : ℝ) (hn : 0 ≤ n)
    (hk : 4 ≤ k) (ha : 0 ≤ a)
    (hbase : 2 ≤ n / 2 - a * n - 1 / 2)
    (hd : n / 2 - a * n - 1 / 2 ≤ d) :
    n ^ 2 / 8 - 2 * a * n ^ 2 - 10 * k * n ≤ (d - 1) * (d - 2) / 2 := by
  have hp := mul_nonneg (show 0 ≤ d - (n / 2 - a * n - 1 / 2) by linarith)
    (show 0 ≤ d + (n / 2 - a * n - 1 / 2) - 3 by linarith)
  have han : 0 ≤ a * n := mul_nonneg ha hn
  have hann : 0 ≤ a * n ^ 2 := by positivity
  have hkn : 4 * n ≤ k * n := by nlinarith
  nlinarith [sq_nonneg (a * n)]

end Erdos809.LongOddCycles
