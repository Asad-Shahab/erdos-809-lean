module
public import Erdos809.LongOddCycles.ScalarBounds

@[expose] public section

/-! A proved existential cutoff for the scalar conditions in the BCM induction.
The cutoff depends only on the cycle parameter and the error tolerance. -/

noncomputable section

namespace Erdos809.LongOddCycles

lemma epsilon_cube_bounds (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε < 1 / 100) :
    0 ≤ ε ^ 3 ∧ ε ^ 3 ≤ ε / 10000 ∧ ε ^ 3 ≤ 1 / 1000 := by
  have hsq : ε ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hε hεsmall.le 2
  have hcube : ε ^ 3 ≤ ε / 10000 := by
    have := mul_le_mul_of_nonneg_left hsq hε
    nlinarith
  exact ⟨by positivity, hcube, by linarith⟩

lemma far_sqrt_margin (k ε n : ℝ) (hk : 4 ≤ k) (hn : 0 ≤ n) (hε : 0 ≤ ε)
    (hquad : 100 * k * n ≤ ε ^ 8 * n ^ 2) (hlinear : 100 * k ≤ ε ^ 4 * n) :
    Real.sqrt (2 * k * n) + 2 * k + 1 ≤ ε ^ 4 * n := by
  have hsqrt : Real.sqrt (2 * k * n) ≤ ε ^ 4 * n / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hkn : 0 ≤ k * n := mul_nonneg (by linarith) hn
      nlinarith only [hquad, hkn]
  linarith

/-- A finite list of numerical inequalities sufficient for every terminal
argument; none mentions the host, its edges, or its coloring. -/
structure ScalarScale (k ε n : ℝ) : Prop where
  order : 100 ≤ n
  order_cycle : 100 * k ≤ n
  error_cycle : 20 * k ≤ ε * n
  far_surplus : 100 * k * n ≤ ε ^ 6 * n ^ 2
  far_margin : Real.sqrt (2 * k * n) + 2 * k + 1 ≤ ε ^ 4 * n
  near_left : 0 ≤ n / 2 - ε ^ 3 * n - 3 / 2 - 5 * k
  near_right : 0 ≤ n / 2 - 3 * ε ^ 3 * n - 10 * k - 5 / 2
  near_common : 0 ≤ n / 4 - 3 * ε ^ 3 * n - 15 * k - 5 / 2
  greedy : 2 * k ≤ n / 2 - ε ^ 3 * n - 1 / 2
  book_selection : 2 * ε ^ 3 * n + 9 < n / 8
  book_degree : n / 8 ≤ n / 6 - ε ^ 3 * n - 1 / 2
  absorption : (5 * ε ^ 3 / 2 + (ε ^ 3) ^ 2 / 2) * n ^ 2 + 10 * k * n ≤
    ε * n ^ 2

lemma scalarScale_of_bounds (k ε n : ℝ) (hk : 4 ≤ k)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100)
    (hn : 100 ≤ n) (hnk : 100 * k ≤ n) (hen : 20 * k ≤ ε * n)
    (h6 : 100 * k * n ≤ ε ^ 6 * n ^ 2)
    (h8 : 100 * k * n ≤ ε ^ 8 * n ^ 2)
    (h4 : 100 * k ≤ ε ^ 4 * n) : ScalarScale k ε n := by
  obtain ⟨ha, haε, hasmall⟩ := epsilon_cube_bounds ε hε.le hεsmall
  have han : ε ^ 3 * n ≤ n / 1000 := by
    have := mul_le_mul_of_nonneg_right hasmall (show 0 ≤ n by linarith)
    linarith
  have haone : (ε ^ 3) ^ 2 ≤ ε ^ 3 := by nlinarith
  have haabsorb : 5 * ε ^ 3 / 2 + (ε ^ 3) ^ 2 / 2 ≤ ε / 2 := by
    nlinarith
  have hquad := mul_le_mul_of_nonneg_right haabsorb (sq_nonneg n)
  have hlinear := mul_le_mul_of_nonneg_right hen (show 0 ≤ n by linarith)
  refine ⟨hn, hnk, hen, h6, far_sqrt_margin k ε n hk (by linarith) hε.le h8 h4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Existence of a uniform natural cutoff proving the complete scalar ledger.
An existential cutoff avoids irrelevant optimization of BCM's error constant. -/
theorem exists_scalarScale_cutoff (k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∃ M : ℕ, ∀ n : ℝ, (M : ℝ) ≤ n → ScalarScale (k : ℝ) ε n := by
  obtain ⟨M, hM⟩ := exists_nat_ge
    (max 100 (max (100 * (k : ℝ)) (max (20 * (k : ℝ) / ε)
      (max (100 * (k : ℝ) / ε ^ 6)
        (max (100 * (k : ℝ) / ε ^ 8) (100 * (k : ℝ) / ε ^ 4))))))
  refine ⟨M, ?_⟩
  intro n hMn
  have hb := le_trans hM hMn
  simp only [max_le_iff] at hb
  rcases hb with ⟨hn, hnk, he, h6, h8, h4⟩
  have hn0 : 0 ≤ n := by linarith
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hen : 20 * (k : ℝ) ≤ ε * n := by
    have := (div_le_iff₀ hε).mp he
    nlinarith only [this]
  have hp6 : 0 < ε ^ 6 := pow_pos hε _
  have hp8 : 0 < ε ^ 8 := pow_pos hε _
  have hp4 : 0 < ε ^ 4 := pow_pos hε _
  have h6n := mul_le_mul_of_nonneg_right ((div_le_iff₀ hp6).mp h6) hn0
  have h8n := mul_le_mul_of_nonneg_right ((div_le_iff₀ hp8).mp h8) hn0
  have h4n := (div_le_iff₀ hp4).mp h4
  apply scalarScale_of_bounds (k : ℝ) ε n hkR hε hεsmall hn hnk hen
  · nlinarith only [h6n]
  · nlinarith only [h8n]
  · nlinarith only [h4n]

lemma ScalarScale.far_surplus_ge (k ε n s : ℝ) (hk : 4 ≤ k)
    (hscale : ScalarScale k ε n) (hs : ε ^ 6 * n ^ 2 ≤ s) :
    2 * k * n + 4 ≤ s := by
  have hkn : 400 ≤ k * n := by
    nlinarith [hscale.order]
  linarith [hscale.far_surplus]

lemma ScalarScale.far_surplus_gt_order (k ε n s : ℝ) (hk : 4 ≤ k)
    (hscale : ScalarScale k ε n) (hs : ε ^ 6 * n ^ 2 ≤ s) : n < s := by
  have hkn : 4 * n ≤ k * n := by
    nlinarith [hscale.order]
  linarith [hscale.far_surplus, hscale.order]

/-- The far terminal branch obtains precisely the robust-four-path degree
condition, together with the greedy-extension budget. -/
lemma far_degree_of_comparison (k n m d ε C : ℝ) (hk : 4 ≤ k)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hscale : ScalarScale k ε n)
    (hm : n ^ 2 / 4 < m) (hmupper : m ≤ n ^ 2 / 2)
    (hfar : ε ^ 6 * n ^ 2 ≤ m - n ^ 2 / 4)
    (hcompare : bcmPotential (n - 1) (m - d) - ε * (n - 1) ^ 2 - C <
      bcmPotential n m - ε * n ^ 2 - C) :
    4 ≤ m - n ^ 2 / 4 - 2 * k * n ∧
    n / 2 - Real.sqrt (m - n ^ 2 / 4 - 2 * k * n) + 2 * k ≤ d ∧
    2 * k ≤ d := by
  have hn0 : 0 ≤ n := by linarith [hscale.order]
  have hr0 : 0 ≤ 2 * k * n := by positivity
  have hs := hscale.far_surplus_ge k ε n (m - n ^ 2 / 4) hk hfar
  have hdiff := sqrt_sub_gap_le (m - n ^ 2 / 4) (2 * k * n) hr0 (by linarith)
  have htlow : ε ^ 3 * n ≤ Real.sqrt (m - n ^ 2 / 4) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hfar]
  have htmul := mul_le_mul_of_nonneg_left htlow hε.le
  have hd := induction_degree_comparison n m d ε C (by linarith [hscale.order])
    hm hmupper hε hεsmall hcompare
  have hrob : n / 2 - Real.sqrt (m - n ^ 2 / 4 - 2 * k * n) + 2 * k ≤ d := by
    nlinarith [hscale.far_margin, Real.sqrt_nonneg (2 * k * n)]
  have htsmall : Real.sqrt (m - n ^ 2 / 4 - 2 * k * n) ≤ n / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  exact ⟨by linarith, hrob, by linarith⟩

/-- The near terminal degree condition follows from either branch of the
vertex-deletion eligibility split. -/
lemma near_degree_of_terminal_split (k n m d ε C : ℝ) (hk : 4 ≤ k)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) (hscale : ScalarScale k ε n)
    (hm : n ^ 2 / 4 < m) (hmupper : m ≤ n ^ 2 / 2)
    (hnear : m - n ^ 2 / 4 < ε ^ 6 * n ^ 2)
    (hterminal : m - d ≤ (n - 1) ^ 2 / 4 ∨
      bcmPotential (n - 1) (m - d) - ε * (n - 1) ^ 2 - C <
        bcmPotential n m - ε * n ^ 2 - C) :
    n / 2 - ε ^ 3 * n - 1 / 2 < d := by
  rcases hterminal with hineligible | hcompare
  · exact near_degree_of_deleted_ineligible n m d (ε ^ 3)
      (by linarith [hscale.order]) (by positivity) hm hineligible
  · exact near_degree_of_comparison n m d ε C (by linarith [hscale.order])
      hm hmupper hε hεsmall hnear hcompare

end Erdos809.LongOddCycles
