module
public import Erdos809.LongOddCycles.FiniteLower
public import Erdos809.LongOddCycles.FinalInterface
public import Erdos809.Source.NearCutLower

@[expose] public section

/-! BCM's longer-cycle lower bound at the exact one-edge threshold, combined
with the existing two-clique upper construction and actual minimum attainment. -/
namespace Erdos809
open LongOddCycles

/-- For every fixed k≥4, every sufficiently large eligible host and every
valid coloring use at least (1/8−ε)n² colors. The constant is uniform over hosts
and arbitrary color types; the order cutoff may depend on k and ε. -/
theorem longOddCycle_asymptoticLowerBound (k : ℕ) (hk : 4 ≤ k) :
    CycleAsymptoticLowerBound (2 * k + 1) := by
  intro ε hε
  let η : ℝ := min (ε / 4) (1 / 200)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η < 1 / 100 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηε : η ≤ ε / 2 := by
    have h := min_le_left (ε / 4) (1 / 200 : ℝ)
    dsimp [η]
    linarith
  obtain ⟨C, hC, hfinite⟩ := longOddCycle_finiteLower k hk η hη hηsmall
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (2 * C / ε))
  refine ⟨N, ?_⟩
  intro n hn G K c hm hc
  classical
  have hnR : max 1 (2 * C / ε) ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans hnR
  have hnC : 2 * C / ε ≤ (n : ℝ) := (le_max_right _ _).trans hnR
  have hmul := (div_le_iff₀ hε).mp hnC
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have habs : C ≤ ε / 2 * (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsq hε.le
    nlinarith
  have hsurplus : (Fintype.card (Fin n) : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) :=
    Source.real_excess_of_exactThreshold (by simpa using hm)
  have hbound := hfinite (Fin n) G K c hc hsurplus
  have hpot := bcmPotential_lower (n : ℝ) G.edgeFinset.card (Nat.cast_nonneg n)
    (by simpa using hsurplus.le)
  simp only [Fintype.card_fin] at hbound
  have heps := mul_le_mul_of_nonneg_right hηε (sq_nonneg (n : ℝ))
  linarith

/-- The universal lower bound and an actual upper witness for every sufficiently
large order in the longer-cycle cases, as published by Bucić–Chen–Ma. -/
theorem erdos_809_long_odd_cycles_bounds (k : ℕ) (hk : 4 ≤ k) :
    CycleAsymptoticTheorem (2 * k + 1) :=
  cycleAsymptoticTheorem_iff.mpr
    ⟨longOddCycle_asymptoticLowerBound k hk, cycle_asymptoticUpperBound (by omega)⟩

/-- The full attained-minimum epsilon theorem for every fixed odd cycle of
length at least nine. The lower proof formalizes BCM; the construction is reused. -/
theorem erdos_809_long_odd_cycles (k : ℕ) (hk : 4 ≤ k) :
    CycleAsymptoticExtremalValue (2 * k + 1) :=
  cycleAsymptoticExtremalValue_of_lower (by omega) (longOddCycle_asymptoticLowerBound k hk)

end Erdos809
