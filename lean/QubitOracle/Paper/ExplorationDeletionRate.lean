import QubitOracle.Paper.ExplorationFractionPath
import QubitOracle.Paper.RetainedMixedInformation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory

/-- The paper's one-based exploration flag read from a zero-based path.  The
value at index zero is immaterial because terminal sums start at one. -/
def pathExplorationFlag
    (omega : ℕ → Bool × Unit) (i : ℕ) : ℕ :=
  if (omega (i - 1)).1 then 1 else 0

/-- Number of realized exploration shots among the first `n` observations. -/
def pathExplorationCount
    (omega : ℕ → Bool × Unit) (n : ℕ) : ℕ :=
  ∑ i ∈ terminalObservedSet n, pathExplorationFlag omega i

/-- The predictable exploration schedule average `E_n / n`. -/
def explorationScheduleAverage
    (epsilon : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ k ∈ Finset.range n, epsilon (k + 1)

/-- The realized exploration frequency among the first `n` observations. -/
def pathExplorationAverage
    (omega : ℕ → Bool × Unit) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (pathExplorationCount omega n : ℝ)

/-- The normalized deterministic burn-in length `q_n / n`. -/
def terminalBurnInAverage (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (terminalBurnInCutoff n : ℝ)

/-- Exact reindexing from the paper's one-based observations to the path's
zero-based coordinates. -/
theorem pathExplorationCount_eq_sum_range
    (omega : ℕ → Bool × Unit) (n : ℕ) :
    pathExplorationCount omega n =
      ∑ k ∈ Finset.range n,
        if (omega k).1 then 1 else 0 := by
  unfold pathExplorationCount terminalObservedSet
  refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj hij
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    refine ⟨k + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro i hi
    rfl

/-- Casting the terminal count to the reals gives the sum of the real-valued
indicators used in the martingale strong law. -/
theorem pathExplorationCount_cast_eq_indicator_sum
    (omega : ℕ → Bool × Unit) (n : ℕ) :
    (pathExplorationCount omega n : ℝ) =
      ∑ k ∈ Finset.range n,
        explorationIndicator (omega k).1 := by
  rw [pathExplorationCount_eq_sum_range, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  cases hflag : (omega k).1 <;>
    simp [explorationIndicator, hflag]

/-- The realized frequency is the centered martingale average plus the
predictable schedule average. -/
theorem pathExplorationAverage_eq_centered_add_schedule
    (epsilon : ℕ → ℝ) (omega : ℕ → Bool × Unit) (n : ℕ) :
    pathExplorationAverage omega n =
      (n : ℝ)⁻¹ *
          ∑ k ∈ Finset.range n,
            explorationAllShotInnovation epsilon omega k +
        explorationScheduleAverage epsilon n := by
  unfold pathExplorationAverage explorationScheduleAverage
  rw [pathExplorationCount_cast_eq_indicator_sum]
  simp only [explorationAllShotInnovation]
  rw [Finset.sum_sub_distrib]
  ring

/-- A centered strong law and `E_n / n → 0` imply that the realized
exploration frequency vanishes. -/
theorem pathExplorationAverage_tendsto_zero
    (epsilon : ℕ → ℝ) (omega : ℕ → Bool × Unit)
    (hcenter : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ *
          ∑ k ∈ Finset.range n,
            explorationAllShotInnovation epsilon omega k)
      atTop (nhds 0))
    (hschedule : Tendsto
      (explorationScheduleAverage epsilon) atTop (nhds 0)) :
    Tendsto (pathExplorationAverage omega) atTop (nhds 0) := by
  have hsum := hcenter.add hschedule
  have heq : pathExplorationAverage omega =
      fun n : ℕ =>
        (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n,
              explorationAllShotInnovation epsilon omega k +
          explorationScheduleAverage epsilon n := by
    funext n
    exact pathExplorationAverage_eq_centered_add_schedule
      epsilon omega n
  rw [heq]
  simpa using hsum

/-- Under the actual latent-flag trajectory law, `E_n / n → 0` implies that
the realized exploration frequency vanishes almost surely. -/
theorem pathExplorationAverage_strongLaw
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (hschedule : Tendsto
      (explorationScheduleAverage epsilon) atTop (nhds 0)) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure
        epsilon hepsilon0 hepsilon1,
      Tendsto (pathExplorationAverage omega) atTop (nhds 0) := by
  filter_upwards
    [Label.eq_SI_exploration_fraction_realized
      epsilon hepsilon0 hepsilon1] with omega hcenter
  exact pathExplorationAverage_tendsto_zero
    epsilon omega hcenter hschedule

/-- The deterministic burn-in `q_n = ceil(n^(1/3))` is sublinear. -/
theorem terminalBurnInAverage_tendsto_zero :
    Tendsto terminalBurnInAverage atTop (nhds 0) := by
  have hpow : Tendsto
      (fun n : ℕ =>
        Real.rpow (n : ℝ) (-(2 / 3 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 2 / 3)).comp
        tendsto_natCast_atTop_atTop
  have hrootOver : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (1 / 3 : ℝ))
      atTop (nhds 0) := by
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hrpowOne : Real.rpow (n : ℝ) (1 : ℝ) = (n : ℝ) := by
      simpa using (Real.rpow_natCast (n : ℝ) 1)
    calc
      Real.rpow (n : ℝ) (-(2 / 3 : ℝ)) =
          Real.rpow (n : ℝ) ((1 / 3 : ℝ) - 1) := by
        norm_num
      _ = Real.rpow (n : ℝ) (1 / 3 : ℝ) /
          Real.rpow (n : ℝ) 1 :=
        Real.rpow_sub hnR (1 / 3 : ℝ) 1
      _ = (n : ℝ)⁻¹ * Real.rpow (n : ℝ) (1 / 3 : ℝ) := by
        rw [hrpowOne, div_eq_mul_inv, mul_comm]
  have hone : Tendsto
      (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ))
  have hupper : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ *
          (Real.rpow (n : ℝ) (1 / 3 : ℝ) + 1))
      atTop (nhds 0) := by
    simpa only [mul_add, mul_one, zero_add] using
      hrootOver.add hone
  apply squeeze_zero'
    (Eventually.of_forall fun n => by
      exact mul_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg n))
        (Nat.cast_nonneg (terminalBurnInCutoff n)))
    (Eventually.of_forall fun n => by
      unfold terminalBurnInAverage terminalBurnInCutoff
      apply mul_le_mul_of_nonneg_left
      · exact (Nat.ceil_lt_add_one
          (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 3 : ℝ))).le
      · exact inv_nonneg.mpr (Nat.cast_nonneg n))
    hupper

/-- Pointwise algebraic form of the mixed deletion bound along a latent-flag
path. -/
theorem mixedTerminalDeletionBound_path_eq
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (omega : ℕ → Bool × Unit) (n : ℕ) (hn : 0 < n) :
    mixedTerminalDeletionBound theta (pathExplorationFlag omega) n =
      (terminalBurnInAverage n + pathExplorationAverage omega n) /
        (1 - QubitOracle.blochNormSq theta) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hden : 1 - QubitOracle.blochNormSq theta ≠ 0 := by
    linarith
  unfold mixedTerminalDeletionBound terminalBurnInAverage
    pathExplorationAverage pathExplorationCount
  rw [Nat.cast_add]
  field_simp [hn0, hden]
  <;> ring

/-- The scalar right-hand side in `eq:SI_delete_mixed` converges to zero
almost surely from the paper's schedule condition `E_n / n → 0`. -/
theorem mixedTerminalDeletionBound_path_strongLaw
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (hschedule : Tendsto
      (explorationScheduleAverage epsilon) atTop (nhds 0)) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure
        epsilon hepsilon0 hepsilon1,
      Tendsto
        (mixedTerminalDeletionBound theta
          (pathExplorationFlag omega))
        atTop (nhds 0) := by
  filter_upwards
    [pathExplorationAverage_strongLaw
      epsilon hepsilon0 hepsilon1 hschedule] with omega hflag
  have hsum := terminalBurnInAverage_tendsto_zero.add hflag
  have hscaled : Tendsto
      (fun n : ℕ =>
        (terminalBurnInAverage n + pathExplorationAverage omega n) /
          (1 - QubitOracle.blochNormSq theta))
      atTop (nhds 0) := by
    simpa using hsum.div_const
      (1 - QubitOracle.blochNormSq theta)
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (mixedTerminalDeletionBound_path_eq
    theta hinterior omega n hn).symm

namespace Label

/-- The convergence assertion at the end of `eq:SI_delete_mixed`. -/
theorem eq_SI_delete_mixed_tendsto_zero
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (hschedule : Tendsto
      (explorationScheduleAverage epsilon) atTop (nhds 0)) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure
        epsilon hepsilon0 hepsilon1,
      Tendsto
        (mixedTerminalDeletionBound theta
          (pathExplorationFlag omega))
        atTop (nhds 0) := by
  exact mixedTerminalDeletionBound_path_strongLaw
    theta hinterior epsilon hepsilon0 hepsilon1 hschedule

/-- Pathwise retained mixed information under the paper's schedule condition.
The only remaining protocol premise is the full-information convergence from
`thm:SI_information`; the deletion-limit premise is discharged here. -/
theorem eq_SI_retained_mixed_of_schedule
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (hschedule : Tendsto
      (explorationScheduleAverage epsilon) atTop (nhds 0))
    (axis : (ℕ → Bool × Unit) → ℕ → Fin 3 → ℝ)
    (haxis : ∀ omega i,
      QubitOracle.blochNormSq (axis omega i) = 1)
    (target : OracleMatrix)
    (hfull : ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure
        epsilon hepsilon0 hepsilon1,
      Tendsto
        (mixedObservedInformationAverage theta (axis omega))
        atTop (nhds target)) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure
        epsilon hepsilon0 hepsilon1,
      Tendsto
        (mixedRetainedInformationAverage theta (axis omega)
          (pathExplorationFlag omega))
        atTop (nhds target) := by
  filter_upwards
    [hfull,
      eq_SI_delete_mixed_tendsto_zero
        theta hinterior epsilon hepsilon0 hepsilon1 hschedule]
      with omega hfullOmega hboundOmega
  exact eq_SI_retained_mixed
    theta hinterior (axis omega) (haxis omega)
    (pathExplorationFlag omega) target hfullOmega hboundOmega

end Label

end QubitOracle.Paper
