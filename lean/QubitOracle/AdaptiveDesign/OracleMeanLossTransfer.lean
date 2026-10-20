import QubitOracle.Paper.MomentRiskTransfer

/-!
# Conditional mean-loss transfer

This file formalizes the cap-removal step in the new oracle-risk theorem.
The inputs are a capped-loss limit and a uniform second moment of the
normalized nonnegative loss. The latter corresponds to a fourth moment
of the normalized state error when the loss is quadratic. Neither input
is claimed here for the three adaptive protocols.
-/

namespace QubitOracle.AdaptiveDesign.OracleMeanLoss

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- Expected nonnegative loss after a deterministic cap. -/
def cappedExpectedLoss {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (loss : ℕ → Ω → ENNReal) (cap : ENNReal) (n : ℕ) :
    ENNReal :=
  ∫⁻ ω, min (loss n ω) cap ∂μ n

/-- A uniform second moment of the normalized loss. -/
def HasUniformSecondLossMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (loss : ℕ → Ω → ENNReal) (M : ENNReal) : Prop :=
  ∀ n, (∫⁻ ω, (loss n ω)^2 ∂μ n) ≤ M

/-- The truncation remainder is bounded by the second moment divided
by the cap, for every sample size. -/
theorem expectedLoss_le_capped_add_secondMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (loss : ℕ → Ω → ENNReal)
    (hMeas : ∀ n, Measurable (loss n))
    (M cap : ENNReal) (hMoment : HasUniformSecondLossMoment μ loss M)
    (hcap0 : cap ≠ 0) (hcapTop : cap ≠ ∞) (n : ℕ) :
    QubitOracle.Paper.expectedENNRealLoss (μ n) (loss n) ≤
      cappedExpectedLoss μ loss cap n + M * cap⁻¹ := by
  have hMin : Measurable (fun ω => min (loss n ω) cap) :=
    (hMeas n).min measurable_const
  have hSq : Measurable (fun ω => (loss n ω)^2) := (hMeas n).pow_const 2
  calc
    QubitOracle.Paper.expectedENNRealLoss (μ n) (loss n) =
        ∫⁻ ω, loss n ω ∂μ n := rfl
    _ ≤ ∫⁻ ω, min (loss n ω) cap +
          (loss n ω)^2 * cap⁻¹ ∂μ n := by
        exact lintegral_mono fun ω =>
          QubitOracle.Paper.ennreal_le_min_add_sq_mul_inv
            (loss n ω) cap hcap0 hcapTop
    _ = cappedExpectedLoss μ loss cap n +
          (∫⁻ ω, (loss n ω)^2 ∂μ n) * cap⁻¹ := by
        rw [lintegral_add_left hMin, lintegral_mul_const cap⁻¹ hSq]
        rfl
    _ ≤ cappedExpectedLoss μ loss cap n + M * cap⁻¹ := by
        gcongr
        exact hMoment n

/-- A diagonal capped-loss limit and a finite uniform second moment
give convergence of the full expected loss. The capped limit is an
explicit input; this theorem does not manufacture it from a CLT. -/
theorem expectedLoss_tendsto_of_capped_and_secondMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (loss : ℕ → Ω → ENNReal)
    (hMeas : ∀ n, Measurable (loss n))
    (M benchmark : ENNReal) (hMtop : M ≠ ∞)
    (hMoment : HasUniformSecondLossMoment μ loss M)
    (hCapped : Tendsto
      (fun n : ℕ => cappedExpectedLoss μ loss ((n+1 : ℕ) : ENNReal) n)
      atTop (nhds benchmark)) :
    Tendsto (fun n => QubitOracle.Paper.expectedENNRealLoss (μ n) (loss n))
      atTop (nhds benchmark) := by
  have hTail : Tendsto (fun n : ℕ => M * ((n+1 : ℕ) : ENNReal)⁻¹)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuousAt_const_mul
        (a := M) (b := 0) (Or.inl hMtop)).tendsto.comp
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
  have hUpper : Tendsto
      (fun n : ℕ => cappedExpectedLoss μ loss ((n+1 : ℕ) : ENNReal) n +
        M * ((n+1 : ℕ) : ENNReal)⁻¹) atTop (nhds benchmark) := by
    simpa using hCapped.add hTail
  refine Tendsto.squeeze hCapped hUpper ?_ ?_
  · intro n
    exact lintegral_mono fun ω => min_le_left _ _
  · intro n
    exact expectedLoss_le_capped_add_secondMoment
      μ loss hMeas M ((n+1 : ℕ) : ENNReal) hMoment
      (by exact_mod_cast (Nat.succ_ne_zero n))
      (ENNReal.natCast_ne_top (n+1)) n

end
end QubitOracle.AdaptiveDesign.OracleMeanLoss
