import QubitOracle.Paper.AdaptiveMLEEfficiency
import QubitOracle.Paper.EventLIntegralCore
import QubitOracle.TwoBasis

/-!
# Moment bounds, uniform integrability, and expected-risk transfer

This module isolates the measure-theoretic end of the paper's risk argument.
It adds no scientific axiom. Protocol-specific work enters only through
primitive fourth-moment, bad-event probability, and Taylor-remainder bounds.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

/-! ## Fourth moments imply quadratic uniform integrability -/

/-- Fourth moment of a normalized local estimation error. -/
def localQuadraticFourthMoment
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (n : ℕ) (h : LANParameter D) : ENNReal :=
  ∫⁻ x, (ENNReal.ofReal (‖(T n).toFun x - h‖ ^ 2)) ^ 2
    ∂(E n).measure h

/-- Primitive protocol estimate: the normalized local error has a fourth
moment bounded uniformly over the sample size and a fixed finite local set. -/
def HasUniformFiniteLocalFourthMomentBound
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) (C : ENNReal) : Prop :=
  ∀ n (h : ↥I), localQuadraticFourthMoment E T n h.1 ≤ C

/-- Elementary truncation inequality for a positive finite cap. -/
theorem ennreal_le_min_add_sq_mul_inv
    (a cap : ENNReal) (hcap0 : cap ≠ 0) (hcapTop : cap ≠ ∞) :
    a ≤ min a cap + a ^ 2 * cap⁻¹ := by
  by_cases ha : a ≤ cap
  · rw [min_eq_left ha]
    exact le_add_right (le_refl a)
  · have hcap : cap ≤ a := le_of_not_ge ha
    rw [min_eq_right hcap]
    have hsquare : a ≤ a ^ 2 * cap⁻¹ := by
      calc
        a = a * 1 := (mul_one a).symm
        _ = a * (cap * cap⁻¹) := by rw [ENNReal.mul_inv_cancel hcap0 hcapTop]
        _ = (a * cap) * cap⁻¹ := by rw [mul_assoc]
        _ ≤ (a * a) * cap⁻¹ := by gcongr
        _ = a ^ 2 * cap⁻¹ := by rw [pow_two]
    exact hsquare.trans (le_add_left (le_refl _))

/-- A fourth moment controls the loss removed by capping before taking any
worst-case supremum. -/
theorem localQuadraticRisk_le_capped_add_fourthMoment
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (hcap0 : cap ≠ 0) (hcapTop : cap ≠ ∞)
    (n : ℕ) (h : LANParameter D) :
    localQuadraticRisk E T n h ≤
    localCappedQuadraticRisk E T cap n h +
        localQuadraticFourthMoment E T n h * cap⁻¹ := by
  letI : MeasurableSpace (E n).Sample := (E n).measurableSpace
  let q : (E n).Sample → ENNReal :=
    fun x => ENNReal.ofReal (‖(T n).toFun x - h‖ ^ 2)
  have hq : Measurable q := by
    dsimp [q]
    exact (((T n).measurable.sub measurable_const).norm.pow_const 2).ennreal_ofReal
  have hmin : Measurable (fun x => min (q x) cap) :=
    hq.min measurable_const
  have hsq : Measurable (fun x => (q x) ^ 2) := hq.pow_const 2
  calc
    localQuadraticRisk E T n h = ∫⁻ x, q x ∂(E n).measure h := rfl
    _ ≤ ∫⁻ x, min (q x) cap + (q x) ^ 2 * cap⁻¹
        ∂(E n).measure h :=
      lintegral_mono fun x => ennreal_le_min_add_sq_mul_inv
        (q x) cap hcap0 hcapTop
    _ = (∫⁻ x, min (q x) cap ∂(E n).measure h) +
        ∫⁻ x, (q x) ^ 2 * cap⁻¹ ∂(E n).measure h := by
      rw [lintegral_add_left hmin]
    _ = localCappedQuadraticRisk E T cap n h +
        localQuadraticFourthMoment E T n h * cap⁻¹ := by
      rw [lintegral_mul_const cap⁻¹ hsq]
      rfl

/-- Uniform fourth moments give the quantitative finite-local cap-removal
bound C times the inverse cap. -/
theorem finiteLocalQuadraticTailRemainder_le_fourthMoment_mul_inv
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) (C cap : ENNReal)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C)
    (hcap0 : cap ≠ 0) (hcapTop : cap ≠ ∞) (n : ℕ) :
    finiteLocalQuadraticTailRemainder E T cap I n ≤ C * cap⁻¹ := by
  have hFull :
      finiteLocalWorstQuadraticRisk E T I n ≤
        finiteLocalWorstCappedQuadraticRisk E T cap I n + C * cap⁻¹ := by
    refine iSup_le fun h => ?_
    calc
      localQuadraticRisk E T n h.1 ≤
          localCappedQuadraticRisk E T cap n h.1 +
            localQuadraticFourthMoment E T n h.1 * cap⁻¹ :=
        localQuadraticRisk_le_capped_add_fourthMoment
          E T cap hcap0 hcapTop n h.1
      _ ≤ localCappedQuadraticRisk E T cap n h.1 + C * cap⁻¹ := by
        gcongr
        exact hFourth n h
      _ ≤ finiteLocalWorstCappedQuadraticRisk E T cap I n + C * cap⁻¹ := by
        gcongr
        exact le_iSup
          (fun k : ↥I => localCappedQuadraticRisk E T cap n k.1) h
  rw [finiteLocalQuadraticTailRemainder, tsub_le_iff_left]
  simpa [add_comm] using hFull

/-- A uniform fourth-moment estimate proves the exact uniform quadratic-tail
condition consumed by QuadraticRiskAttainability. -/
theorem hasUniformFiniteLocalQuadraticTails_of_fourthMoment
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C) :
    HasUniformFiniteLocalQuadraticTails E T I := by
  let upper : ℕ → ENNReal :=
    fun m => if m = 0 then ∞ else C * (m : ENNReal)⁻¹
  have hUpperTendsto : Tendsto upper atTop (nhds 0) := by
    have hBase :
        Tendsto (fun m : ℕ => C * (m : ENNReal)⁻¹) atTop (nhds 0) := by
      simpa [Function.comp_def] using (ENNReal.continuousAt_const_mul
        (a := C) (b := 0) (Or.inl hCTop)).tendsto.comp
          ENNReal.tendsto_inv_nat_nhds_zero
    apply hBase.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    simp [upper, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)]
  unfold HasUniformFiniteLocalQuadraticTails
  refine Tendsto.squeeze tendsto_const_nhds hUpperTendsto ?_ ?_
  · intro m
    exact bot_le
  · intro m
    by_cases hm : m = 0
    · simp [upper, hm]
    · simp only [upper, hm, if_false]
      refine iSup_le fun n => ?_
      exact finiteLocalQuadraticTailRemainder_le_fourthMoment_mul_inv
        E T I C (m : ENNReal) hFourth
        (by exact_mod_cast hm) (ENNReal.natCast_ne_top m) n

/-! ## Taylor loss transfer under a moment envelope -/

/-- Expected nonnegative loss. -/
def expectedENNRealLoss
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (loss : Omega → ENNReal) : ENNReal :=
  ∫⁻ omega, loss omega ∂mu

/-- A pointwise Taylor remainder dominated by a vanishing deterministic rate
times a uniformly bounded moment envelope has vanishing expected value. -/
theorem expectedTaylorRemainder_tendsto_zero_of_moment_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega)
    (remainder moment : ℕ → Omega → ENNReal)
    (rate : ℕ → ENNReal) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hmomentMeasurable : ∀ n, Measurable (moment n))
    (hEnvelope : ∀ n omega, remainder n omega ≤ rate n * moment n omega)
    (hMoment : ∀ n, ∫⁻ omega, moment n omega ∂mu n ≤ C)
    (hRate : Tendsto rate atTop (nhds 0)) :
    Tendsto (fun n => expectedENNRealLoss (mu n) (remainder n))
      atTop (nhds 0) := by
  have hUpper : Tendsto (fun n => rate n * C) atTop (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.continuousAt_mul_const
      (a := C) (b := 0) (Or.inl hCTop)).tendsto.comp hRate
  refine Tendsto.squeeze tendsto_const_nhds hUpper ?_ ?_
  · intro n
    exact bot_le
  · intro n
    calc
      expectedENNRealLoss (mu n) (remainder n) ≤
          ∫⁻ omega, rate n * moment n omega ∂mu n :=
        lintegral_mono (hEnvelope n)
      _ = rate n * ∫⁻ omega, moment n omega ∂mu n := by
        rw [lintegral_const_mul (rate n) (hmomentMeasurable n)]
      _ ≤ rate n * C := by gcongr; exact hMoment n

/-- Measure-theoretic loss transfer from a quadratic approximation to a
physical loss under a primitive moment envelope. -/
theorem expectedPhysicalLoss_tendsto_of_quadratic_and_moment_remainder
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega)
    (physical quadratic remainder moment : ℕ → Omega → ENNReal)
    (rate : ℕ → ENNReal) (C benchmark : ENNReal)
    (hCTop : C ≠ ∞)
    (hQuadraticMeasurable : ∀ n, Measurable (quadratic n))
    (hMomentMeasurable : ∀ n, Measurable (moment n))
    (hLower : ∀ n omega, quadratic n omega ≤ physical n omega)
    (hUpper : ∀ n omega,
      physical n omega ≤ quadratic n omega + remainder n omega)
    (hRemainderEnvelope : ∀ n omega,
      remainder n omega ≤ rate n * moment n omega)
    (hMoment : ∀ n, ∫⁻ omega, moment n omega ∂mu n ≤ C)
    (hRate : Tendsto rate atTop (nhds 0))
    (hQuadraticRisk : Tendsto
      (fun n => expectedENNRealLoss (mu n) (quadratic n))
      atTop (nhds benchmark)) :
    Tendsto (fun n => expectedENNRealLoss (mu n) (physical n))
      atTop (nhds benchmark) := by
  have hRemainder :=
    expectedTaylorRemainder_tendsto_zero_of_moment_bound
      mu remainder moment rate C hCTop hMomentMeasurable hRemainderEnvelope
      hMoment hRate
  have hUpperTendsto :
      Tendsto
        (fun n => expectedENNRealLoss (mu n) (quadratic n) +
          expectedENNRealLoss (mu n) (remainder n))
        atTop (nhds benchmark) := by
    simpa using hQuadraticRisk.add hRemainder
  refine Tendsto.squeeze hQuadraticRisk hUpperTendsto ?_ ?_
  · intro n
    exact lintegral_mono (hLower n)
  · intro n
    calc
      expectedENNRealLoss (mu n) (physical n) ≤
          ∫⁻ omega, quadratic n omega + remainder n omega ∂mu n :=
        lintegral_mono (hUpper n)
      _ = expectedENNRealLoss (mu n) (quadratic n) +
          expectedENNRealLoss (mu n) (remainder n) := by
        rw [lintegral_add_left (hQuadraticMeasurable n)]
        rfl

/-! ## Paper-label endpoints -/

/--
A uniform fourth-moment bound supplies the uniform quadratic tails required to
remove the cap from finite-local Gaussian risk convergence.
-/
theorem finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_fourthMoment
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D Real) (hJ : J.PosDef)
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (C : ENNReal) (hCTop : C ≠ ⊤)
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n) atTop
      (nhds (ENNReal.ofReal (J⁻¹).trace)) :=
  finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_uniformTails
    J hJ E T I hCapped
    (hasUniformFiniteLocalQuadraticTails_of_fourthMoment
      E T I C hCTop hFourth)

namespace Label

/-- Supplement theorem thm:SI_moments. -/
theorem thm_SI_moments
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C) :
    HasUniformFiniteLocalQuadraticTails E T I :=
  hasUniformFiniteLocalQuadraticTails_of_fourthMoment E T I C hCTop hFourth

/-- Supplement equation eq:SI_bad_event_moment. -/
theorem eq_SI_bad_event_moment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega) (bad : ℕ → Set Omega)
    (loss : ℕ → Omega → ENNReal) (B p : ℕ → ENNReal)
    (hbad : ∀ n, MeasurableSet (bad n))
    (hEnvelope : ∀ n omega, omega ∈ bad n → loss n omega ≤ B n)
    (hProbability : ∀ n, mu n (bad n) ≤ p n)
    (hRate : Tendsto (fun n => B n * p n) atTop (nhds 0)) :
    (∀ n, eventLIntegral (mu n) (bad n) (loss n) ≤ B n * p n) ∧
      Tendsto (fun n => eventLIntegral (mu n) (bad n) (loss n))
        atTop (nhds 0) := by
  constructor
  · intro n
    exact (eventLIntegral_le_envelope_mul_measure
      (mu n) (bad n) (hbad n) (loss n) (B n) (hEnvelope n)).trans
        (by gcongr; exact hProbability n)
  · exact eventLIntegral_tendsto_zero_of_envelope_probability
      mu bad loss B p hbad hEnvelope hProbability hRate

/-- Main theorem thm:risk_attainment. -/
theorem thm_risk_attainment
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (hCapped : ∀ I : Finset (LANParameter D), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : ∀ I : Finset (LANParameter D), I.Nonempty →
      ∃ C : ENNReal, C ≠ ∞ ∧
        HasUniformFiniteLocalFourthMomentBound E T I C) :
    AttainsGaussianLocalAsymptoticMinimaxBound J E T := by
  apply gaussianScore_localAsymptoticMinimax_attained_of_cappedGaussian_of_uniformTails
    J hJ E hExperiment T hCapped
  intro I hI
  obtain ⟨C, hCTop, hC⟩ := hFourth I hI
  exact hasUniformFiniteLocalQuadraticTails_of_fourthMoment
    E T I C hCTop hC

/-- Main equation eq:mixed_risk_limit. -/
theorem eq_mixed_risk_limit
    (J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter (Fin 3)))
    (T : (n : ℕ) → Statistic (E n) (LANParameter (Fin 3)))
    (I : Finset (LANParameter (Fin 3))) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C)
    (hConstant : Matrix.trace J⁻¹ = (9 / 4 : ℝ)) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  have hTail :=
    hasUniformFiniteLocalQuadraticTails_of_fourthMoment
      E T I C hCTop hFourth
  simpa [hConstant] using
    finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_uniformTails
      J hJ E T I hCapped hTail

/-- Supplement equation eq:SI_mixed_risk. -/
theorem eq_SI_mixed_risk
    (J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter (Fin 3)))
    (T : (n : ℕ) → Statistic (E n) (LANParameter (Fin 3)))
    (I : Finset (LANParameter (Fin 3))) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C)
    (hConstant : Matrix.trace J⁻¹ = (9 / 4 : ℝ)) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) :=
  eq_mixed_risk_limit J hJ E T I C hCTop hCapped hFourth hConstant

/-- Main equation eq:r1_risk_limit. -/
theorem eq_r1_risk_limit
    {d : ℕ}
    (J : Matrix (TangentIndex d) (TangentIndex d) ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter (TangentIndex d)))
    (T : (n : ℕ) → Statistic (E n) (LANParameter (TangentIndex d)))
    (I : Finset (LANParameter (TangentIndex d))) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C)
    (hConstant : Matrix.trace J⁻¹ = (d : ℝ)) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds (ENNReal.ofReal (d : ℝ))) := by
  have hTail :=
    hasUniformFiniteLocalQuadraticTails_of_fourthMoment
      E T I C hCTop hFourth
  simpa [hConstant] using
    finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_uniformTails
      J hJ E T I hCapped hTail

/-- Supplement equation eq:SI_r1_risk. -/
theorem eq_SI_r1_risk
    {d : ℕ}
    (J : Matrix (TangentIndex d) (TangentIndex d) ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter (TangentIndex d)))
    (T : (n : ℕ) → Statistic (E n) (LANParameter (TangentIndex d)))
    (I : Finset (LANParameter (TangentIndex d))) (C : ENNReal)
    (hCTop : C ≠ ∞)
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hFourth : HasUniformFiniteLocalFourthMomentBound E T I C)
    (hConstant : Matrix.trace J⁻¹ = (d : ℝ)) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds (ENNReal.ofReal (d : ℝ))) :=
  eq_r1_risk_limit J hJ E T I C hCTop hCapped hFourth hConstant

/-- Supplement equation eq:SI_mixed_loss_transfer. -/
theorem eq_SI_mixed_loss_transfer
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega)
    (physical quadratic remainder moment : ℕ → Omega → ENNReal)
    (rate : ℕ → ENNReal) (C benchmark : ENNReal)
    (hCTop : C ≠ ∞)
    (hQuadraticMeasurable : ∀ n, Measurable (quadratic n))
    (hMomentMeasurable : ∀ n, Measurable (moment n))
    (hLower : ∀ n omega, quadratic n omega ≤ physical n omega)
    (hUpper : ∀ n omega,
      physical n omega ≤ quadratic n omega + remainder n omega)
    (hRemainderEnvelope : ∀ n omega,
      remainder n omega ≤ rate n * moment n omega)
    (hMoment : ∀ n, ∫⁻ omega, moment n omega ∂mu n ≤ C)
    (hRate : Tendsto rate atTop (nhds 0))
    (hQuadraticRisk : Tendsto
      (fun n => expectedENNRealLoss (mu n) (quadratic n))
      atTop (nhds benchmark)) :
    Tendsto (fun n => expectedENNRealLoss (mu n) (physical n))
      atTop (nhds benchmark) :=
  expectedPhysicalLoss_tendsto_of_quadratic_and_moment_remainder
    mu physical quadratic remainder moment rate C benchmark
    hCTop hQuadraticMeasurable hMomentMeasurable hLower hUpper
    hRemainderEnvelope hMoment hRate hQuadraticRisk

/-- Supplement equation eq:SI_r1_loss_transfer. -/
theorem eq_SI_r1_loss_transfer
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℕ → Measure Omega)
    (physical quadratic remainder moment : ℕ → Omega → ENNReal)
    (rate : ℕ → ENNReal) (C benchmark : ENNReal)
    (hCTop : C ≠ ∞)
    (hQuadraticMeasurable : ∀ n, Measurable (quadratic n))
    (hMomentMeasurable : ∀ n, Measurable (moment n))
    (hLower : ∀ n omega, quadratic n omega ≤ physical n omega)
    (hUpper : ∀ n omega,
      physical n omega ≤ quadratic n omega + remainder n omega)
    (hRemainderEnvelope : ∀ n omega,
      remainder n omega ≤ rate n * moment n omega)
    (hMoment : ∀ n, ∫⁻ omega, moment n omega ∂mu n ≤ C)
    (hRate : Tendsto rate atTop (nhds 0))
    (hQuadraticRisk : Tendsto
      (fun n => expectedENNRealLoss (mu n) (quadratic n))
      atTop (nhds benchmark)) :
    Tendsto (fun n => expectedENNRealLoss (mu n) (physical n))
      atTop (nhds benchmark) :=
  expectedPhysicalLoss_tendsto_of_quadratic_and_moment_remainder
    mu physical quadratic remainder moment rate C benchmark
    hCTop hQuadraticMeasurable hMomentMeasurable hLower hUpper
    hRemainderEnvelope hMoment hRate hQuadraticRisk

end Label

end

end QubitOracle.Paper
