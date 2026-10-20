import QubitOracle.Paper.OneQubitMixedPolynomialVectorScoreCLT
import QubitOracle.Paper.OneQubitMixedTruthFrameWhitening
import QubitOracle.Paper.FrozenMixedQubitLANConstructor

/-!
# Frozen-coordinate vector score CLT for the mixed one-qubit protocol

The score is transported through the explicit truth-frame whitening map.
Every projection is reduced to the already verified physical directional
score, so the only scientific dependency of the final CLT is the cited
Hall--Heyde martingale-array theorem.
-/

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace QubitOracle.Paper

noncomputable section

attribute [local instance]
  mixedPolynomialTotalScaleRowMeasurableSpace
  mixedPolynomialTotalScaleRowMeasurableSingletonClass

/-- Concrete row score in Bures-whitened truth-frame coordinates. -/
def mixedPolynomialRowWhitenedVectorScore
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : Fin 3 → ℝ :=
  fun i =>
    dotProduct
      (mixedPolynomialTruthFrameWhiteningDirection
        theta b (standardBasis3 i))
      (mixedPolynomialRowVectorScore theta b n row)

/-- Every frozen-coordinate projection is exactly the physical directional
score along the corresponding whitened Bloch direction. -/
theorem mixedPolynomialRowWhitenedVectorScore_projection
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) (h : Fin 3 → ℝ) :
    dotProduct h
        (mixedPolynomialRowWhitenedVectorScore theta b n row) =
      mixedPolynomialTotalScaleFinalLinearScore theta
        (mixedPolynomialTruthFrameWhiteningDirection theta b h)
        b n row := by
  rw [← mixedPolynomialRowVectorScore_projection theta
    (mixedPolynomialTruthFrameWhiteningDirection theta b h) b n row]
  unfold mixedPolynomialRowWhitenedVectorScore
    mixedPolynomialTruthFrameWhiteningDirection
    dotProduct standardBasis3
  simp [Fin.sum_univ_succ]
  ring

/-- Law of the complete frozen-coordinate row score. -/
noncomputable def mixedPolynomialRowWhitenedVectorScoreLaw
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  (mixedPolynomialTotalScaleRowProbabilityMeasure
      b theta hTruth hSeed n).map
    ((measurable_of_finite (fun row =>
      WithLp.toLp 2
        (mixedPolynomialRowWhitenedVectorScore theta b n row))).aemeasurable)

/-- Projection of the frozen-coordinate score law is the concrete physical
directional score law in the whitened direction. -/
theorem mixedPolynomialRowWhitenedVectorScoreLaw_projected
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    OneQubitCramerWoldBridge.projectedLaw
        (mixedPolynomialRowWhitenedVectorScoreLaw
          b theta hTruth hSeed n) t =
      mixedPolynomialRowDirectionalScoreLaw b theta
        (mixedPolynomialTruthFrameWhiteningDirection
          theta b (fun i => t i))
        hTruth hSeed n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    ((mixedPolynomialTotalScaleRowMeasure theta b n).map
        (fun row => WithLp.toLp 2
          (mixedPolynomialRowWhitenedVectorScore theta b n row))).map
        (fun x => ⟪t, x⟫) =
      (mixedPolynomialTotalScaleRowMeasure theta b n).map
        (mixedPolynomialTotalScaleFinalLinearScore theta
          (mixedPolynomialTruthFrameWhiteningDirection
            theta b (fun i => t i)) b n)
  rw [Measure.map_map (by fun_prop) (measurable_of_finite _)]
  apply Measure.map_congr
  filter_upwards with row
  simpa [Function.comp_def, PiLp.inner_apply, dotProduct, mul_comm] using
    (mixedPolynomialRowWhitenedVectorScore_projection
      theta b n row (fun i => t i))

/-- Frozen Gaussian law with covariance `(1/3) I_3`. -/
noncomputable def mixedFrozenOracleGaussianLaw :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  ⟨multivariateGaussian 0 mixedFrozenOracleInformation, inferInstance⟩

/-- Quadratic form of the frozen information matrix. -/
theorem mixedFrozenOracleInformation_quadratic
    (h : Fin 3 → ℝ) :
    dotProduct h (mixedFrozenOracleInformation.mulVec h) =
      (1 / 3 : ℝ) * blochNormSq h := by
  rw [mixedFrozenOracleInformation_eq_smul_one]
  simp [Matrix.mulVec, dotProduct, blochNormSq, Fin.sum_univ_succ]
  ring

/-- Every projection of the frozen Gaussian has variance
`(1/3) * ||t||^2`. -/
theorem mixedFrozenOracleGaussianLaw_projected
    (t : EuclideanSpace ℝ (Fin 3)) :
    OneQubitCramerWoldBridge.projectedLaw
        mixedFrozenOracleGaussianLaw t =
      (⟨gaussianReal 0
        ((1 / 3 : ℝ) * blochNormSq (fun i => t i)).toNNReal,
        inferInstance⟩ : ProbabilityMeasure ℝ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    (multivariateGaussian 0 mixedFrozenOracleInformation).map
        (innerSL ℝ t) =
      gaussianReal 0
        ((1 / 3 : ℝ) * blochNormSq (fun i => t i)).toNNReal
  rw [IsGaussian.map_eq_gaussianReal]
  congr 2
  · rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp
    · exact IsGaussian.integrable_id
  · change
      Var[(fun x => ⟪t, x⟫);
        multivariateGaussian 0 mixedFrozenOracleInformation] =
        (1 / 3 : ℝ) * blochNormSq (fun i => t i)
    rw [← covarianceBilin_self IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian
        mixedFrozenOracleInformation_posDef.posSemidef]
    simpa [dotProduct] using
      (mixedFrozenOracleInformation_quadratic (fun i => t i))

/-- Weak convergence of the exact frozen-coordinate score law. -/
theorem mixedPolynomialRowWhitenedVectorScoreLaw_tendsto_gaussian
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    Tendsto
      (mixedPolynomialRowWhitenedVectorScoreLaw
        b theta hTruth hSeed)
      atTop (nhds mixedFrozenOracleGaussianLaw) := by
  apply OneQubitCramerWoldBridge.mixedThreeDimensionalScore_tendsto
  intro t
  have hsource :
      (fun n => OneQubitCramerWoldBridge.projectedLaw
        (mixedPolynomialRowWhitenedVectorScoreLaw
          b theta hTruth hSeed n) t) =
        mixedPolynomialRowDirectionalScoreLaw b theta
          (mixedPolynomialTruthFrameWhiteningDirection
            theta b (fun i => t i))
          hTruth hSeed := by
    funext n
    exact mixedPolynomialRowWhitenedVectorScoreLaw_projected
      b theta hTruth hSeed n t
  rw [hsource, mixedFrozenOracleGaussianLaw_projected t]
  have hscalar :=
    mixedPolynomialRowDirectionalScoreLaw_tendsto_gaussian
      b theta
        (mixedPolynomialTruthFrameWhiteningDirection
          theta b (fun i => t i))
      hTruth hSeed hHoeffding
  simpa [mixedPolynomialTruthFrameDirectionalInformation_whitened
    theta b (fun i => t i) hTruth hSeed] using hscalar

/-- Standard Mathlib convergence-in-distribution formulation for the exact
frozen-coordinate score random variables. -/
theorem mixedPolynomialRowWhitenedVectorScore_tendstoInDistribution
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    TendstoInDistribution
      (fun n row => WithLp.toLp 2
        (mixedPolynomialRowWhitenedVectorScore theta b n row))
      atTop id
      (fun n => (mixedPolynomialTotalScaleRowProbabilityMeasure
        b theta hTruth hSeed n :
          Measure (MixedPolynomialTotalScaleRow n)))
      (multivariateGaussian 0 mixedFrozenOracleInformation) := by
  refine
    { forall_aemeasurable := fun n => (measurable_of_finite _).aemeasurable
      aemeasurable_limit := measurable_id.aemeasurable
      tendsto := ?_ }
  have hsource :
      (fun n =>
        (⟨((mixedPolynomialTotalScaleRowProbabilityMeasure
              b theta hTruth hSeed n :
                Measure (MixedPolynomialTotalScaleRow n))).map
            (fun row => WithLp.toLp 2
              (mixedPolynomialRowWhitenedVectorScore theta b n row)),
          Measure.isProbabilityMeasure_map
            ((measurable_of_finite _).aemeasurable)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))) =
        mixedPolynomialRowWhitenedVectorScoreLaw
          b theta hTruth hSeed := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  have htarget :
      (⟨(multivariateGaussian 0 mixedFrozenOracleInformation).map id,
        Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) =
      mixedFrozenOracleGaussianLaw := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [mixedFrozenOracleGaussianLaw]
  rw [hsource, htarget]
  exact mixedPolynomialRowWhitenedVectorScoreLaw_tendsto_gaussian
    b theta hTruth hSeed hHoeffding

end

end QubitOracle.Paper
