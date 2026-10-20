import QubitOracle.Paper.OneQubitMixedTruthFrameInformationMatrix
import QubitOracle.Paper.OneQubitCramerWoldBridge
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Varying-row vector score for the concrete polynomial mixed-qubit protocol

Every finite row is packaged as its exact Born probability measure. The
common-space scalar CLT is transported to this varying-row law through the
kernel-proved coordinate map. The vector score itself is direction-independent,
and every scalar projection is exactly the corresponding directional score.
-/

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal RealInnerProductSpace

namespace QubitOracle.Paper

noncomputable section

attribute [local instance]
  mixedPolynomialTotalScaleRowMeasurableSpace
  mixedPolynomialTotalScaleRowMeasurableSingletonClass
  MixedExactCycleScalarTriangularArrayData.rowMeasurableSpace
  MixedExactCycleScalarTriangularArrayData.rowMeasurableSingletonClass

/-- Exact finite two-stage Born row as a probability measure. -/
noncomputable def mixedPolynomialTotalScaleRowProbabilityMeasure
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) :
    ProbabilityMeasure (MixedPolynomialTotalScaleRow n) := by
  letI : IsProbabilityMeasure
      (mixedPolynomialTotalScaleRowMeasure theta b n) := by
    refine ⟨?_⟩
    unfold mixedPolynomialTotalScaleRowMeasure
    exact mixedTwoStageFiniteBornMeasure_univ theta
      (mixedPolynomialTotalScaleSelectedFrame b n)
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
  exact ⟨mixedPolynomialTotalScaleRowMeasure theta b n, inferInstance⟩

/-- Three-coordinate total-scale final score, evaluated on the standard Bloch
basis. -/
def mixedPolynomialRowVectorScore
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : Fin 3 → ℝ :=
  fun i =>
    mixedPolynomialTotalScaleFinalLinearScore theta (standardBasis3 i) b n row

/-- Finite linear algebra: every projection of the vector score is the
corresponding directional score. -/
theorem mixedPolynomialRowVectorScore_projection
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) :
    dotProduct h (mixedPolynomialRowVectorScore theta b n row) =
      mixedPolynomialTotalScaleFinalLinearScore theta h b n row := by
  unfold mixedPolynomialRowVectorScore
    mixedPolynomialTotalScaleFinalLinearScore
    mixedExactCycleLinearScoreTerm
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
    mixedPolynomialTotalScaleDirection
    dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [standardBasis3, blochDot, Fin.sum_univ_succ]
  ring

/-- Law of one directional total-scale row score. -/
noncomputable def mixedPolynomialRowDirectionalScoreLaw
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) : ProbabilityMeasure ℝ :=
  (mixedPolynomialTotalScaleRowProbabilityMeasure
      b theta hTruth hSeed n).map
    ((measurable_of_finite
      (mixedPolynomialTotalScaleFinalLinearScore theta h b n)).aemeasurable)

/-- The lifted common-space score law is exactly the finite-row score law. -/
theorem mixedPolynomialCommonScoreLaw_eq_rowDirectionalScoreLaw
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (hMeasurable : AEMeasurable
      (mixedPolynomialCommonTotalScaleFinalScore
        b theta h hTruth hSeed n)
      (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)) :
    (⟨(mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed).map
        (mixedPolynomialCommonTotalScaleFinalScore
          b theta h hTruth hSeed n), by
        letI : IsProbabilityMeasure
            (mixedPolynomialScalarLANCommonMeasure
              b theta h hTruth hSeed) := by
          unfold mixedPolynomialScalarLANCommonMeasure
          infer_instance
        exact Measure.isProbabilityMeasure_map hMeasurable⟩ :
      ProbabilityMeasure ℝ) =
      mixedPolynomialRowDirectionalScoreLaw
        b theta h hTruth hSeed n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed).map
        (mixedPolynomialCommonTotalScaleFinalScore
          b theta h hTruth hSeed n) =
      (mixedPolynomialTotalScaleRowMeasure theta b n).map
        (mixedPolynomialTotalScaleFinalLinearScore theta h b n)
  have hfun :
      mixedPolynomialCommonTotalScaleFinalScore
          b theta h hTruth hSeed n =
        fun omega =>
          mixedPolynomialTotalScaleFinalLinearScore theta h b n (omega n) := by
    funext omega
    rw [mixedPolynomialCommonTotalScaleFinalScore_eq_rowScore]
  rw [hfun]
  exact mixedPolynomialScalarLANCommonMeasure_map_rowVariable
    b theta h hTruth hSeed n
    (mixedPolynomialTotalScaleFinalLinearScore theta h b n)
    (measurable_of_finite _)

/-- Varying-row scalar score CLT for every physical direction. -/
theorem mixedPolynomialRowDirectionalScoreLaw_tendsto_gaussian
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    Tendsto
      (mixedPolynomialRowDirectionalScoreLaw
        b theta h hTruth hSeed)
      atTop
      (nhds
        (⟨gaussianReal 0
          (mixedPolynomialTruthFrameDirectionalInformation
            theta h b).toNNReal, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hscalar := mixedPolynomialCommonTotalScaleFinalScore_CLT
    b theta h hTruth hSeed hHoeffding
  letI : IsProbabilityMeasure
      (mixedPolynomialScalarLANCommonMeasure
        b theta h hTruth hSeed) := by
    unfold mixedPolynomialScalarLANCommonMeasure
    infer_instance
  have hsource :
      (fun n =>
        (⟨(mixedPolynomialScalarLANCommonMeasure
              b theta h hTruth hSeed).map
            (mixedPolynomialCommonTotalScaleFinalScore
              b theta h hTruth hSeed n),
          Measure.isProbabilityMeasure_map
            (hscalar.forall_aemeasurable n)⟩ : ProbabilityMeasure ℝ)) =
        mixedPolynomialRowDirectionalScoreLaw
          b theta h hTruth hSeed := by
    funext n
    exact mixedPolynomialCommonScoreLaw_eq_rowDirectionalScoreLaw
      b theta h hTruth hSeed n (hscalar.forall_aemeasurable n)
  have htarget :
      (⟨(gaussianReal 0
          (mixedPolynomialTruthFrameDirectionalInformation
            theta h b).toNNReal).map id,
        Measure.isProbabilityMeasure_map
          hscalar.aemeasurable_limit⟩ : ProbabilityMeasure ℝ) =
        ⟨gaussianReal 0
          (mixedPolynomialTruthFrameDirectionalInformation
            theta h b).toNNReal, inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp
  rw [← hsource, ← htarget]
  exact hscalar.tendsto

/-- Law of the full three-coordinate row score. -/
noncomputable def mixedPolynomialRowVectorScoreLaw
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  (mixedPolynomialTotalScaleRowProbabilityMeasure
      b theta hTruth hSeed n).map
    ((measurable_of_finite (fun row =>
      WithLp.toLp 2
        (mixedPolynomialRowVectorScore theta b n row))).aemeasurable)

/-- Projecting the direction-independent vector score law in direction `t`
gives exactly the already-verified scalar directional score law. -/
theorem mixedPolynomialRowVectorScoreLaw_projected
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) (t : EuclideanSpace ℝ (Fin 3)) :
    OneQubitCramerWoldBridge.projectedLaw
        (mixedPolynomialRowVectorScoreLaw
          b theta hTruth hSeed n) t =
      mixedPolynomialRowDirectionalScoreLaw
        b theta (fun i => t i) hTruth hSeed n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    ((mixedPolynomialTotalScaleRowMeasure theta b n).map
        (fun row =>
          WithLp.toLp 2 (mixedPolynomialRowVectorScore theta b n row))).map
        (fun x => ⟪t, x⟫) =
      (mixedPolynomialTotalScaleRowMeasure theta b n).map
        (mixedPolynomialTotalScaleFinalLinearScore
          theta (fun i => t i) b n)
  rw [Measure.map_map (by fun_prop) (measurable_of_finite _)]
  apply Measure.map_congr
  filter_upwards with row
  simpa [Function.comp_def, PiLp.inner_apply, dotProduct, mul_comm] using
    (mixedPolynomialRowVectorScore_projection
      theta (fun i => t i) b n row)

/-- The centered three-dimensional Gaussian law with the concrete truth-frame
Fisher information matrix as covariance. -/
noncomputable def mixedPolynomialTruthFrameGaussianLaw
    (theta b : Fin 3 → ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)) :=
  ⟨multivariateGaussian 0
      (mixedPolynomialTruthFrameInformationMatrix theta b), inferInstance⟩

/-- Every projection of the concrete target Gaussian has the scalar variance
already appearing in the directional score CLT. -/
theorem mixedPolynomialTruthFrameGaussianLaw_projected
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (t : EuclideanSpace ℝ (Fin 3)) :
    OneQubitCramerWoldBridge.projectedLaw
        (mixedPolynomialTruthFrameGaussianLaw theta b) t =
      (⟨gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation
          theta (fun i => t i) b).toNNReal,
        inferInstance⟩ : ProbabilityMeasure ℝ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    (multivariateGaussian 0
      (mixedPolynomialTruthFrameInformationMatrix theta b)).map
        (innerSL ℝ t) =
      gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation
          theta (fun i => t i) b).toNNReal
  rw [IsGaussian.map_eq_gaussianReal]
  congr 2
  · rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp
    · exact IsGaussian.integrable_id
  · change
      Var[(fun x => ⟪t, x⟫);
        multivariateGaussian 0
          (mixedPolynomialTruthFrameInformationMatrix theta b)] =
        mixedPolynomialTruthFrameDirectionalInformation
          theta (fun i => t i) b
    rw [← covarianceBilin_self IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian
        (mixedPolynomialTruthFrameInformationMatrix_posDef
          theta b hTruth hSeed).posSemidef]
    simpa [dotProduct] using
      (mixedPolynomialTruthFrameInformationMatrix_quadratic
        theta (fun i => t i) b)

/-- True three-dimensional weak convergence of the concrete varying-row score
law, obtained from the scalar Hall--Heyde limits by the kernel-proved
Cramer--Wold bridge. -/
theorem mixedPolynomialRowVectorScoreLaw_tendsto_gaussian
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    Tendsto
      (mixedPolynomialRowVectorScoreLaw b theta hTruth hSeed)
      atTop
      (nhds (mixedPolynomialTruthFrameGaussianLaw theta b)) := by
  apply OneQubitCramerWoldBridge.mixedThreeDimensionalScore_tendsto
  intro t
  have hsource :
      (fun n => OneQubitCramerWoldBridge.projectedLaw
        (mixedPolynomialRowVectorScoreLaw
          b theta hTruth hSeed n) t) =
        mixedPolynomialRowDirectionalScoreLaw
          b theta (fun i => t i) hTruth hSeed := by
    funext n
    exact mixedPolynomialRowVectorScoreLaw_projected
      b theta hTruth hSeed n t
  rw [hsource,
    mixedPolynomialTruthFrameGaussianLaw_projected
      theta b hTruth hSeed t]
  exact mixedPolynomialRowDirectionalScoreLaw_tendsto_gaussian
    b theta (fun i => t i) hTruth hSeed hHoeffding

/- Standard Mathlib random-variable formulation of the concrete vector score
CLT.  The varying sample space in row `n` is the exact finite two-stage Born
row, and the limit variable is the identity under the centered Gaussian with
the explicitly computed truth-frame Fisher covariance. -/
theorem mixedPolynomialRowVectorScore_tendstoInDistribution
    (b theta : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    TendstoInDistribution
      (fun n row => WithLp.toLp 2
        (mixedPolynomialRowVectorScore theta b n row))
      atTop id
      (fun n => (mixedPolynomialTotalScaleRowProbabilityMeasure
        b theta hTruth hSeed n :
          Measure (MixedPolynomialTotalScaleRow n)))
      (multivariateGaussian 0
        (mixedPolynomialTruthFrameInformationMatrix theta b)) := by
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
              (mixedPolynomialRowVectorScore theta b n row)),
          Measure.isProbabilityMeasure_map
            ((measurable_of_finite _).aemeasurable)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))) =
        mixedPolynomialRowVectorScoreLaw b theta hTruth hSeed := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  have htarget :
      (⟨(multivariateGaussian 0
          (mixedPolynomialTruthFrameInformationMatrix theta b)).map id,
        Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 3))) =
      mixedPolynomialTruthFrameGaussianLaw theta b := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [mixedPolynomialTruthFrameGaussianLaw]
  rw [hsource, htarget]
  exact mixedPolynomialRowVectorScoreLaw_tendsto_gaussian
    b theta hTruth hSeed hHoeffding

end

end QubitOracle.Paper
