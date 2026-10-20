import QubitOracle.Paper.SourceFaithfulMatrixFreedman
import QubitOracle.Paper.SourceFaithfulSelfNormalized
import QubitOracle.Paper.SourceFaithfulDavisKahan

/-!
# Conditional concentration interfaces for supplement labels

These theorems expose source-faithful endpoints corresponding to
`eq:SI_self_normalized`, `eq:SI_Davis_Kahan`, `eq:SI_score_Freedman`, and
`eq:SI_Hessian_Freedman`.  They do not assert that a concrete quantum protocol
satisfies the martingale, sub-Gaussian, bounded-increment, variance, or
population-gap assumptions.
-/

namespace QubitOracle.Paper.ConcentrationLabelInterfaces

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Conditional interface corresponding to `eq:SI_self_normalized`. -/
theorem eq_SI_self_normalized
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {R : ℝ}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData Ω d μ R)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.PosDef) (hR : 0 ≤ R)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ENNReal.ofReal (1 - delta) ≤ μ
      (SourceFaithfulSelfNormalized.selfNormalizedGoodEvent data V delta) :=
  SourceFaithfulSelfNormalized.abbasiYadkoriPalSzepesvari2011_theorem16
    data V hV hR delta hdelta0 hdelta1

/-- Conditional interface corresponding to `eq:SI_Davis_Kahan`, including
both the sine-subspace and aligned-basis conclusions in the cited theorem. -/
theorem eq_SI_Davis_Kahan
    {p q : ℕ}
    (data : SourceFaithfulDavisKahan.PopulationEigenspaceBlock p q)
    (hgap : 0 < data.populationGap) :
    SourceFaithfulDavisKahan.sinThetaFrobenius
        data.sampleVectors data.populationVectors ≤
        2 * data.perturbationSize / data.populationGap ∧
      ∃ O : Matrix (Fin q) (Fin q) ℝ,
        SourceFaithfulDavisKahan.IsOrthogonalMatrix O ∧
          SourceFaithfulDavisKahan.alignedBasisDistance
              data.sampleVectors data.populationVectors O ≤
            (2 * Real.sqrt 2) * data.perturbationSize / data.populationGap :=
  SourceFaithfulDavisKahan.yuWangSamworth2015_theorem2 data hgap

/-- Conditional matrix-Freedman interface corresponding to
`eq:SI_score_Freedman`.  A protocol must separately identify its score (or a
self-adjoint dilation of it) with `data.process`. -/
theorem eq_SI_score_Freedman
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (data : SourceFaithfulMatrixFreedman.MatrixMartingaleData Ω d μ)
    (R t varianceThreshold : ℝ)
    (hd : 0 < d) (hR : 0 < R) (ht : 0 ≤ t)
    (hvariance : 0 < varianceThreshold)
    (hincrement : ∀ k,
      ∀ᵐ ω ∂μ,
        SourceFaithfulMatrixFreedman.largestEigenvalue
          (SourceFaithfulMatrixFreedman.matrixIncrement data.process k ω) ≤ R) :
    μ (SourceFaithfulMatrixFreedman.matrixFreedmanCrossingEvent
        data t varianceThreshold) ≤
      ENNReal.ofReal
        (SourceFaithfulMatrixFreedman.matrixFreedmanBound
          d R t varianceThreshold) :=
  SourceFaithfulMatrixFreedman.tropp2011_matrixFreedman_theorem1_2
    data R t varianceThreshold hd hR ht hvariance hincrement

/-- Conditional matrix-Freedman interface corresponding to
`eq:SI_Hessian_Freedman`.  A protocol must separately identify its centered
Hessian process and verify the displayed source hypotheses. -/
theorem eq_SI_Hessian_Freedman
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (data : SourceFaithfulMatrixFreedman.MatrixMartingaleData Ω d μ)
    (R t varianceThreshold : ℝ)
    (hd : 0 < d) (hR : 0 < R) (ht : 0 ≤ t)
    (hvariance : 0 < varianceThreshold)
    (hincrement : ∀ k,
      ∀ᵐ ω ∂μ,
        SourceFaithfulMatrixFreedman.largestEigenvalue
          (SourceFaithfulMatrixFreedman.matrixIncrement data.process k ω) ≤ R) :
    μ (SourceFaithfulMatrixFreedman.matrixFreedmanCrossingEvent
        data t varianceThreshold) ≤
      ENNReal.ofReal
        (SourceFaithfulMatrixFreedman.matrixFreedmanBound
          d R t varianceThreshold) :=
  SourceFaithfulMatrixFreedman.tropp2011_matrixFreedman_theorem1_2
    data R t varianceThreshold hd hR ht hvariance hincrement

end

end QubitOracle.Paper.ConcentrationLabelInterfaces
