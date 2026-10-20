import QubitOracle.AdaptiveDesign.LibraryRidgeLinearization
import QubitOracle.AdaptiveDesign.NearestPureExpansion
import QubitOracle.AdaptiveDesign.PureChartCovariance

/-! Gaussian limits for the literal nearest-pure estimator of the
optional library, without a Fisher correction or an assumed CLT input. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def pureEstimate {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) : HermitianSpace (d+1) :=
  (pureParameter d (nearestVector d (toMatrix (rawEstimator hd batchSize path n)))).val

lemma pureEstimate_matrix {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) :
    toMatrix (pureEstimate hd batchSize n path)=stateEstimator hd batchSize path n := rfl

lemma pureEstimate_measurable {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) (n : ℕ) :
    StronglyMeasurable (pureEstimate hd batchSize n) :=
  statistic_measurable hd batchSize n (fun A => (pureParameter d (nearestVector d (toMatrix A))).val)

lemma pureEstimate_consistent {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (fun n => pureEstimate hd batchSize n path) atTop (𝓝 (pureParameter d truth).val) := by
  filter_upwards [rawEstimator_consistent hd batchSize (pureParameter d truth)] with path hp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hp).const_mul 2
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa using hh)
  intro n
  rw [← toMatrix_norm, ← toMatrix_norm (rawEstimator hd batchSize path n-(pureParameter d truth).val)]
  exact projectedMatrix_error_le_two d truth (toMatrix (rawEstimator hd batchSize path n))

theorem projection_remainder_zero {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val-
          tangentProjector truth (rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val)))
      atTop (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.dominated (raw_square_negligible hd truth batchSize) 20 (by norm_num)
  intro n path
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (nearestProjector_expansion truth (rawEstimator hd batchSize path (n+1)))
    (Real.sqrt_nonneg ((n+1:ℕ):ℝ))
  exact hh.trans_eq (by ring)

theorem pure_linearization {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val)-
          ((gramConstant d*Real.sqrt ((n+1:ℕ):ℝ))⁻¹) •
            tangentProjector truth (noiseSum hd truth batchSize (n+1) path)) atTop (fun _ => 0) := by
  have hh := ProbabilityZeroAlgebra.add (projection_remainder_zero hd truth batchSize)
    (tangent_linearization hd truth batchSize hpositive)
  apply hh.congr _ EventuallyEq.rfl
  intro n
  apply Eventually.of_forall
  intro path
  simp only [smul_sub]
  abel

lemma fullScore_coordinate {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (Outcome d)) :
    fullScore hd truth batchSize n path = (2:ℝ) • trueCoordinate truth
      ((gramConstant d*Real.sqrt (n:ℝ))⁻¹ • tangentProjector truth (noiseSum hd truth batchSize n path)) := by
  simp only [fullScore, noiseSum, scoreResponse, actualVectorResponse, map_smul, map_sum,
    trueCoordinate_projection, ← Finset.smul_sum, smul_smul, mul_inv, div_eq_mul_inv]
  module

theorem coordinates_minus_score_zero {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth
        (pureEstimate hd batchSize n path-(pureParameter d truth).val))-fullScore hd truth batchSize n path)
      atTop (fun _ => 0) := by
  have hh := continuousAt_const (pure_linearization hd truth batchSize hpositive)
    (show ContinuousAt (fun x : HermitianSpace (d+1) => (2:ℝ) • trueCoordinate truth x) 0 by fun_prop)
  have he (n : ℕ) (path : AdaptiveInfinitePath (Outcome d)) :
      (2:ℝ) • trueCoordinate truth
        (Real.sqrt ((n+1:ℕ):ℝ) • (pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val)-
          (gramConstant d*Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • tangentProjector truth
            (noiseSum hd truth batchSize (n+1) path)) =
      Real.sqrt ((n+1:ℕ):ℝ) • ((2:ℝ) • trueCoordinate truth
        (pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val))-
          fullScore hd truth batchSize (n+1) path := by
    rw [fullScore_coordinate]
    simp only [map_sub, map_smul, smul_sub]
    module
  simp only [map_zero, smul_zero] at hh
  have hs := hh.congr (fun n => Eventually.of_forall (he n)) EventuallyEq.rfl
  intro ε hε
  exact (tendsto_add_atTop_iff_nat 1).mp (hs ε hε)

theorem coordinates_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth
        (pureEstimate hd batchSize n path-(pureParameter d truth).val))) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ (fullScore_clt hd truth batchSize hpositive)
    (coordinates_minus_score_zero hd truth batchSize hpositive)
  intro n
  exact (statistic_measurable hd batchSize n (fun A => Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth
    ((pureParameter d (nearestVector d (toMatrix A))).val-(pureParameter d truth).val)))).measurable.aemeasurable

/-- Exact amplitude coordinates of the uncorrected physical estimator.
All assumptions concern the finite dimension and predetermined batches. -/
theorem amplitude_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (pureEstimate hd batchSize n path))
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  exact amplitude_clt_of_projector_clt truth (pureEstimate hd batchSize)
    (pureEstimate_measurable hd batchSize) (pureEstimate_consistent hd truth batchSize)
    (coordinates_clt hd truth batchSize hpositive)

theorem smoothChart_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (φ : EuclideanSpace ℝ (TangentIndex d) → EuclideanSpace ℝ (TangentIndex d))
    (hφm : Measurable φ) (J : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] EuclideanSpace ℝ (TangentIndex d))
    (hφ : HasFDerivAt φ J 0) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • (φ (amplitudeCoordinates truth
        (pureEstimate hd batchSize n path))-φ 0)) atTop (fun z => J z)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  exact smoothChart_clt_of_amplitude_clt truth (pureEstimate hd batchSize)
    (pureEstimate_measurable hd batchSize) (pureEstimate_consistent hd truth batchSize)
    (amplitude_clt hd truth batchSize hpositive) φ hφm J hφ

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
