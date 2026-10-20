import QubitOracle.Paper.CovarianceLimits
import QubitOracle.AdaptiveDesign.LibraryCovariance
import QubitOracle.AdaptiveDesign.POVMEstimatorMoments
import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance

/-! Actual population covariance limits in the same-record comparison.
The fourth moments are derived for the implemented estimators. Neither
covariance convergence nor a moment bound on an output is a hypothesis of
the final protocol theorems. The factor sqrt(2) converts the off-diagonal
coordinates to a Frobenius-orthonormal tangent basis. -/
namespace QubitOracle.AdaptiveDesign.ActualEstimatorCovariance
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseMoments AdaptiveRidgeConsistency CoerciveLeastSquares
open LibraryUnweighted
open QubitOracle.Paper.EmpiricalCovariance
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

theorem uniformMoment_clm {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → E} {p : ℕ}
    (hX : UniformMoment μ X p) (L : E →L[ℝ] F) :
    UniformMoment μ (fun n ω => L (X n ω)) p := by
  apply hX.of_dominated _ (fun n => L.continuous.comp_aestronglyMeasurable
    ((Classical.choose_spec hX).2 n).1.1) ‖L‖ (norm_nonneg _)
  exact fun n ω => L.le_opNorm (X n ω)

theorem covarianceMatrix_smul {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ ι) (a : ℝ) :
    covarianceMatrix (μ:=μ) (fun ω => a • X ω) = a^2 • covarianceMatrix (μ:=μ) X := by
  ext i j
  simp only [covarianceMatrix,PiLp.smul_apply,smul_eq_mul,
    covariance_const_mul_left,covariance_const_mul_right,Matrix.smul_apply]
  ring

theorem gaussian_covariance_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (c : ℝ) (hc : 0 ≤ c)
    (hw : TendstoInDistribution X atTop id (fun _ => μ)
      (multivariateGaussian 0 (c • (1 : Matrix ι ι ℝ))))
    (h4 : UniformMoment μ (fun n => X (n+1)) 4) :
    Tendsto (fun n => covarianceMatrix (μ:=μ) (X n)) atTop
      (𝓝 (c • (1 : Matrix ι ι ℝ))) := by
  have hs : TendstoInDistribution (fun n => X (n+1)) atTop id (fun _ => μ)
      (multivariateGaussian 0 (c • (1 : Matrix ι ι ℝ))) :=
    ⟨fun n => hw.forall_aemeasurable (n+1),hw.aemeasurable_limit,
      hw.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  have hZ : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 4
      (multivariateGaussian 0 (c • (1 : Matrix ι ι ℝ))) :=
    IsGaussian.memLp_id _ 4 (by norm_num)
  have ht := covariance_matrix_tendsto _ _ hs h4 hZ
  have he : covarianceMatrix (μ:=multivariateGaussian 0 (c • (1 : Matrix ι ι ℝ)))
      (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) = c • (1 : Matrix ι ι ℝ) := by
    ext i j
    exact covariance_eval_multivariateGaussian (Matrix.PosSemidef.one.smul hc) i j
  rw [he] at ht
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem rescaled_covariance_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (c : ℝ)
    (ht : Tendsto (fun n => covarianceMatrix (μ:=μ) (X n)) atTop
      (𝓝 (c • (1 : Matrix ι ι ℝ)))) :
    Tendsto (fun n => covarianceMatrix (μ:=μ) (fun ω => (Real.sqrt 2/2) • X n ω))
      atTop (𝓝 ((c/2) • (1 : Matrix ι ι ℝ))) := by
  have ha : (Real.sqrt 2/2)^2=(1/2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  simpa only [covarianceMatrix_smul,ha,smul_smul,show (1/2:ℝ)*c=c/2 by ring]
    using ht.const_smul (1/2:ℝ)

theorem normalized_trace_limit {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : ℕ → Matrix ι ι ℝ) (c : ℝ)
    (ht : Tendsto C atTop (𝓝 (c • (1 : Matrix ι ι ℝ)))) :
    Tendsto (fun n => Matrix.trace (C n)/(Fintype.card ι:ℝ)) atTop (𝓝 c) := by
  have hcont : Continuous (fun M : Matrix ι ι ℝ => Matrix.trace M/(Fintype.card ι:ℝ)) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hh := hcont.tendsto (c • (1 : Matrix ι ι ℝ)) |>.comp ht
  have hn : (Fintype.card ι:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [Function.comp_def,Matrix.trace_smul,Matrix.trace_one,smul_eq_mul,
    mul_div_cancel_right₀ c hn] using hh

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def frobeniusCoordinates (truth : PureVector d) :
    HermitianSpace (d+1) →L[ℝ] EuclideanSpace ℝ (TangentIndex d) :=
  Real.sqrt 2 • trueCoordinate truth

theorem frobeniusCoordinates_norm (truth : PureVector d) (A : HermitianSpace (d+1)) :
    ‖frobeniusCoordinates truth A‖ = ‖tangentProjector truth A‖ := by
  have he : ‖tangentProjector truth A‖^2=2*‖trueCoordinate truth A‖^2 := by
    have hi := trueLift_inner truth (trueCoordinate truth A)
      (trueLift truth (trueCoordinate truth A))
    rw [trueCoordinate_lift,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
      trueLift_coordinate] at hi
    exact hi
  rw [frobeniusCoordinates,ContinuousLinearMap.smul_apply,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),he]

theorem corrected_covariance_limit
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    let μ := adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth
    Tendsto (fun (n : ℕ) => covarianceMatrix (μ:=μ) (fun path =>
      frobeniusCoordinates truth (Real.sqrt (n:ℝ) •
        actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path)))
      atTop (𝓝 (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) := by
  let Y := fun (n : ℕ) path => Real.sqrt (n:ℝ) • trueFrameCoordinates truth
    (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n)
  have hw := optimalVariance P hI hp hF truth regularization ridge hr hη batchSize hpositive
  have h4 : UniformMoment
      (adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n => Y (n+1)) 4 := by
    have hm := uniformMoment_clm
      (POVMEstimatorMoments.corrected_uniformMoment P hI hp truth regularization ridge hr hη batchSize 4)
      ((2:ℝ) • trueCoordinate truth)
    simpa only [Y,trueFrameCoordinates_actual,ContinuousLinearMap.smul_apply,map_smul,
      smul_smul,mul_comm] using hm
  have ht := rescaled_covariance_limit Y 2 (gaussian_covariance_limit Y 2 (by norm_num) hw h4)
  have he : ∀ (n : ℕ) path,(Real.sqrt 2/2) • Y n path =
      frobeniusCoordinates truth (Real.sqrt (n:ℝ) •
        actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path) := by
    intro n path
    simp only [Y,trueFrameCoordinates_actual,frobeniusCoordinates,
      ContinuousLinearMap.smul_apply,map_smul,smul_smul]
    congr 1
    ring
  simpa only [he,show (2:ℝ)/2=1 by norm_num,one_smul] using ht

theorem library_raw_uniformMoment (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (P2Adaptive.adaptiveProtocol hd batchSize)
      (pureParameter d truth)) (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (P2Adaptive.rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val)) p := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  let protocol := P2Adaptive.adaptiveProtocol hd batchSize
  letI : IsMarkovKernel (protocol.response (pureParameter d truth)) := protocol.response_isMarkov _
  let μ := adaptiveInfiniteTrajectoryMeasure protocol (pureParameter d truth)
  let θ := (pureParameter d truth).val
  let κ := P2Adaptive.coercivityConstant hd
  have hκ : 0 < κ := P2Adaptive.coercivityConstant_pos hd
  let g := fun a y => responseVector hd a y-regressionFrame hd a θ
  have hmean (a) : ∫ y,g a y ∂protocol.response (pureParameter d truth) a = 0 := by
    change (∫ y,responseVector hd a y-regressionFrame hd a θ
      ∂bornKernel hd (pureParameter d truth) a)=0
    rw [integral_sub Integrable.of_finite (integrable_const _),responseVector_mean hd]
    simp [θ]
  let S := fun n path => ∑ k ∈ Finset.range (n+1),actualVectorResponse protocol g k path
  have hS := actualVectorResponse_uniformMoment protocol (pureParameter d truth) g hmean
    (2*responseBound hd) (by have h:=responseBound_nonnegative hd;positivity)
    (responseInnovation_bound hd (pureParameter d truth)) p
  have hB : UniformMoment μ (fun n (_ : AdaptiveInfinitePath (Outcome d)) =>
      (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (-θ)) p := by
    apply uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const)
      ‖-θ‖ (norm_nonneg _)
    intro n path
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hsqrt : 1 ≤ Real.sqrt ((n+1:ℕ):ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)];norm_num
    exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (by positivity)).mpr hsqrt)
  have hSB : UniformMoment μ (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (S n path-θ)) p := by
    simpa only [smul_add,smul_neg,sub_eq_add_neg] using hS.add hB
  apply hSB.of_dominated _ (fun n =>
    (LibraryUnweighted.statistic_measurable hd batchSize (n+1)
      (fun raw => Real.sqrt ((n+1:ℕ):ℝ) • (raw-θ))).aestronglyMeasurable)
    κ⁻¹ (inv_nonneg.mpr hκ.le)
  intro n path
  have he := ridgeEstimate_error_bound
    (fun k => regressionFrame hd (actualAction protocol path k))
    (fun k => responseVector hd (actualAction protocol path k) (path k)) θ
    1 κ zero_lt_one hκ.le (fun k => P2Adaptive.regressionFrame_coercive hd _) (n+1)
  have hN : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have he' : ‖P2Adaptive.rawEstimator hd batchSize path (n+1)-θ‖ ≤
      ‖S n path-θ‖/(((n+1:ℕ):ℝ)*κ) := by
    rw [LibraryUnweighted.raw_eq_ridge hd]
    simpa only [one_smul,S,g,actualVectorResponse,actualAction,
      CoerciveLeastSquares.innovation,actualRidgeEstimate,protocol,κ] using he.trans
      (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hN hκ) (by linarith))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.sqrt ((n+1:ℕ):ℝ)*(‖S n path-θ‖/(((n+1:ℕ):ℝ)*κ)) :=
      mul_le_mul_of_nonneg_left he' (Real.sqrt_nonneg _)
    _ = _ := by
      have hs := Real.sq_sqrt hN.le
      have hs0 : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      field_simp [hN.ne',hκ.ne',hs0]
      rw [hs]
      ring

theorem library_pure_uniformMoment (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (P2Adaptive.adaptiveProtocol hd batchSize)
      (pureParameter d truth)) (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (LibraryUnweighted.pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val)) p := by
  refine (library_raw_uniformMoment hd truth batchSize p).of_dominated
    (fun (n : ℕ) (path : AdaptiveInfinitePath (Outcome d)) =>
      Real.sqrt ((n+1:ℕ):ℝ) •
        (LibraryUnweighted.pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val))
    ?_ 2 (by norm_num) ?_
  · intro n
    exact ((LibraryUnweighted.pureEstimate_measurable hd batchSize (n+1)).sub
      (stronglyMeasurable_const (b := (pureParameter d truth).val))).const_smul
        (Real.sqrt ((n+1:ℕ):ℝ)) |>.aestronglyMeasurable
  intro n path
  simp only [norm_smul]
  have hb : ‖LibraryUnweighted.pureEstimate hd batchSize (n+1) path-(pureParameter d truth).val‖ ≤
      2*‖P2Adaptive.rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val‖ := by
    rw [← toMatrix_norm,← toMatrix_norm]
    exact projectedMatrix_error_le_two d truth _
  nlinarith [norm_nonneg (Real.sqrt ((n+1:ℕ):ℝ))]

theorem library_covariance_limit (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j,0 < batchSize j) :
    let μ := adaptiveInfiniteTrajectoryMeasure (P2Adaptive.adaptiveProtocol hd batchSize)
      (pureParameter d truth)
    Tendsto (fun (n : ℕ) => covarianceMatrix (μ:=μ) (fun path =>
      frobeniusCoordinates truth (Real.sqrt (n:ℝ) •
        (LibraryUnweighted.pureEstimate hd batchSize n path-(pureParameter d truth).val))))
      atTop (𝓝 (tangentVariance d • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  let Y := fun (n : ℕ) path => Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth
    (LibraryUnweighted.pureEstimate hd batchSize n path-(pureParameter d truth).val))
  have hw := LibraryUnweighted.coordinates_clt hd truth batchSize hpositive
  have h4 : UniformMoment (adaptiveInfiniteTrajectoryMeasure (P2Adaptive.adaptiveProtocol hd batchSize)
      (pureParameter d truth)) (fun n => Y (n+1)) 4 := by
    have hm := uniformMoment_clm (library_pure_uniformMoment hd truth batchSize 4)
      ((2:ℝ) • trueCoordinate truth)
    simpa only [Y,ContinuousLinearMap.smul_apply,map_smul,smul_smul,mul_comm] using hm
  have hc : 0 ≤ 2*tangentVariance d := by
    rw [← LibraryUnweighted.variance_ratio hd]
    exact mul_nonneg (by norm_num) (div_nonneg (LibraryUnweighted.constants_positive hd).2.le (sq_nonneg _))
  have ht := rescaled_covariance_limit Y (2*tangentVariance d)
    (gaussian_covariance_limit Y (2*tangentVariance d) hc hw h4)
  have he : ∀ (n : ℕ) path,(Real.sqrt 2/2) • Y n path =
      frobeniusCoordinates truth (Real.sqrt (n:ℝ) •
        (LibraryUnweighted.pureEstimate hd batchSize n path-(pureParameter d truth).val)) := by
    intro n path
    simp only [Y,frobeniusCoordinates,ContinuousLinearMap.smul_apply,map_smul,smul_smul]
    congr 1
    ring
  simpa only [he,show 2*tangentVariance d/2=tangentVariance d by ring] using ht

end
end QubitOracle.AdaptiveDesign.ActualEstimatorCovariance
