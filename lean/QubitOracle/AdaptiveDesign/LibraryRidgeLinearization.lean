import QubitOracle.AdaptiveDesign.LibraryScoreCLT
import QubitOracle.AdaptiveDesign.GeneralPOVMRootRate
import QubitOracle.AdaptiveDesign.GeneralPOVMQuarterRate
import QubitOracle.AdaptiveDesign.FiniteHistoryStatistics

/-! The actual ridge normal equation, root-n tightness, and tangent
asymptotic linear representation for the optional finite library. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency CoerciveLeastSquares ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma raw_eq_ridge {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    rawEstimator hd batchSize path n = actualRidgeEstimate (adaptiveProtocol hd batchSize)
      (regressionFrame hd) (responseVector hd) 1 (coercivityConstant hd) zero_lt_one
      (coercivityConstant_pos hd).le (regressionFrame_coercive hd) path n :=
  SequentialRidgeController.pathState_estimate_eq_ridgeEstimate
    (regressionFrame hd) (responseVector hd) (physicalController d)
    (SequentialRidgeController.batchRefresh batchSize) 1 (coercivityConstant hd) zero_lt_one
    (coercivityConstant_pos hd).le (regressionFrame_coercive hd) path n

lemma state_eq_of_agrees {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path path' : AdaptiveInfinitePath (Outcome d)) (h : ∀ k<n, path k=path' k) :
    actualState hd batchSize path n=actualState hd batchSize path' n := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  unfold actualState SequentialRidgeController.pathState
  rw [FiniteHistoryStatistics.prefix_eq_of_agrees n path path' h]

lemma statistic_measurable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : 0 < d) (batchSize : ℕ → ℕ) (n : ℕ)
    (f : HermitianSpace (d+1) → E) :
    StronglyMeasurable (fun path => f (rawEstimator hd batchSize path n)) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  apply FiniteHistoryStatistics.stronglyMeasurable_of_past n
  intro path path' h
  unfold rawEstimator
  rw [state_eq_of_agrees hd batchSize n path path' h]

theorem raw_rootTight {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val)) atTop := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  simp_rw [raw_eq_ridge hd]
  exact GeneralPOVMRootRate.actualRidgeEstimate_rootTight _ _ _ _ _ 1 (coercivityConstant hd)
    zero_lt_one (coercivityConstant_pos hd) (regressionFrame_coercive hd)
    (responseVector_mean hd (pureParameter d truth)) (2*responseBound hd)
    (by have h := responseBound_nonnegative hd; positivity)
    (responseInnovation_bound hd (pureParameter d truth))

theorem raw_square_negligible {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) *
        ‖rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val‖^2) atTop (fun _ => 0) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  have hh := GeneralPOVMQuarterRate.actualRidgeEstimate_quarterRate
    (adaptiveProtocol hd batchSize) (pureParameter d truth) (regressionFrame hd) (responseVector hd)
    (pureParameter d truth).val 1 (coercivityConstant hd) zero_lt_one (coercivityConstant_pos hd)
    (regressionFrame_coercive hd) (responseVector_mean hd (pureParameter d truth))
    (2*responseBound hd) (by have h := responseBound_nonnegative hd; positivity)
    (responseInnovation_bound hd (pureParameter d truth))
  have hsq := square_norm_zero hh
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, BoundedResponseQuarterRate.quarterScale_sq,
    ← raw_eq_ridge hd] using hsq

def noiseSum {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) : HermitianSpace (d+1) :=
  ∑ k ∈ Finset.range n, actualVectorResponse (adaptiveProtocol hd batchSize) (innovation hd truth) k path

def projectedGram {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) : HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  (n:ℝ)⁻¹ • (tangentProjector truth+
    ∑ k ∈ Finset.range n, (tangentProjector truth).comp (frameAt hd (measurementFrame hd batchSize path k)))

lemma projectedGram_measurable {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (n : ℕ) : StronglyMeasurable (projectedGram hd truth batchSize n) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  apply FiniteHistoryStatistics.stronglyMeasurable_of_past n
  intro path path' h
  apply congrArg (fun S : HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) =>
    (n:ℝ)⁻¹ • (tangentProjector truth+S))
  apply Finset.sum_congr rfl
  intro k hk
  unfold measurementFrame
  rw [state_eq_of_agrees hd batchSize k path path' (fun j hj => h j (hj.trans (Finset.mem_range.mp hk)))]

theorem projectedGram_limit {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (fun n => projectedGram hd truth batchSize n path) atTop
        (𝓝 (gramConstant d • tangentProjector truth)) := by
  filter_upwards [actual_ray_limit hd truth batchSize hpositive] with path hp
  have hh := (projected_frame_limit hd truth _ (measurementFrame_unitary hd batchSize path) hp).cesaro_smul
  have hz := (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ)).smul_const (tangentProjector truth)
  simpa only [projectedGram, smul_add, zero_smul, zero_add] using hz.add hh

lemma tangent_truth_zero {d : ℕ} (truth : PureVector d) :
    tangentProjector truth (pureParameter d truth).val=0 := by
  apply toMatrix_injective
  rw [tangentProjector_apply]
  change tangentProjectionMatrix truth (pureParameter d truth).val=0
  simp [tangentProjectionMatrix, pureParameter, pureProjector_idempotent]

lemma projected_error_equation {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (Outcome d)) :
    projectedGram hd truth batchSize n path
      (rawEstimator hd batchSize path n-(pureParameter d truth).val) =
        (n:ℝ)⁻¹ • tangentProjector truth (noiseSum hd truth batchSize n path) := by
  have hh := ridgeEstimate_errorEquation
    (fun k => regressionFrame hd (actualAction (adaptiveProtocol hd batchSize) path k))
    (fun k => responseVector hd (actualAction (adaptiveProtocol hd batchSize) path k) (path k))
    (pureParameter d truth).val 1 (coercivityConstant hd) zero_lt_one
    (coercivityConstant_pos hd).le (fun k => regressionFrame_coercive hd _) n
  change ridgeGram _ 1 n (actualRidgeEstimate (adaptiveProtocol hd batchSize)
    (regressionFrame hd) (responseVector hd) 1 (coercivityConstant hd) zero_lt_one
    (coercivityConstant_pos hd).le (regressionFrame_coercive hd) path n-
    (pureParameter d truth).val) = noiseSum hd truth batchSize n path-1 • (pureParameter d truth).val at hh
  rw [← raw_eq_ridge hd] at hh
  have ht := congrArg (fun A => (n:ℝ)⁻¹ • tangentProjector truth A) hh
  have hzero : tangentProjector truth (noiseSum hd truth batchSize n path-(1:ℝ) • (pureParameter d truth).val) =
      tangentProjector truth (noiseSum hd truth batchSize n path) := by
    rw [one_smul, map_sub, tangent_truth_zero, sub_zero]
  have ht' := ht.trans (congrArg (fun A : HermitianSpace (d+1) => (n:ℝ)⁻¹ • A) hzero)
  have hf (k : ℕ) (A : HermitianSpace (d+1)) :
      frameAt hd (measurementFrame hd batchSize path k) A =
        regressionFrame hd (actualAction (adaptiveProtocol hd batchSize) path k) A := by
    simp only [frameAt, gramCLM_apply, one_mul, regressionFrame, FiniteFrameCoercivity.frameOperator_apply]
    rfl
  simpa only [projectedGram, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ridgeGram_apply,
    map_add, map_sum, one_smul, hf] using ht'

theorem tangent_linearization {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) • tangentProjector truth
        (rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val)-
          ((gramConstant d*Real.sqrt ((n+1:ℕ):ℝ))⁻¹) •
            tangentProjector truth (noiseSum hd truth batchSize (n+1) path)) atTop (fun _ => 0) := by
  have hG : TendstoInMeasure
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (fun n path => projectedGram hd truth batchSize (n+1) path-gramConstant d • tangentProjector truth)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun n => ((projectedGram_measurable hd truth batchSize (n+1)).sub stronglyMeasurable_const).aestronglyMeasurable
    · filter_upwards [projectedGram_limit hd truth batchSize hpositive] with path hp
      simpa using (hp.comp (tendsto_add_atTop_nat 1)).sub_const (gramConstant d • tangentProjector truth)
  have hz := clm_apply_zero hG (raw_rootTight hd truth batchSize)
  have hs := continuousAt_const hz
    (show ContinuousAt (fun x : HermitianSpace (d+1) => -(gramConstant d)⁻¹ • x) 0 by fun_prop)
  simp only [smul_zero] at hs
  apply hs.congr _ EventuallyEq.rfl
  intro n
  apply Eventually.of_forall
  intro path
  change -(gramConstant d)⁻¹ •
      (projectedGram hd truth batchSize (n+1) path-gramConstant d • tangentProjector truth)
        (Real.sqrt ((n+1:ℕ):ℝ) • (rawEstimator hd batchSize path (n+1)-(pureParameter d truth).val)) = _
  rw [map_smul]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, projected_error_equation,
    smul_sub, smul_smul]
  have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  have ha := (constants_positive hd).1.ne'
  have hr : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have he : -(gramConstant d)⁻¹*(Real.sqrt ((n+1:ℕ):ℝ)*((n+1:ℕ):ℝ)⁻¹) =
      -(gramConstant d*Real.sqrt ((n+1:ℕ):ℝ))⁻¹ := by
    rw [mul_inv, ← div_eq_mul_inv (Real.sqrt _), Real.sqrt_div_self]
    ring
  rw [he]
  have he' : -(gramConstant d)⁻¹*(Real.sqrt ((n+1:ℕ):ℝ)*gramConstant d) =
      -Real.sqrt ((n+1:ℕ):ℝ) := by field_simp
  rw [he']
  module

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
