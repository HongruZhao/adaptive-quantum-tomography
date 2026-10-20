-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMCorrectionLimits
import QubitOracle.AdaptiveDesign.TangentGLSAsymptoticLinearization

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityCalculus BoundedResponseQuarterRate
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def deltaVector (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  (actualDelta ridge hr batchSize path n).val

def projectorError (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  (pureParameter d (actualEstimate ridge hr batchSize path n)).val-(pureParameter d truth).val

lemma delta_quarterRate (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => quarterScale n • deltaVector ridge hr batchSize (n+1) path) atTop (fun _ => 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)
  have ht : TightNorm μ (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
      (deltaVector ridge hr batchSize (n+1) path+tangentError (actualPreliminary batchSize path (n+1)) truth)) atTop := by
    have hh := tight_add (tight_of_zero (linearError_zero truth ridge hr batchSize hpositive hbudget))
      (projectedScore_rootTight truth batchSize)
    simpa only [linearError,deltaVector,sub_add_cancel] using hh
  have hs : TendstoInMeasure μ (fun n (_ : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) =>
      quarterScale n/Real.sqrt ((n+1:ℕ):ℝ)) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound _ quarterScale_div_sqrt_zero
    intro n path
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [quarterScale]; positivity)]
  have hsum : TendstoInMeasure μ (fun n path => quarterScale n •
      (deltaVector ridge hr batchSize (n+1) path+tangentError (actualPreliminary batchSize path (n+1)) truth))
      atTop (fun _ => 0) := by
    apply product_bound_zero hs ht
    intro n path
    simp only [norm_smul,Real.norm_eq_abs,abs_div]
    have hn := (Real.sqrt_pos.mpr (show (0:ℝ)<((n+1:ℕ):ℝ) by positivity)).ne'
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp
    exact le_rfl
  have he := ProbabilityZeroAlgebra.dominated (actualPreliminaryError_quarterRate batchSize truth hbudget)
    1 (by norm_num) (fun n path => (show
      ‖-(quarterScale n • tangentError (actualPreliminary batchSize path (n+1)) truth)‖ ≤
      1*‖quarterScale n • actualPreliminaryError batchSize truth (n+1) path‖ by
        rw [norm_neg,one_mul,norm_smul,norm_smul]
        exact mul_le_mul_of_nonneg_left (preliminaryTangentError_norm_le _ truth) (norm_nonneg _)))
  simpa only [smul_add,add_neg_cancel_right] using ProbabilityZeroAlgebra.add hsum he

lemma delta_square_rootRate (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ)*‖deltaVector ridge hr batchSize (n+1) path‖^2)
      atTop (fun _ => 0) := by
  have hh := square_norm_zero (delta_quarterRate truth ridge hr batchSize hpositive hbudget)
  simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,quarterScale_sq] using hh

lemma ambientScore_rootTight (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => ((d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ)) • scoreSum truth batchSize (n+1) path) atTop := by
  apply tight_dominated (scoreSum_rootTight truth batchSize) (d+1:ℝ) (by positivity)
  intro n path
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (show (0:ℝ)≤(d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ) by positivity),
    abs_of_nonneg (show (0:ℝ)≤(Real.sqrt ((n+1:ℕ):ℝ))⁻¹ by positivity)]
  exact le_of_eq (by ring)

lemma projectorError_linearization (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) • projectorError truth ridge hr batchSize (n+1) path-
        ((d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ)) • tangentProjector truth (scoreSum truth batchSize (n+1) path))
      atTop (fun _ => 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)
  have hgeom : TendstoInMeasure μ (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
      (projectorError truth ridge hr batchSize (n+1) path-
        (actualPreliminaryError batchSize truth (n+1) path+deltaVector ridge hr batchSize (n+1) path)))
      atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated (delta_square_rootRate truth ridge hr batchSize hpositive hbudget) 3 (by norm_num)
    intro n path
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left (updated_error_bound
      (actualPreliminary batchSize path (n+1)) truth (actualRecords batchSize path (n+1)) ridge hr)
      (Real.sqrt_nonneg ((n+1:ℕ):ℝ))
    apply hb.trans_eq
    change Real.sqrt ((n+1:ℕ):ℝ)*(3*‖deltaVector ridge hr batchSize (n+1) path‖^2) = _
    ring
  have hnormal : TendstoInMeasure μ (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
      (actualPreliminaryError batchSize truth (n+1) path-tangentError (actualPreliminary batchSize path (n+1)) truth))
      atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated (actualPreliminaryError_square_rootRate batchSize truth hbudget) 3 (by norm_num)
    intro n path
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left (preliminaryError_normal_bound
      (actualPreliminary batchSize path (n+1)) truth) (Real.sqrt_nonneg ((n+1:ℕ):ℝ))
    exact hb.trans_eq (by dsimp only [actualPreliminaryError]; ring)
  have hQ : TendstoInMeasure μ (fun n path =>
      tangentProjector (actualPreliminary batchSize path (n+1))-tangentProjector truth) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (actualStatistic_stronglyMeasurable batchSize (n+1) (fun raw _ =>
        tangentProjector (nearestVector d (toMatrix raw))-tangentProjector truth)).aestronglyMeasurable
    · filter_upwards [fittedProjector_limit truth batchSize] with path hp
      simpa using (hp.comp (tendsto_add_atTop_nat 1)).sub_const (tangentProjector truth)
  have hscore := clm_apply_zero hQ (ambientScore_rootTight truth batchSize)
  have hh := ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add hgeom hnormal)
    (linearError_zero truth ridge hr batchSize hpositive hbudget)) hscore
  convert hh using 1
  funext n path
  simp only [linearError,projectedScore,deltaVector,ContinuousLinearMap.sub_apply,map_smul,smul_sub,smul_add]
  abel

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
