-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMCorrectionAlgebra

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma fittedProjector_limit (truth : PureVector d) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n => tangentProjector (actualPreliminary batchSize path n))
        atTop (𝓝 (tangentProjector truth)) := by
  filter_upwards [actualPreliminaryError_consistent batchSize truth] with path he
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm (fun n => tangentProjector_lipschitz _ truth)
  simpa only [actualPreliminaryError,_root_.norm_zero,MulZeroClass.mul_zero] using he.norm.const_mul 6

lemma operatorError_limit (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n => recordOperatorError (actualPreliminary batchSize path n)
        (actualRecords batchSize path n) ridge) atTop (𝓝 0) := by
  filter_upwards [fittedProjector_limit truth batchSize,fittedGram_limit truth batchSize hpositive]
    with path hQ hG
  have hr0 : Tendsto (fun n : ℕ => ((d+1:ℝ)*ridge)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hd := hG.const_smul (d+1:ℝ)
  have hd' : (d+1:ℝ) • ((1/(d+1:ℝ)) • tangentProjector truth) = tangentProjector truth := by
    rw [smul_smul]
    have he : (d+1:ℝ)*(1/(d+1:ℝ))=1 := by field_simp
    rw [he,one_smul]
  rw [hd'] at hd
  have hh := ((hr0.smul hQ).add hd).sub hQ
  simpa only [recordOperatorError,recordOperator,smul_add,smul_smul,div_eq_mul_inv,
    mul_assoc,mul_left_comm,mul_comm,zero_smul,zero_add,sub_self] using hh

lemma operatorError_zero (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => recordOperatorError (actualPreliminary batchSize path n)
        (actualRecords batchSize path n) ridge) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (actualStatistic_stronglyMeasurable batchSize n (fun raw data =>
      recordOperatorError (nearestVector d (toMatrix raw)) data ridge)).aestronglyMeasurable
  · exact operatorError_limit truth ridge batchSize hpositive

def projectedScore (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  ((d+1:ℝ)/Real.sqrt (n:ℝ)) • tangentProjector (actualPreliminary batchSize path n)
    (scoreSum truth batchSize n path)

def linearError (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  Real.sqrt (n:ℝ) • ((actualDelta ridge hr batchSize path n).val+
    tangentError (actualPreliminary batchSize path n) truth)-projectedScore truth batchSize n path

def forcing (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  ((d+1:ℝ)/Real.sqrt (n:ℝ)) • normalRemainder (actualPreliminary batchSize path n) truth
    (actualRecords batchSize path n) ridge -
  recordOperatorError (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge
    (projectedScore truth batchSize n path)

lemma linearError_equation (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (hn : 0 < n)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
    linearError truth ridge hr batchSize n path +
      recordOperatorError (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge
        (linearError truth ridge hr batchSize n path) = forcing truth ridge batchSize n path := by
  apply scaled_ambient_equation
    (recordOperator (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge)
    (tangentProjector (actualPreliminary batchSize path n)) _ _ _ (n:ℝ) (d+1:ℝ)
    (by exact_mod_cast hn)
  · exact tangentProjector_self _ (actualDelta ridge hr batchSize path n+
      preliminaryTangentError (actualPreliminary batchSize path n) truth)
  · exact tangentProjector_idem _ _
  · exact actual_normal_equation truth ridge hr batchSize n path

lemma linearError_measurable (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) : StronglyMeasurable (linearError truth ridge hr batchSize n) := by
  apply FiniteHistoryStatistics.stronglyMeasurable_of_past n
  intro path path' he
  simp only [linearError,projectedScore,actualDelta,actualPreliminary,scoreSum_records]
  rw [rawEstimator_eq_of_agrees batchSize n path path' he,
    actualRecords_eq_of_agrees batchSize n path path' he]

lemma projectedScore_rootTight (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => projectedScore truth batchSize (n+1) path) atTop := by
  apply tight_dominated (scoreSum_rootTight truth batchSize) (d+1:ℝ) (by positivity)
  intro n path
  have hb := ((tangentProjector (actualPreliminary batchSize path (n+1))).le_opNorm
    ((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • scoreSum truth batchSize (n+1) path)).trans
    (mul_le_mul_of_nonneg_right (tangentProjector_norm_le _) (norm_nonneg _))
  have he : projectedScore truth batchSize (n+1) path = (d+1:ℝ) •
      tangentProjector (actualPreliminary batchSize path (n+1))
        ((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • scoreSum truth batchSize (n+1) path) := by
    simp only [projectedScore,map_smul,smul_smul,div_eq_mul_inv]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤d+1 by positivity)

lemma scaled_normalRemainder_zero (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ)
    (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => ((d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ)) • normalRemainder
        (actualPreliminary batchSize path (n+1)) truth (actualRecords batchSize path (n+1)) ridge)
      atTop (fun _ => 0) := by
  let C : ℝ := 3*(d+1:ℝ)^2*(PVMGeometry.basisBound d)^2
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have he := ProbabilityCalculus.continuousAt_const
    (actualPreliminaryError_square_rootRate batchSize truth hbudget)
    (show ContinuousAt (fun x : ℝ => C*x) 0 by fun_prop)
  simp only [MulZeroClass.mul_zero] at he
  have hs := ProbabilityZeroAlgebra.uniform_norm_bound
    (mu := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
    (fun n : ℕ => (2*(d+1:ℝ)*|ridge|)/Real.sqrt ((n+1:ℕ):ℝ))
    (by simpa only [Function.comp_def] using
      (constant_div_sqrt_nat_tendsto_zero (2*(d+1:ℝ)*|ridge|)).comp (tendsto_add_atTop_nat 1))
    (fun n (_ : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) =>
      (show ‖(2*(d+1:ℝ)*|ridge|)/Real.sqrt ((n+1:ℕ):ℝ)‖ ≤
        (2*(d+1:ℝ)*|ridge|)/Real.sqrt ((n+1:ℕ):ℝ) by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]))
  apply ProbabilityZeroAlgebra.dominated (ProbabilityZeroAlgebra.add he hs) 1 (by norm_num)
  intro n path
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (normalRemainder_bound
    (actualPreliminary batchSize path (n+1)) truth (actualRecords batchSize path (n+1)) ridge
    (PVMGeometry.basisBound d) (PVMGeometry.basisBound_nonnegative d)
    (fun r => by rw [recordFeature_eq]; exact PVMGeometry.basisEffect_bound _ _))
    (show (0:ℝ)≤(d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ) by positivity)
  apply hb.trans_eq
  simp only [Fintype.card_fin,actualPreliminaryError]
  dsimp [C]
  have hn : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hn2 := Real.sq_sqrt (show (0:ℝ)≤((n+1:ℕ):ℝ) by positivity)
  field_simp
  rw [hn2]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

lemma forcing_zero (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => forcing truth ridge batchSize (n+1) path) atTop (fun _ => 0) := by
  have hb := clm_apply_zero ((operatorError_zero truth ridge batchSize hpositive).comp (tendsto_add_atTop_nat 1))
    (projectedScore_rootTight truth batchSize)
  have hb' := ProbabilityZeroAlgebra.dominated hb 1 (by norm_num)
    (fun n path => (show ‖-recordOperatorError (actualPreliminary batchSize path (n+1))
      (actualRecords batchSize path (n+1)) ridge (projectedScore truth batchSize (n+1) path)‖ ≤
      1*‖recordOperatorError (actualPreliminary batchSize path (n+1))
      (actualRecords batchSize path (n+1)) ridge (projectedScore truth batchSize (n+1) path)‖ by simp))
  simpa only [forcing,sub_eq_add_neg] using ProbabilityZeroAlgebra.add
    (scaled_normalRemainder_zero truth ridge batchSize hbudget) hb'

lemma linearError_zero (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => linearError truth ridge hr batchSize (n+1) path) atTop (fun _ => 0) := by
  apply of_eventual_ae_bound 2 (fun n => (linearError_measurable truth ridge hr batchSize (n+1)).aestronglyMeasurable)
    (norm_zero (forcing_zero truth ridge batchSize hpositive hbudget)) tendsto_const_nhds
  filter_upwards [operatorError_limit truth ridge batchSize hpositive] with path hp
  refine ⟨0,?_⟩
  have he := ((hp.comp (tendsto_add_atTop_nat 1)).norm.eventually (gt_mem_nhds (show ‖(0:Operator d)‖<1/2 by norm_num)))
  filter_upwards [he] with n hn
  have hb := perturbation_norm_bound _ (by simpa using hn.le) (linearError truth ridge hr batchSize (n+1) path)
  rw [linearError_equation truth ridge hr batchSize (n+1) (by omega)] at hb
  simpa only [norm_norm,abs_norm,MulZeroClass.mul_zero,add_zero] using hb

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
