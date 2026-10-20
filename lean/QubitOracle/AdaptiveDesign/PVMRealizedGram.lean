-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotMomentLimits
import QubitOracle.AdaptiveDesign.PVMTangentLeastSquares
import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseStrongLaw

/-! Actual random-basis Gram convergence, including its martingale
fluctuations and the data-dependent fitted tangent space. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMPilotBorn
open PVMUniformMoments Filter MeasureTheory ProbabilityTheory AdaptiveRidgeConsistency
open FiniteDimensionalResponseRates
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

abbrev Operator (d : ℕ) := HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1)

def basisGramOperator (U : Action d) : Operator d := gramCLM (basisEffect U) (fun _ => 1)
def meanGram (a : ℕ × Action d) : Operator d :=
  ∑ b : Setting d, settingWeight d a.1 b • basisGramOperator (settingBasis a.2 b)
def gramNoise (a : ℕ × Action d) (o : Outcome d) : Operator d :=
  basisGramOperator (settingBasis a.2 o.1)-meanGram a

def gramBound (d : ℕ) : ℝ := (d+1:ℝ)*(basisBound d)^2
lemma gramBound_nonnegative (d : ℕ) : 0 ≤ gramBound d := by unfold gramBound; positivity
lemma basisGramOperator_bound (U : Action d) : ‖basisGramOperator U‖ ≤ gramBound d := by
  have h := gramCLM_bound_constant (basisEffect U) (fun _ => 1) (basisBound d) 1
    (basisBound_nonnegative d) zero_le_one (basisEffect_bound U) (fun _ => by norm_num)
  simpa [basisGramOperator,gramBound] using h

lemma meanGram_bound (a : ℕ × Action d) : ‖meanGram a‖ ≤ gramBound d := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ b : Setting d, settingWeight d a.1 b*gramBound d := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (settingWeight_nonnegative _ _ _)]
      exact mul_le_mul_of_nonneg_left (basisGramOperator_bound _) (settingWeight_nonnegative _ _ _)
    _ = _ := by rw [← Finset.sum_mul,settingWeight_sum,one_mul]

lemma gramNoise_bound (a : ℕ × Action d) (o : Outcome d) : ‖gramNoise a o‖ ≤ 2*gramBound d :=
  (norm_sub_le _ _).trans (by linarith [basisGramOperator_bound (settingBasis a.2 o.1),meanGram_bound a])

lemma gramNoise_mean (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, gramNoise a o ∂bornKernel theta a=0 := by
  have hm : ∫ o, basisGramOperator (settingBasis a.2 o.1) ∂bornKernel theta a=meanGram a := by
    rw [integral_bornKernel]
    simp only [← Finset.sum_smul, basisProbability_sum,one_smul,meanGram]
  simp only [gramNoise]
  rw [integral_sub Integrable.of_finite (integrable_const _),hm]
  simp

def realizedGram (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : Operator d :=
  ∑ k ∈ Finset.range n, basisGramOperator
    (settingBasis (PVMPilotAdaptive.actualState d batchSize path k).action (path k).1)

def compress (truth : PureVector d) : Operator d →L[ℝ] Operator d :=
  ({ toFun := fun K => (tangentProjector truth).comp (K.comp (tangentProjector truth))
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } : Operator d →ₗ[ℝ] Operator d).toContinuousLinearMap

lemma informationLift_sum_smul {J : Type} [Fintype J] (truth : PureVector d)
    (q : J → ℝ) (M : J → Matrix (TangentIndex d) (TangentIndex d) ℝ) :
    informationLift truth (∑ j, q j • M j)=∑ j, q j • informationLift truth (M j) := by
  ext x
  simp only [informationLift,map_sum,map_smul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  module

lemma compress_meanGram (truth : PureVector d) (a : ℕ × Action d) :
    compress truth (meanGram a)=informationLift truth (coordinateGram truth a) := by
  rw [meanGram,map_sum,coordinateGram,informationLift_sum_smul]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  congr 1
  exact basis_projectedGram truth (settingBasis a.2 b)

lemma informationLift_scalar (truth : PureVector d) (c : ℝ) :
    informationLift truth (c • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) =
      (2*c) • tangentProjector truth := by
  ext x
  simp only [informationLift,map_smul,map_one,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,smul_smul, trueLift_coordinate]

lemma informationLift_gram_target (truth : PureVector d) :
    informationLift truth ((1/(2*(d+1:ℝ))) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) =
      (1/(d+1:ℝ)) • tangentProjector truth := by
  rw [informationLift_scalar]
  congr 1
  field_simp

lemma realizedGram_centered_ae (truth : PureVector d) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • (realizedGram batchSize n path-
        ∑ k ∈ Finset.range n, meanGram (k,(PVMPilotAdaptive.actualState d batchSize path k).action)))
        atTop (𝓝 0) := by
  have hh := actualResponse_average_ae_normed (PVMPilotAdaptive.adaptiveProtocol d batchSize)
    (pureParameter d truth) gramNoise (gramNoise_mean _) (2*gramBound d)
    (mul_nonneg (by norm_num) (gramBound_nonnegative d)) gramNoise_bound
  filter_upwards [hh] with path hp
  have hdesign k : (PVMPilotAdaptive.adaptiveProtocol d batchSize).design k
      (adaptiveInfinitePathPrefix k path) =
      (k,(PVMPilotAdaptive.actualState d batchSize path k).action) := rfl
  simpa only [realizedGram, ← Finset.sum_sub_distrib, gramNoise, actualVectorResponse,
    hdesign] using hp

lemma trueGram_limit (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • compress truth (realizedGram batchSize n path))
        atTop (𝓝 ((1/(d+1:ℝ)) • tangentProjector truth)) := by
  filter_upwards [realizedGram_centered_ae truth batchSize,actual_moment_limits truth batchSize hpositive]
    with path hn hm
  have hnoise := (compress truth).continuous.continuousAt.tendsto.comp hn
  simp only [Function.comp_def,map_smul,map_sub,map_sum,map_zero] at hnoise
  have hmean := ((informationLift_continuous truth).continuousAt.tendsto.comp hm.1).cesaro_smul
  simp only [Function.comp_def, ← compress_meanGram, ← map_sum,informationLift_gram_target] at hmean
  have hs := hnoise.add hmean
  simpa only [map_sum,smul_sub, sub_add_cancel, zero_add] using hs

lemma recordInformation_eq_realized (h : PureVector d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) :
    recordInformation h (actualRecords batchSize path n) (floor d)=compress h (realizedGram batchSize n path) := by
  ext x
  simp only [recordInformation,unit_weight,ContinuousLinearMap.comp_apply,gramCLM_apply,
    Fintype.sum_prod_type,recordFeature_eq]
  change _ = tangentProjector h ((realizedGram batchSize n path) (tangentProjector h x))
  rw [realizedGram, ← Fin.sum_univ_eq_sum_range]
  simp only [ContinuousLinearMap.sum_apply,basisGramOperator,gramCLM_apply,one_mul]

lemma fittedGram_limit (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • recordInformation (actualPreliminary batchSize path n)
        (actualRecords batchSize path n) (floor d))
        atTop (𝓝 ((1/(d+1:ℝ)) • tangentProjector truth)) := by
  filter_upwards [actualPreliminaryError_consistent batchSize truth,trueGram_limit truth batchSize hpositive]
    with path he ht
  simp_rw [← recordInformation_eq_realized] at ht
  let B : ℝ := (d+1:ℝ)*((basisBound d)^3/(floor d)^2+12*(basisBound d)^2/floor d)
  have hd : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ •
      (recordInformation (actualPreliminary batchSize path n) (actualRecords batchSize path n) (floor d)-
        recordInformation truth (actualRecords batchSize path n) (floor d))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n => B*‖actualPreliminaryError batchSize truth n path‖)
      atTop (𝓝 0) by simpa using he.norm.const_mul B)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn')]
    have hb := recordInformation_difference (actualPreliminary batchSize path n) truth
      (actualRecords batchSize path n) (floor d) (basisBound d) (floor_pos d) (basisBound_nonnegative d)
      (fun r => by rw [recordFeature_eq]; exact basisEffect_bound _ _)
    apply (mul_le_mul_of_nonneg_left hb (inv_pos.mpr hn').le).trans_eq
    dsimp [B,actualPreliminaryError]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  simpa only [smul_sub,sub_add_cancel,zero_add] using hd.add ht

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
