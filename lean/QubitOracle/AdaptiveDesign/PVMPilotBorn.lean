-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralGeometry
import QubitOracle.AdaptiveDesign.PVMPilotSchedule

/-! The literal PVM setting/outcome experiment, not a surrogate regression cycle. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotBorn
open MeasureTheory ProbabilityTheory QubitOracle.Paper
open GlobalPFSICHermitian GlobalPFSICBorn PVMGeometry PVMGeneralGeometry FiniteFrameCoercivity CoerciveLeastSquares
open PVMPilotSchedule
open scoped BigOperators InnerProductSpace
noncomputable section
variable [PVMPilotSchedule.Schedule]
set_option maxHeartbeats 2000000

abbrev Setting (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] := Bool ⊕ PVMGeneralGeometry.ExplorationIndex d
abbrev Outcome (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] := Setting d × Fin (d+1)
instance (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : MeasurableSpace (Outcome d) := ⊤
instance (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : MeasurableSingletonClass (Outcome d) where
  measurableSet_singleton _ := by trivial
instance (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : Nonempty (Outcome d) := ⟨(Sum.inl false,0)⟩

def settingBasis {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (U : Action d) : Setting d → Action d
  | Sum.inl false => PVMGeneralGeometry.exploitationChiAction U
  | Sum.inl true => PVMGeneralGeometry.exploitationTauAction U
  | Sum.inr l => PVMGeneralGeometry.explorationBasis l

def settingWeight (d n : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : Setting d → ℝ
  | Sum.inl _ => (1-epsilon n)/2
  | Sum.inr _ => epsilon n * (Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹

lemma settingWeight_nonnegative (d n : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (b : Setting d) : 0 ≤ settingWeight d n b := by
  cases b with
  | inl b => exact div_nonneg (sub_nonneg.mpr (epsilon_le_one n)) (by norm_num)
  | inr l => exact mul_nonneg (epsilon_nonnegative n) (inv_nonneg.mpr (Nat.cast_nonneg _))
lemma exploration_card_pos (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : (0:ℝ) < Fintype.card (PVMGeneralGeometry.ExplorationIndex d) := by
  exact PVMGeneralGeometry.exploration_card_pos d
lemma settingWeight_sum (d n : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : ∑ b, settingWeight d n b = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [settingWeight, Fintype.sum_bool, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_bool, Nat.cast_ofNat]
  have h := (exploration_card_pos d).ne'
  field_simp
  ring

def responseVector {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (U : Action d) (o : Outcome d) : HermitianSpace (d+1) :=
  basisEffect (settingBasis U o.1) o.2

def regressionFrame {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (n : ℕ) (U : Action d) :
    HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  ∑ b : Setting d, settingWeight d n b • basisFrame (settingBasis U b)

def bornProbability {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1))
    (a : ℕ × Action d) (o : Outcome d) : ℝ :=
  settingWeight d a.1 o.1 * basisProbability theta (settingBasis a.2 o.1) o.2

lemma bornProbability_nonnegative {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1))
    (a : ℕ × Action d) (o : Outcome d) : 0 ≤ bornProbability theta a o :=
  mul_nonneg (settingWeight_nonnegative _ _ _) (basisProbability_nonnegative _ _ _)
lemma bornProbability_sum {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∑ o, bornProbability theta a o = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [bornProbability, ← Finset.mul_sum, basisProbability_sum, mul_one]
  exact settingWeight_sum _ _

def bornMeasure {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) : Measure (Outcome d) :=
  finiteMassMeasure (bornProbability theta a) (bornProbability_nonnegative theta a)
    (bornProbability_sum theta a)
instance bornMeasure_probability {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    IsProbabilityMeasure (bornMeasure theta a) := by unfold bornMeasure; infer_instance

def bornKernel {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) : Kernel (ℕ × Action d) (Outcome d) where
  toFun := bornMeasure theta
  measurable' := by
    apply measurable_from_prod_countable_right
    intro n
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    intro t ht
    trivial
instance bornKernel_isMarkov {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) :
    IsMarkovKernel (bornKernel theta) where
  isProbabilityMeasure a := bornMeasure_probability theta a

lemma regressionFrame_apply {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (n : ℕ) (U : Action d) (x : HermitianSpace (d+1)) :
    regressionFrame n U x = ∑ o : Outcome d,
      (settingWeight d n o.1 * ⟪responseVector U o, x⟫_ℝ) • responseVector U o := by
  simp only [regressionFrame, LinearMap.sum_apply, LinearMap.smul_apply, basisFrame,
    frameOperator_apply, Finset.smul_sum, smul_smul, Fintype.sum_prod_type, responseVector]

lemma responseVector_mean {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, responseVector a.2 o ∂bornKernel theta a = regressionFrame a.1 a.2 theta.1 := by
  change (∫ o, responseVector a.2 o ∂finiteMassMeasure (bornProbability theta a)
    (bornProbability_nonnegative theta a) (bornProbability_sum theta a)) = _
  rw [integral_finiteMassMeasure, regressionFrame_apply]
  rfl

lemma responseVector_bound {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (U : Action d) (o : Outcome d) :
    ‖responseVector U o‖ ≤ basisBound d := basisEffect_bound _ _
lemma regressionFrame_truth_bound {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ‖regressionFrame a.1 a.2 theta.1‖ ≤ basisBound d := by
  rw [regressionFrame_apply]
  change ‖∑ o : Outcome d, bornProbability theta a o • responseVector a.2 o‖ ≤ _
  calc
    _ ≤ ∑ o : Outcome d, ‖bornProbability theta a o • responseVector a.2 o‖ := norm_sum_le _ _
    _ ≤ ∑ o : Outcome d, bornProbability theta a o * basisBound d := by
      apply Finset.sum_le_sum
      intro o _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bornProbability_nonnegative theta a o)]
      exact mul_le_mul_of_nonneg_left (responseVector_bound _ _) (bornProbability_nonnegative theta a o)
    _ = _ := by rw [← Finset.sum_mul, bornProbability_sum, one_mul]
lemma responseInnovation_bound {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) (o : Outcome d) :
    ‖responseVector a.2 o - regressionFrame a.1 a.2 theta.1‖ ≤ 2 * basisBound d := by
  calc
    _ ≤ ‖responseVector a.2 o‖ + ‖regressionFrame a.1 a.2 theta.1‖ := norm_sub_le _ _
    _ ≤ basisBound d + basisBound d := add_le_add (responseVector_bound _ _) (regressionFrame_truth_bound theta a)
    _ = _ := by ring

lemma regressionFrame_nonnegative {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (n : ℕ) (U : Action d) : Coercive (regressionFrame n U) 0 := by
  intro x
  rw [zero_mul, regressionFrame, LinearMap.sum_apply, inner_sum]
  apply Finset.sum_nonneg
  intro b _
  rw [LinearMap.smul_apply, inner_smul_right]
  have h := basisFrame_nonnegative (settingBasis U b) x
  simp only [zero_mul] at h
  exact mul_nonneg (settingWeight_nonnegative _ _ _) h

lemma regressionFrame_decompose {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (n : ℕ) (U : Action d) :
    regressionFrame n U = ((1-epsilon n)/2) • (basisFrame (PVMGeneralGeometry.exploitationChiAction U) + basisFrame (PVMGeneralGeometry.exploitationTauAction U)) +
      epsilon n • PVMGeneralGeometry.explorationFrame d := by
  ext x
  simp only [regressionFrame, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_sum_type, Fintype.sum_bool, settingWeight, settingBasis,
    PVMGeneralGeometry.explorationFrame, frameOperator_apply, Fintype.sum_prod_type, smul_add,
    LinearMap.add_apply, Finset.smul_sum, smul_smul, basisFrame]
  abel

def coercivityConstant (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : ℝ := Classical.choose (PVMGeneralGeometry.explorationFrame_coercive d)
lemma coercivityConstant_pos (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] : 0 < coercivityConstant d :=
  (Classical.choose_spec (PVMGeneralGeometry.explorationFrame_coercive d)).1
lemma regressionFrame_coercive {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (n : ℕ) (U : Action d) :
    Coercive (regressionFrame n U) (coercivityConstant d * epsilon n) := by
  intro x
  have he := (Classical.choose_spec (PVMGeneralGeometry.explorationFrame_coercive d)).2 x
  have hc := basisFrame_nonnegative (PVMGeneralGeometry.exploitationChiAction U) x
  have ht := basisFrame_nonnegative (PVMGeneralGeometry.exploitationTauAction U) x
  simp only [zero_mul] at hc ht
  rw [regressionFrame_decompose, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, LinearMap.add_apply, inner_add_right, inner_smul_right,
    inner_add_right, inner_smul_right]
  have hw : 0 ≤ (1-epsilon n)/2 := div_nonneg (sub_nonneg.mpr (epsilon_le_one n)) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left he (epsilon_nonnegative n)
  change epsilon n * (coercivityConstant d * ‖x‖^2) ≤ _ at hh
  nlinarith [mul_nonneg hw (add_nonneg hc ht)]
end
end QubitOracle.AdaptiveDesign.PVMPilotBorn

-/
