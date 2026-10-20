import QubitOracle.Paper.HistoryDependentPredictableMixture
import QubitOracle.Paper.RankOneStageContinuity

/-!
# Adaptive rank-one information assembly

The setting type consists of the two controller-adapted exploitation bases and
a finite exploration-library index.  This module proves that the equal-basis
exploitation policy has conditional information `rankOneStageInformation`,
then combines stage convergence, vanishing exploration, the actual adaptive
path martingale, and the exact Hall--Heyde conditional-moment strong law.
-/

namespace QubitOracle.Paper

open scoped BigOperators Matrix.Norms.L2Operator
open Filter MeasureTheory

noncomputable section

/-- Two exploitation choices together with a finite exploration library. -/
abbrev RankOneSetting (L : Type*) := Bool ⊕ L

/-- Equal mass on the chi and tau settings, and zero mass on exploration
settings. -/
def rankOneTwoBasisPolicy
    {L Y : Type*} [Fintype L] : AdaptivePolicy (RankOneSetting L) Y where
  mass _ s := match s with
    | Sum.inl _ => 1 / 2
    | Sum.inr _ => 0
  mass_nonneg _ s := by cases s <;> positivity
  sum_mass _ := by
    rw [Fintype.sum_sum_type]
    simp

/-- True fixed-chart Fisher information for every exploitation or exploration
setting selected after a history. -/
def rankOneSettingInformation {n : Nat} {L Y : Type*}
    (F : OracleFrame n)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (TangentIndex n) (TangentIndex n) Real)
    (history : SequentialHistory (RankOneSetting L) Y) :
    RankOneSetting L → Matrix (TangentIndex n) (TangentIndex n) Real
  | Sum.inl false =>
      fixedChartBasisFisher (controllerChiBasis F (controller history))
  | Sum.inl true =>
      fixedChartBasisFisher (controllerTauBasis F (controller history))
  | Sum.inr l => explorationInformation history l

/-- Equal chi/tau policy information is exactly the rank-one stage matrix. -/
theorem rankOneTwoBasisPolicy_meanInformation_eq_stage {n : Nat}
    {L Y : Type*} [Fintype L]
    (F : OracleFrame n)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (TangentIndex n) (TangentIndex n) Real)
    (history : SequentialHistory (RankOneSetting L) Y) :
    historyPolicyMeanInformation rankOneTwoBasisPolicy
        (rankOneSettingInformation F controller explorationInformation) history =
      rankOneStageInformation F (controller history) := by
  unfold historyPolicyMeanInformation rankOneStageInformation
  rw [Fintype.sum_sum_type]
  simp [rankOneTwoBasisPolicy, rankOneSettingInformation]
  ac_rfl

/-- Controller consistency along one path gives convergence of the
exploitation conditional mean. -/
theorem rankOneTwoBasisMean_tendsto {n : Nat}
    {L Y : Type*} [Fintype L]
    (F : OracleFrame n)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (TangentIndex n) (TangentIndex n) Real)
    (omega : ℕ → RankOneSetting L × Y)
    (hunitary : ∀ k, controller
      (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) ∈
        Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : Tendsto
      (fun k => controllerTrueOverlapSq (controller
        (trajectoryPrefixHistory (Preorder.frestrictLe k omega))))
      atTop (nhds 1)) :
    Tendsto
      (fun k => historyPolicyMeanInformation rankOneTwoBasisPolicy
        (rankOneSettingInformation F controller explorationInformation)
        (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
      atTop (nhds ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) := by
  have hstage := rankOneStageInformation_tendsto F
    (fun k => controller
      (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
    hunitary hoverlap
  convert hstage using 1
  funext k
  exact rankOneTwoBasisPolicy_meanInformation_eq_stage
    F controller explorationInformation _

/-- Stage convergence plus vanishing exploration gives the pathwise
predictable information limit. -/
theorem rankOnePathPredictableInformation_tendsto {n : Nat}
    {L Y : Type*} [Fintype L]
    (F : OracleFrame n)
    (epsilon : SequentialHistory (RankOneSetting L) Y → ℝ)
    (explore : AdaptivePolicy (RankOneSetting L) Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (TangentIndex n) (TangentIndex n) Real)
    (omega : ℕ → RankOneSetting L × Y) (C : ℝ)
    (hC : 0 ≤ C)
    (hunitary : ∀ k, controller
      (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) ∈
        Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : Tendsto
      (fun k => controllerTrueOverlapSq (controller
        (trajectoryPrefixHistory (Preorder.frestrictLe k omega))))
      atTop (nhds 1))
    (hdifference : ∀ k,
      ‖historyPolicyMeanInformation explore
          (rankOneSettingInformation F controller explorationInformation)
          (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) -
        historyPolicyMeanInformation rankOneTwoBasisPolicy
          (rankOneSettingInformation F controller explorationInformation)
          (trajectoryPrefixHistory (Preorder.frestrictLe k omega))‖ ≤ C)
    (hschedule : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
        epsilon (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N,
        historyPathPredictableInformation
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one)
          (rankOneSettingInformation F controller explorationInformation)
          k omega)
      atTop (nhds ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) := by
  apply historyPathPredictableInformation_mixture_tendsto
    epsilon rankOneTwoBasisPolicy explore hepsilon_nonneg hepsilon_le_one
    (rankOneSettingInformation F controller explorationInformation)
    omega ((1 / 2 : Real) •
      (1 : Matrix (TangentIndex n) (TangentIndex n) Real)) C hC
  · exact rankOneTwoBasisMean_tendsto
      F controller explorationInformation omega hunitary hoverlap
  · exact hdifference
  · exact hschedule

/-- Rank-one post-initial information convergence under the exact remaining
protocol conditions.  No martingale premise is assumed: it is derived from
the adaptive trajectory law.  The pilot/library verification must discharge
the explicit integrability and Hall--Heyde conditional-moment premises. -/
theorem rankOneTailInformationConvergence_of_protocolConditions {n : Nat}
    {Theta L Y : Type*} [Fintype L] [Fintype Y]
    [MeasurableSpace (RankOneSetting L)]
    [MeasurableSingletonClass (RankOneSetting L)]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace (RankOneSetting L)] [StandardBorelSpace Y]
    [Nonempty (RankOneSetting L)] [Nonempty Y]
    (F : OracleFrame n)
    (epsilon : SequentialHistory (RankOneSetting L) Y → ℝ)
    (explore : AdaptivePolicy (RankOneSetting L) Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (TangentIndex n) (TangentIndex n) Real)
    (p : OutcomeKernel Theta (RankOneSetting L) Y) (theta : Theta)
    (hL2 : ∀ k i j, MemLp
      (fun omega : ℕ → RankOneSetting L × Y =>
        historyPathInformationInnovation
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one)
          (rankOneSettingInformation F controller explorationInformation)
          k omega i j)
      2 (adaptiveTrajectoryMeasure
        (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
          hepsilon_nonneg hepsilon_le_one) p theta))
    (hsummable : ∀ i j,
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        Summable (fun k => hallHeydeWeightedSecondMoment
          (adaptiveTrajectoryMeasure
            (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
              hepsilon_nonneg hepsilon_le_one) p theta)
          MeasureTheory.Filtration.piLE
          (fun k omega => historyPathInformationInnovation
            (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
              hepsilon_nonneg hepsilon_le_one)
            (rankOneSettingInformation F controller explorationInformation)
            k omega i j) k omega))
    (hcontroller :
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        (∀ k, controller
          (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) ∈
            Matrix.unitaryGroup (Fin (n + 1)) Complex) ∧
        Tendsto
          (fun k => controllerTrueOverlapSq (controller
            (trajectoryPrefixHistory (Preorder.frestrictLe k omega))))
          atTop (nhds 1))
    (hdifference :
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
          ‖historyPolicyMeanInformation explore
              (rankOneSettingInformation F controller explorationInformation)
              (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) -
            historyPolicyMeanInformation rankOneTwoBasisPolicy
              (rankOneSettingInformation F controller explorationInformation)
              (trajectoryPrefixHistory (Preorder.frestrictLe k omega))‖ ≤ C)
    (hschedule :
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        Tendsto
          (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
            epsilon (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
          atTop (nhds 0)) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure
        (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
          hepsilon_nonneg hepsilon_le_one) p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N,
          historyPathSelectedInformation
            (rankOneSettingInformation F controller explorationInformation)
            k omega)
        atTop (nhds ((1 / 2 : Real) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) := by
  let q := adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
    hepsilon_nonneg hepsilon_le_one
  let information := rankOneSettingInformation F controller explorationInformation
  have hpredictable : ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N,
          historyPathPredictableInformation q information k omega)
        atTop (nhds ((1 / 2 : Real) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) := by
    filter_upwards [hcontroller, hdifference, hschedule] with omega hc hd hs
    rcases hd with ⟨C, hC, hd⟩
    exact rankOnePathPredictableInformation_tendsto
      F epsilon explore hepsilon_nonneg hepsilon_le_one controller
      explorationInformation omega C hC hc.1 hc.2 hd hs
  exact historyPathSelectedInformationAverage_ae_tendsto_of_conditionalMoments
    q p theta information
    ((1 / 2 : Real) •
      (1 : Matrix (TangentIndex n) (TangentIndex n) Real))
    hL2 hsummable hpredictable

end

end QubitOracle.Paper
