import QubitOracle.Paper.RankOneAdaptiveInformation
import QubitOracle.Paper.InformationInnovationBounds

open scoped Matrix.Norms.L2Operator

namespace QubitOracle.Paper

noncomputable section

/-- Rank-one observed-information convergence with the analytic martingale
hypotheses discharged from one uniform bound on the actual per-setting
information matrices.  In particular, callers no longer provide integrability
or Hall--Heyde conditional-moment summability separately. -/
theorem rankOneTailInformationConvergence_of_uniformInformationBound
    {n : ℕ} {Theta L Y : Type*}
    [Fintype L] [Fintype Y]
    [MeasurableSpace (RankOneSetting L)]
    [MeasurableSingletonClass (RankOneSetting L)]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace (RankOneSetting L)] [StandardBorelSpace Y]
    [Nonempty (RankOneSetting L)] [Nonempty Y]
    (F : QubitOracle.OracleFrame n)
    (epsilon : SequentialHistory (RankOneSetting L) Y → ℝ)
    (explore : AdaptivePolicy (RankOneSetting L) Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (controller : SequentialHistory (RankOneSetting L) Y →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (explorationInformation : SequentialHistory (RankOneSetting L) Y →
      L → Matrix (QubitOracle.TangentIndex n) (QubitOracle.TangentIndex n) ℝ)
    (p : OutcomeKernel Theta (RankOneSetting L) Y) (theta : Theta)
    (hInformationBound : ∃ B, 0 ≤ B ∧
      ∀ history setting i j,
        ‖rankOneSettingInformation F controller explorationInformation
          history setting i j‖ ≤ B)
    (hcontroller :
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        (∀ k, controller
            (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) ∈
              Matrix.unitaryGroup (Fin (n + 1)) ℂ) ∧
        Filter.Tendsto
          (fun k => controllerTrueOverlapSq
            (controller (trajectoryPrefixHistory (Preorder.frestrictLe k omega))))
          Filter.atTop (nhds 1))
    (hdifference :
      ∀ᵐ omega ∂adaptiveTrajectoryMeasure
          (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
            hepsilon_nonneg hepsilon_le_one) p theta,
        ∃ C, 0 ≤ C ∧ ∀ k,
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
        Filter.Tendsto
          (fun (N : ℕ) => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
            epsilon (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
          Filter.atTop (nhds 0)) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure
        (adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
          hepsilon_nonneg hepsilon_le_one) p theta,
      Filter.Tendsto
        (fun (N : ℕ) => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N,
          historyPathSelectedInformation
            (rankOneSettingInformation F controller explorationInformation) k omega)
        Filter.atTop (nhds ((1 / 2 : ℝ) • (1 : Matrix
          (QubitOracle.TangentIndex n) (QubitOracle.TangentIndex n) ℝ))) := by
  let q := adaptivePolicyMixture epsilon rankOneTwoBasisPolicy explore
    hepsilon_nonneg hepsilon_le_one
  let information := rankOneSettingInformation F controller explorationInformation
  have hInnovationBound : ∃ C, 0 ≤ C ∧ ∀ history setting i j,
      ‖historyInformationInnovation q information history setting i j‖ ≤ C :=
    historyInformationInnovation_uniformBound_of_informationBound
      q information hInformationBound
  have hPredictable :=
    Filter.mp_mem hschedule
      (Filter.mp_mem hdifference
        (Filter.mp_mem hcontroller
          (Filter.univ_mem'
            (id fun omega hc hd hs =>
              Exists.casesOn hd fun C h =>
                And.casesOn h fun hC hd =>
                  rankOnePathPredictableInformation_tendsto
                    F epsilon explore hepsilon_nonneg hepsilon_le_one
                    controller explorationInformation omega C hC
                    hc.1 hc.2 hd hs))))
  exact historyPathSelectedInformationAverage_ae_tendsto_of_uniform_bound
    q p theta information ((1 / 2 : ℝ) • (1 : Matrix
      (QubitOracle.TangentIndex n) (QubitOracle.TangentIndex n) ℝ))
    hInnovationBound hPredictable

end

end QubitOracle.Paper
