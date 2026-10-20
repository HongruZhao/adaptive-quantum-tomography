import QubitOracle.Paper.OneQubitPureCyclicPauliCompletion
import QubitOracle.Paper.OneQubitMixedCyclicPauliLAN

open scoped Topology ProbabilityTheory
open Filter MeasureTheory

namespace QubitOracle.Paper

/-- Bundled, axiom-free cyclic-Pauli LAN result for pure and mixed one-qubit states. -/
structure CyclicPauliOneQubitComplete : Prop where
  pure_lan : ∀ h : Fin 2 → ℝ, PureCyclicPauliLAN h
  pure_chart_eventually_valid : ∀ h : Fin 2 → ℝ,
    ∀ᶠ q : ℕ in atTop, PureCyclicPauliLocalChartValid q h
  pure_local_states_eventually_norm_one : ∀ h : Fin 2 → ℝ,
    ∀ᶠ q : ℕ in atTop,
      pureCyclicPauliBlochNormSq (pureCyclicPauliLocalBloch q h) = 1
  mixed_lan : ∀ theta h : RLSVector 3,
    ∀ hInterior : MixedCyclicPauliStrictInterior theta,
      MixedCyclicPauliLAN theta h hInterior
  mixed_local_states_eventually_physical : ∀ theta h : RLSVector 3,
    MixedCyclicPauliStrictInterior theta →
      ∀ᶠ q : ℕ in atTop,
        MixedCyclicPauliStrictInterior (mixedCyclicPauliLocalBloch theta h q)
  mixed_information_strong_law : ∀ theta h : RLSVector 3,
    ∀ hInterior : MixedCyclicPauliStrictInterior theta,
      ∀ᵐ omega ∂mixedCyclicPauliMeasure theta,
        Tendsto (fun q => mixedCyclicPauliObservedInformation theta h q omega)
          atTop (𝓝 (mixedCyclicPauliFisherQuadratic theta h))
  mixed_information_in_measure : ∀ theta h : RLSVector 3,
    ∀ hInterior : MixedCyclicPauliStrictInterior theta,
      TendstoInMeasure (mixedCyclicPauliMeasure theta)
        (mixedCyclicPauliObservedInformation theta h) atTop
        (fun _ => mixedCyclicPauliFisherQuadratic theta h)
  mixed_fisher_formula : ∀ theta h : RLSVector 3,
    MixedCyclicPauliStrictInterior theta →
      mixedCyclicPauliFisherQuadratic theta h =
        (1 / 3 : ℝ) *
          (h 0 ^ 2 / (1 - theta 0 ^ 2) +
           h 1 ^ 2 / (1 - theta 1 ^ 2) +
           h 2 ^ 2 / (1 - theta 2 ^ 2))
  mixed_exact_likelihood_expansion : ∀ theta h : RLSVector 3,
    ∀ q omega,
      mixedCyclicPauliLogLikelihoodRatio theta h q omega =
        mixedCyclicPauliNormalizedScore theta h q omega -
          mixedCyclicPauliFisherQuadratic theta h / 2 +
        mixedCyclicPauliLANRemainder theta h q omega

/-- Main exact endpoint for cyclic Pauli tomography of one pure or mixed qubit. -/
theorem cyclicPauliOneQubit_complete : CyclicPauliOneQubitComplete where
  pure_lan := pureCyclicPauli_LAN
  pure_chart_eventually_valid := pureCyclicPauliLocalChart_eventually_valid
  pure_local_states_eventually_norm_one :=
    pureCyclicPauliLocalBloch_eventually_normSq_one
  mixed_lan := mixedCyclicPauli_LAN
  mixed_local_states_eventually_physical :=
    mixedCyclicPauliLocalBloch_eventually_strictInterior
  mixed_information_strong_law :=
    mixedCyclicPauliObservedInformation_tendsto_ae
  mixed_information_in_measure :=
    mixedCyclicPauliObservedInformation_tendstoInMeasure
  mixed_fisher_formula := mixedCyclicPauliFisherQuadratic_eq
  mixed_exact_likelihood_expansion :=
    mixedCyclicPauliLogLikelihoodRatio_exact_LAN

end QubitOracle.Paper
