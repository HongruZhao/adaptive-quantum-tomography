import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn

/-! # Adaptive phase-paired tomography, without a Fisher-symmetry input

The actual labelled Born experiment, all-observation ridge estimator,
nearest-pure estimate, and prescribed positive batches are inherited from
the general convergence engine. The necessary reference identity is supplied
by the proved phase-pair lemma, not by a user hypothesis.
This file makes no estimator CLT or efficiency claim.
-/
namespace QubitOracle.AdaptiveDesign.PhasePair
open QubitOracle QubitOracle.Paper GeneralPOVM PureMatrixController P2Adaptive
open Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
  (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
  (hp : Regular P) (hR : RankOne P)
  (regularization : ℝ) (hregularization : 0 < regularization)

include hp hR

/-- Main P2 phase-pair endpoint: every fixed finite dimension, arbitrary
positive finite batches, and no assumed stochastic limit or Fisher identity. -/
theorem adaptive_actualBorn_information
    (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol (paired P) (paired_identifying P hI)
        regularization hregularization batchSize) truth,
      Tendsto (GeneralPOVM.rawEstimator (paired P) (paired_identifying P hI)
        regularization hregularization batchSize path) atTop
        (𝓝 (pureParameter d truth).1) ∧
      Tendsto (GeneralPOVM.stateEstimator (paired P) (paired_identifying P hI)
        regularization hregularization batchSize path) atTop
        (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun n => actualBornFisher (paired P) truth
        (GeneralPOVM.actualState (paired P) (paired_identifying P hI)
          regularization hregularization batchSize path n).action) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        actualBornFisher (paired P) truth
          (GeneralPOVM.actualState (paired P) (paired_identifying P hI)
            regularization hregularization batchSize path n).action x y) atTop
        (𝓝 (((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) :=
  GeneralPOVM.adaptive_actualBorn_information (paired P) (paired_identifying P hI)
    regularization hregularization (paired_regular P hp) (paired_fisher_of_rankOne P hp hR)
    truth batchSize hpositive

end
end QubitOracle.AdaptiveDesign.PhasePair
