import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Exact variance statement for the implemented estimator

This file defines the conclusion separately from its proof. The proposition
is now proved by `TangentGLS.optimalVariance` and the constructive
`TangentGLS.phasePair_optimalVariance` in `TangentGLSOptimalVariance.lean`.
`TangentGLSOptimalVarianceAudit.lean` audits those actual theorem endpoints.

The coordinates are twice the real and imaginary off-diagonal entries in a
fixed true-state frame. They are not the amplitude coordinates themselves.
`PureAmplitudeChart` proves the exact conversion, and
`PureAmplitudeEndpoints` proves the actual estimator CLTs after conversion.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

def trueFrameCoordinates {d : ℕ} (truth : PureVector d)
    (estimated : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : EuclideanSpace ℝ (TangentIndex d) :=
  (2 : ℝ) • WithLp.toLp 2 (GeneralPOVM.matrixGradient
    ((trueFrame d truth).conjTranspose * (estimated - rankOneDensity truth.val) * trueFrame d truth))

def OptimalVarianceStatement {d : ℕ} {O : Type} [Fintype O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P) (hp : GeneralPOVM.Regular P)
    (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (truth : PureVector d) : Prop :=
  TendstoInDistribution
    (fun (n : ℕ) path => Real.sqrt (n : ℝ) • trueFrameCoordinates truth
      (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n)) atTop id
    (fun _ => adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
    (multivariateGaussian 0 ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)))

end
end QubitOracle.AdaptiveDesign.TangentGLS
