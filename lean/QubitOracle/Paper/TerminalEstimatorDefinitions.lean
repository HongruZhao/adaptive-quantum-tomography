import QubitOracle.Paper.PaperProtocolDefinitions
import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.RankOneLosses

/-!
# Exact terminal-estimator definitions used by the paper

The terminal statistics are functions of an infinite recorded path and the
already verified retained-tail set.  Mixed-qubit increments use the concrete
binary-axis score.  Rank-one likelihoods use the existing normalized tangent
coordinates and exact finite-dimensional Born amplitude.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-! ## Retained generic score/Hessian API -/

/-- A retained sum of the existing certified finite-model log scores. -/
def retainedModelScore
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (n : Nat) (exploration : Nat -> Nat)
    (path : Nat -> M × Y) : D -> Real :=
  ∑ i ∈ terminalTailSet n exploration,
    model.logScore theta (path i).1 (path i).2

/-- A retained sum of the existing certified observed-information matrices. -/
def retainedModelObservedInformation
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (n : Nat) (exploration : Nat -> Nat)
    (path : Nat -> M × Y) : Matrix D D Real :=
  ∑ i ∈ terminalTailSet n exploration,
    model.observedInformation theta (path i).1 (path i).2

/-! ## Mixed-qubit terminal statistics -/

/-- Numerical value of a binary outcome: `true = +1`, `false = -1`. -/
def binaryOutcomeSign : Bool -> Real
  | true => 1
  | false => -1

/-- The concrete mixed-qubit score increment `Y U / (1 + Y U^T a)`. -/
def mixedTerminalScoreIncrement
    (a u : Fin 3 -> Real) (y : Bool) : Fin 3 -> Real :=
  fun j =>
    binaryOutcomeSign y * u j /
      (1 + binaryOutcomeSign y * QubitOracle.blochDot u a)

/-- The concrete observed-information increment
`U U^T / (1 + Y U^T a)^2`. -/
def mixedTerminalHessianIncrement
    (a u : Fin 3 -> Real) (y : Bool) : Matrix (Fin 3) (Fin 3) Real :=
  ((1 + binaryOutcomeSign y * QubitOracle.blochDot u a) ^ 2)⁻¹ •
    Matrix.vecMulVec u u

/-- Retained mixed-qubit score on an actual setting/outcome path. -/
def mixedRetainedScore
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) : Fin 3 -> Real :=
  ∑ i ∈ terminalTailSet n exploration,
    mixedTerminalScoreIncrement a (axis (path i).1) (path i).2

/-- Retained mixed-qubit observed information on the same path. -/
def mixedRetainedObservedInformation
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  ∑ i ∈ terminalTailSet n exploration,
    mixedTerminalHessianIncrement a (axis (path i).1) (path i).2

/-- Unprojected mixed-qubit Newton estimator. -/
def mixedOneStepEstimator
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (controller : Fin 3 -> Real) : Fin 3 -> Real :=
  controller +
    ((mixedRetainedObservedInformation n exploration axis path controller)⁻¹).mulVec
      (mixedRetainedScore n exploration axis path controller)

/-- Euclidean norm in Bloch coordinates. -/
def blochEuclideanNorm (v : Fin 3 -> Real) : Real :=
  Real.sqrt (QubitOracle.blochNormSq v)

/-- The compact mixed local-MLE search set. -/
def mixedLocalMLESet
    (controller : Fin 3 -> Real) (radius eta : Real) : Set (Fin 3 -> Real) :=
  {a | blochEuclideanNorm (a - controller) <= radius ∧
    blochEuclideanNorm a <= 1 - eta}

/-! ## Rank-one chart and likelihood -/

/-- The complex tangent vector `E_a (h_R + i h_I)`. -/
def rankOneTangentVector {n : Nat}
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) : Fin (n + 1) -> Complex :=
  fun i => ∑ j : Fin n,
    complement j i *
      (⟨h (Sum.inl j), h (Sum.inr j)⟩ : Complex)

/-- The normalized local chart centered at the controller state. -/
def rankOneControllerChart {n : Nat}
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) : Fin (n + 1) -> Complex :=
  fun i =>
    (Real.sqrt (1 - QubitOracle.tangentRadiusSq h / 4) : Complex) * a i +
      (1 / 2 : Complex) * rankOneTangentVector complement h i

/-- Retained rank-one log likelihood in the controller chart. -/
def rankOneRetainedLogLikelihood {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) : Real :=
  ∑ i ∈ terminalTailSet sampleSize exploration,
    Real.log (basisBornProbability
      (fun j => basis i j (outcome i))
      (rankOneControllerChart a complement h))

/-- Coordinate unit direction in a finite real chart. -/
def coordinateDirection {D : Type*} [DecidableEq D]
    (j : D) : D -> Real :=
  fun k => if k = j then 1 else 0

/-- Coordinate gradient defined through the Frechet derivative. -/
def coordinateGradient {D : Type*} [Fintype D] [DecidableEq D]
    (f : (D -> Real) -> Real) (x : D -> Real) : D -> Real :=
  fun j => (fderiv Real f x) (coordinateDirection j)

/-- Negative coordinate Hessian defined by differentiating the gradient. -/
def negativeCoordinateHessian {D : Type*} [Fintype D] [DecidableEq D]
    (f : (D -> Real) -> Real) (x : D -> Real) : Matrix D D Real :=
  fun j k =>
    -(fderiv Real (fun z => coordinateGradient f z k) x)
      (coordinateDirection j)

/-- Rank-one retained score at the controller-chart origin. -/
def rankOneRetainedScore {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    QubitOracle.TangentIndex n -> Real :=
  coordinateGradient
    (rankOneRetainedLogLikelihood sampleSize exploration basis outcome a complement)
    0

/-- Rank-one retained observed information at the chart origin. -/
def rankOneRetainedObservedInformation {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    Matrix (QubitOracle.TangentIndex n) (QubitOracle.TangentIndex n) Real :=
  negativeCoordinateHessian
    (rankOneRetainedLogLikelihood sampleSize exploration basis outcome a complement)
    0

/-- Unprojected rank-one Newton correction in the controller chart. -/
def rankOneOneStepEstimator {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    Fin (n + 1) -> Complex :=
  rankOneControllerChart a complement
    (((rankOneRetainedObservedInformation sampleSize exploration basis outcome a complement)⁻¹).mulVec
      (rankOneRetainedScore sampleSize exploration basis outcome a complement))

/-- One observed rank-one log likelihood in a fixed true chart. -/
def rankOneShotLogLikelihood {n : Nat}
    (basis : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Fin (n + 1)) (psi : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) : Real :=
  Real.log (basisBornProbability (fun j => basis j outcome)
    (rankOneControllerChart psi complement h))

/-- One fixed-chart rank-one score increment. -/
def rankOneShotScore {n : Nat}
    (basis : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Fin (n + 1)) (psi : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    QubitOracle.TangentIndex n -> Real :=
  coordinateGradient (rankOneShotLogLikelihood basis outcome psi complement) 0

/-- One fixed-chart rank-one observed-information increment. -/
def rankOneShotObservedInformation {n : Nat}
    (basis : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Fin (n + 1)) (psi : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    Matrix (QubitOracle.TangentIndex n) (QubitOracle.TangentIndex n) Real :=
  negativeCoordinateHessian
    (rankOneShotLogLikelihood basis outcome psi complement) 0

/-- Moving controller chart written in fixed true-chart coordinates. -/
def movingRankOneChartMap {n : Nat}
    (inverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (controller : Nat -> Fin (n + 1) -> Complex)
    (complement : Nat -> Fin n -> Fin (n + 1) -> Complex)
    (stage : Nat) :
    (QubitOracle.TangentIndex n -> Real) ->
      (QubitOracle.TangentIndex n -> Real) :=
  fun k => inverseTrueChart
    (rankOneControllerChart (controller stage) (complement stage) k)

/-- Derivative `A_n = D phi_n(0)` of the moving chart. -/
def movingRankOneChartDerivative {n : Nat}
    (inverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (controller : Nat -> Fin (n + 1) -> Complex)
    (complement : Nat -> Fin n -> Fin (n + 1) -> Complex)
    (stage : Nat) :
    (QubitOracle.TangentIndex n -> Real) →L[Real]
      (QubitOracle.TangentIndex n -> Real) :=
  fderiv Real
    (movingRankOneChartMap inverseTrueChart controller complement stage) 0

/-- Fixed-true-chart error of a rank-one terminal estimate. -/
def rankOneTerminalError {n : Nat}
    (inverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (estimate : Nat -> Fin (n + 1) -> Complex) (stage : Nat) :
    QubitOracle.TangentIndex n -> Real :=
  inverseTrueChart (estimate stage)

/-! ## Events and normalized terminal errors -/

/-- Intersection of the four regular-event components in Supplementary Note 9. -/
def terminalGoodEvent {Omega : Type*}
    (controller regular score hessian : Set Omega) : Set Omega :=
  controller ∩ regular ∩ score ∩ hessian

/-- Root-sample-size mixed-coordinate error. -/
def mixedNormalizedError
    (estimate : Nat -> Fin 3 -> Real) (thetaStar : Fin 3 -> Real)
    (n : Nat) : Fin 3 -> Real :=
  Real.sqrt (n : Real) • (estimate n - thetaStar)

/-- Root-sample-size bounded fixed-chart rank-one error. -/
def rankOneNormalizedError {n : Nat}
    (extendedInverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (estimate : Nat -> Fin (n + 1) -> Complex) (sampleSize : Nat) :
    QubitOracle.TangentIndex n -> Real :=
  Real.sqrt (sampleSize : Real) • extendedInverseTrueChart (estimate sampleSize)

namespace Label

/-- Main-text equation `eq:mixed_score_method`. -/
theorem eq_mixed_score_method
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) :
    mixedRetainedScore n exploration axis path a =
      ∑ i ∈ terminalTailSet n exploration,
        fun j => binaryOutcomeSign (path i).2 * axis (path i).1 j /
          (1 + binaryOutcomeSign (path i).2 *
            QubitOracle.blochDot (axis (path i).1) a) :=
  rfl

/-- Main-text equation `eq:mixed_hessian_method`. -/
theorem eq_mixed_hessian_method
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) :
    mixedRetainedObservedInformation n exploration axis path a =
      ∑ i ∈ terminalTailSet n exploration,
        ((1 + binaryOutcomeSign (path i).2 *
          QubitOracle.blochDot (axis (path i).1) a) ^ 2)⁻¹ •
          Matrix.vecMulVec (axis (path i).1) (axis (path i).1) :=
  rfl

/-- Main-text equation `eq:mixed_one_step`. -/
theorem eq_mixed_one_step
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (controller : Fin 3 -> Real) :
    mixedOneStepEstimator n exploration axis path controller =
      controller +
        ((mixedRetainedObservedInformation n exploration axis path controller)⁻¹).mulVec
          (mixedRetainedScore n exploration axis path controller) :=
  rfl

/-- Main-text equation `eq:r1_controller_chart`. -/
theorem eq_r1_controller_chart {n : Nat}
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) :
    rankOneControllerChart a complement h =
      fun i =>
        (Real.sqrt (1 - QubitOracle.tangentRadiusSq h / 4) : Complex) * a i +
          (1 / 2 : Complex) *
            (∑ j : Fin n, complement j i *
              (⟨h (Sum.inl j), h (Sum.inr j)⟩ : Complex)) :=
  rfl

/-- Main-text equation `eq:r1_local_loglik`. -/
theorem eq_r1_local_loglik {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) :
    rankOneRetainedLogLikelihood sampleSize exploration basis outcome a complement h =
      ∑ i ∈ terminalTailSet sampleSize exploration,
        Real.log (basisBornProbability
          (fun j => basis i j (outcome i))
          (rankOneControllerChart a complement h)) :=
  rfl

/-- Main-text equation `eq:r1_score_hessian_method`. -/
theorem eq_r1_score_hessian_method {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    rankOneRetainedScore sampleSize exploration basis outcome a complement =
        coordinateGradient
          (rankOneRetainedLogLikelihood sampleSize exploration basis outcome a complement) 0 ∧
      rankOneRetainedObservedInformation sampleSize exploration basis outcome a complement =
        negativeCoordinateHessian
          (rankOneRetainedLogLikelihood sampleSize exploration basis outcome a complement) 0 := by
  constructor <;> rfl

/-- Main-text equation `eq:r1_one_step`. -/
theorem eq_r1_one_step {n : Nat}
    (sampleSize : Nat) (exploration : Nat -> Nat)
    (basis : Nat -> Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Nat -> Fin (n + 1))
    (a : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    rankOneOneStepEstimator sampleSize exploration basis outcome a complement =
      rankOneControllerChart a complement
        (((rankOneRetainedObservedInformation sampleSize exploration basis outcome a complement)⁻¹).mulVec
          (rankOneRetainedScore sampleSize exploration basis outcome a complement)) :=
  rfl

/-- Main-text equation `eq:mixed_local_mle_set`. -/
theorem eq_mixed_local_mle_set
    (controller : Fin 3 -> Real) (radius eta : Real) :
    mixedLocalMLESet controller radius eta =
      {a | blochEuclideanNorm (a - controller) <= radius ∧
        blochEuclideanNorm a <= 1 - eta} :=
  rfl

/-- Supplement equation `eq:SI_mixed_score`. -/
theorem eq_SI_mixed_score
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) :
    mixedRetainedScore n exploration axis path a =
      ∑ i ∈ terminalTailSet n exploration,
        fun j => binaryOutcomeSign (path i).2 * axis (path i).1 j /
          (1 + binaryOutcomeSign (path i).2 *
            QubitOracle.blochDot (axis (path i).1) a) :=
  rfl

/-- Supplement equation `eq:SI_mixed_hessian`. -/
theorem eq_SI_mixed_hessian
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (a : Fin 3 -> Real) :
    mixedRetainedObservedInformation n exploration axis path a =
      ∑ i ∈ terminalTailSet n exploration,
        ((1 + binaryOutcomeSign (path i).2 *
          QubitOracle.blochDot (axis (path i).1) a) ^ 2)⁻¹ •
          Matrix.vecMulVec (axis (path i).1) (axis (path i).1) :=
  rfl

/-- Supplement equation `eq:SI_mixed_OS`. -/
theorem eq_SI_mixed_OS
    {M : Type*} (n : Nat) (exploration : Nat -> Nat)
    (axis : M -> Fin 3 -> Real) (path : Nat -> M × Bool)
    (controller : Fin 3 -> Real) :
    mixedOneStepEstimator n exploration axis path controller =
      controller +
        ((mixedRetainedObservedInformation n exploration axis path controller)⁻¹).mulVec
          (mixedRetainedScore n exploration axis path controller) :=
  rfl

/-- Supplement equation `eq:SI_true_r1_loglik`. -/
theorem eq_SI_true_r1_loglik {n : Nat}
    (basis : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Fin (n + 1)) (psiStar : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex)
    (h : QubitOracle.TangentIndex n -> Real) :
    rankOneShotLogLikelihood basis outcome psiStar complement h =
      Real.log (basisBornProbability (fun j => basis j outcome)
        (rankOneControllerChart psiStar complement h)) :=
  rfl

/-- Supplement equation `eq:SI_r1_score_increment`. -/
theorem eq_SI_r1_score_increment {n : Nat}
    (basis : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (outcome : Fin (n + 1)) (psiStar : Fin (n + 1) -> Complex)
    (complement : Fin n -> Fin (n + 1) -> Complex) :
    rankOneShotScore basis outcome psiStar complement =
        coordinateGradient
          (rankOneShotLogLikelihood basis outcome psiStar complement) 0 ∧
      rankOneShotObservedInformation basis outcome psiStar complement =
        negativeCoordinateHessian
          (rankOneShotLogLikelihood basis outcome psiStar complement) 0 := by
  constructor <;> rfl

/-- Supplement equation `eq:SI_chart_definition`. -/
theorem eq_SI_chart_definition {n : Nat}
    (inverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (controller : Nat -> Fin (n + 1) -> Complex)
    (complement : Nat -> Fin n -> Fin (n + 1) -> Complex)
    (stage : Nat) (k : QubitOracle.TangentIndex n -> Real) :
    movingRankOneChartMap inverseTrueChart controller complement stage k =
        inverseTrueChart
          (rankOneControllerChart (controller stage) (complement stage) k) ∧
      movingRankOneChartDerivative inverseTrueChart controller complement stage =
        fderiv Real
          (movingRankOneChartMap inverseTrueChart controller complement stage) 0 := by
  constructor <;> rfl

/-- Supplement equation `eq:SI_r1_terminal_error`. -/
theorem eq_SI_r1_terminal_error {n : Nat}
    (inverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (estimate : Nat -> Fin (n + 1) -> Complex) (stage : Nat) :
    rankOneTerminalError inverseTrueChart estimate stage =
      inverseTrueChart (estimate stage) :=
  rfl

/-- Supplement equation `eq:SI_good_event_decomposition`. -/
theorem eq_SI_good_event_decomposition {Omega : Type*}
    (controller regular score hessian : Set Omega) :
    terminalGoodEvent controller regular score hessian =
      controller ∩ regular ∩ score ∩ hessian :=
  rfl

/-- Supplement equation `eq:SI_normalized_errors`. -/
theorem eq_SI_normalized_errors {n : Nat}
    (mixedEstimate : Nat -> Fin 3 -> Real)
    (thetaStar : Fin 3 -> Real)
    (extendedInverseTrueChart : (Fin (n + 1) -> Complex) ->
      (QubitOracle.TangentIndex n -> Real))
    (rankOneEstimate : Nat -> Fin (n + 1) -> Complex)
    (sampleSize : Nat) :
    mixedNormalizedError mixedEstimate thetaStar sampleSize =
        Real.sqrt (sampleSize : Real) •
          (mixedEstimate sampleSize - thetaStar) ∧
      rankOneNormalizedError extendedInverseTrueChart rankOneEstimate sampleSize =
        Real.sqrt (sampleSize : Real) •
          extendedInverseTrueChart (rankOneEstimate sampleSize) := by
  constructor <;> rfl

end Label

end

end QubitOracle.Paper
