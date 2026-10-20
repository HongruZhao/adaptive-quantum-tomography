import QubitOracle.Paper.QubitRLSCore
import QubitOracle.Paper.ControllerInformationConvergenceLabels
import QubitOracle.Paper.PopularRLSConditions

/-!
# Exact qubit reduction to adaptive recursive least squares

For an axis measurement with outcomes in `{ -1, 1 }`, the Born rule has the
exact conditional mean `u dot theta`.  This is a finite-sample identity and
does not use LAN.  The same regression model covers an arbitrary mixed qubit
and a pure qubit; only the parameter constraint changes.

The statistical RLS confidence theorem is not reproved in this module.
`PopularRLSConditions` records its source-exact assumptions.  The quantum
protocol must construct that condition structure by proving predictability,
the martingale-difference identity, and the conditional sub-Gaussian bound.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Constant term in the affine Born model. -/
def qubitRLSIntercept
    (_u : Fin 3 -> Real) (_y : QubitRLSOutcome) : Real :=
  1 / 2

/-- Feature vector `y u / 2` in the affine Born model. -/
def qubitRLSFeature
    (u : Fin 3 -> Real) (y : QubitRLSOutcome) : Fin 3 -> Real :=
  fun j => qubitRLSOutcomeSign y * u j / 2

/-- The matrix Born rule is exactly the affine model used by the paper's RLS
controller. -/
theorem qubitRLSBornProbability_eq_affine
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome) :
    qubitRLSBornProbability theta u y =
      paperAffineBornProbability
        qubitRLSIntercept qubitRLSFeature theta u y := by
  unfold qubitRLSBornProbability
  rw [qubitBornTrace_eq]
  unfold paperAffineBornProbability qubitRLSIntercept
  have hsum :
      dotProduct (qubitRLSFeature u y) theta =
        qubitRLSOutcomeSign y / 2 * blochDot u theta := by
    unfold dotProduct qubitRLSFeature blochDot
    calc
      (∑ j, (qubitRLSOutcomeSign y * u j / 2) * theta j) =
          ∑ j, (qubitRLSOutcomeSign y / 2) * (u j * theta j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = qubitRLSOutcomeSign y / 2 * ∑ j, u j * theta j := by
            rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- The two affine Born weights sum to one. -/
theorem qubitRLSBornProbability_sum
    (theta u : Fin 3 -> Real) :
    (∑ y : QubitRLSOutcome, qubitRLSBornProbability theta u y) = 1 := by
  simp [qubitRLSBornProbability, qubitRLSOutcomeSign,
    qubitBornTrace_eq] <;> ring

/-- Exact linear conditional mean of the signed outcome. -/
theorem qubitRLSOutcome_mean
    (theta u : Fin 3 -> Real) :
    (∑ y : QubitRLSOutcome,
        qubitRLSBornProbability theta u y * qubitRLSOutcomeSign y) =
      blochDot u theta := by
  simp [qubitRLSBornProbability, qubitRLSOutcomeSign,
    qubitBornTrace_eq] <;> ring

/-- Scalar regression noise for one realized axis outcome. -/
def qubitRLSScalarNoise
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome) : Real :=
  qubitRLSOutcomeSign y - blochDot u theta

/-- The regression noise is centered under the exact Born distribution. -/
theorem qubitRLSScalarNoise_centered
    (theta u : Fin 3 -> Real) :
    (∑ y : QubitRLSOutcome,
        qubitRLSBornProbability theta u y *
          qubitRLSScalarNoise theta u y) = 0 := by
  simp [qubitRLSBornProbability, qubitRLSScalarNoise,
    qubitRLSOutcomeSign, qubitBornTrace_eq] <;> ring

/-- If the physical Born mean lies in `[-1, 1]`, the centered signed outcome
is bounded by two.  Conditional Hoeffding therefore supplies the
sub-Gaussian premise of the cited self-normalized theorem. -/
theorem abs_qubitRLSScalarNoise_le_two
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome)
    (hmean : abs (blochDot u theta) <= 1) :
    abs (qubitRLSScalarNoise theta u y) <= 2 := by
  have hlower : -1 <= blochDot u theta := (abs_le.mp hmean).1
  have hupper : blochDot u theta <= 1 := (abs_le.mp hmean).2
  cases y
  · simp only [qubitRLSScalarNoise, qubitRLSOutcomeSign]
    rw [abs_le]
    constructor <;> linarith
  · simp only [qubitRLSScalarNoise, qubitRLSOutcomeSign]
    rw [abs_le]
    constructor <;> linarith

/-- One axis contributes one half of its ordinary outer-product Gram matrix
under the paper's two-indicator affine encoding. -/
theorem qubitRLSSettingGram_eq
    (u : Fin 3 -> Real) :
    paperSettingGram qubitRLSFeature u =
      (1 / 2 : Real) • Matrix.vecMulVec u u := by
  ext i j
  simp [paperSettingGram, qubitRLSFeature, qubitRLSOutcomeSign,
    Matrix.vecMulVec_apply] <;> ring

/-- Interior mixed-qubit constraint. -/
def IsMixedQubitRLSParameter (theta : Fin 3 -> Real) : Prop :=
  blochNormSq theta < 1

/-- Pure-qubit constraint in the same ambient Bloch coordinates. -/
def IsPureQubitRLSParameter (theta : Fin 3 -> Real) : Prop :=
  blochNormSq theta = 1

/-- A mixed qubit has the exact affine RLS model.  The interior hypothesis is
needed later for regular Fisher information, not for this identity. -/
theorem mixedQubit_exactRLSModel
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome)
    (_h : IsMixedQubitRLSParameter theta) :
    qubitRLSBornProbability theta u y =
        paperAffineBornProbability
          qubitRLSIntercept qubitRLSFeature theta u y ∧
      (∑ z : QubitRLSOutcome,
          qubitRLSBornProbability theta u z * qubitRLSOutcomeSign z) =
        blochDot u theta :=
  ⟨qubitRLSBornProbability_eq_affine theta u y,
    qubitRLSOutcome_mean theta u⟩

/-- A pure qubit has exactly the same affine RLS model.  Purity changes only
the subsequent projection and boundary-regularity argument. -/
theorem pureQubit_exactRLSModel
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome)
    (_h : IsPureQubitRLSParameter theta) :
    qubitRLSBornProbability theta u y =
        paperAffineBornProbability
          qubitRLSIntercept qubitRLSFeature theta u y ∧
      (∑ z : QubitRLSOutcome,
          qubitRLSBornProbability theta u z * qubitRLSOutcomeSign z) =
        blochDot u theta :=
  ⟨qubitRLSBornProbability_eq_affine theta u y,
    qubitRLSOutcome_mean theta u⟩

/-- Window scale displayed in `eq:SI_uniform_controller_tail`. -/
def uniformControllerWindowScale
    (expectedExploration : Nat -> Real) (start : Nat -> Nat)
    (n : Nat) : Real :=
  Real.sqrt
    (Real.log (n : Real) / expectedExploration (start n))

/-- Separate pointwise statistical and deterministic schedule premises for
the uniform controller window.  The displayed uniform conclusion is not a
field of this structure. -/
structure UniformControllerTailPrimitives
    (Omega State : Type*) [NormedAddCommGroup State]
    (controller : Nat -> Omega -> State) (truth : State)
    (expectedExploration : Nat -> Real) where
  start : Nat -> Nat
  badEvent : Nat -> Set Omega
  constant : Real
  constant_nonnegative : 0 <= constant
  pointwise_bound_on_good : forall n omega, omega ∉ badEvent n ->
    forall j, start n <= j -> j <= n ->
      ‖controller j omega - truth‖ <=
        constant * controllerRateScale expectedExploration j
  scale_comparison : forall n j, start n <= j -> j <= n ->
    controllerRateScale expectedExploration j <=
      uniformControllerWindowScale expectedExploration start n

namespace Label

/-- Supplement equation `eq:SI_uniform_controller_tail`, derived from a
pointwise self-normalized controller bound and the deterministic comparison
of exploration scales over the terminal window. -/
theorem eq_SI_uniform_controller_tail
    {Omega State : Type*} [NormedAddCommGroup State]
    (controller : Nat -> Omega -> State) (truth : State)
    (expectedExploration : Nat -> Real)
    (h : UniformControllerTailPrimitives
      Omega State controller truth expectedExploration)
    (n : Nat) (omega : Omega) (hgood : omega ∉ h.badEvent n) :
    forall j, h.start n <= j -> j <= n ->
      ‖controller j omega - truth‖ <=
        h.constant *
          uniformControllerWindowScale expectedExploration h.start n := by
  intro j hj0 hj1
  calc
    ‖controller j omega - truth‖ <=
        h.constant * controllerRateScale expectedExploration j :=
      h.pointwise_bound_on_good n omega hgood j hj0 hj1
    _ <= h.constant *
        uniformControllerWindowScale expectedExploration h.start n :=
      mul_le_mul_of_nonneg_left (h.scale_comparison n j hj0 hj1)
        h.constant_nonnegative

end Label

end

end QubitOracle.Paper
