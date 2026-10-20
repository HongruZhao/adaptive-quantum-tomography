import QubitOracle.Paper.CyclicPauliOneQubitComplete

/-!
# Local asymptotic minimax transfer for cyclic Pauli tomography of one qubit

This file contains the one-qubit-only bridge from the kernel-proved cyclic
Pauli LAN theorems to local asymptotic minimax lower bounds.

The sole scientific axiom is a source-faithful specialization of Rudolf
Beran, "The Role of Hajek's Convolution Theorem in Statistical Theory",
Kybernetika 31 (1995), Theorem 4.1.  It transfers LAN with deterministic
nonsingular information to the all-estimator local minimax lower bound for a
symmetric, continuous, subconvex loss.  Everything else in this file is
ordinary Lean proof: finite Born laws, risk functionals, loss conditions,
Fisher/covariance algebra, and the pure and mixed cyclic specializations.

The theorem is used only for lower bounds.  No equality claim for unbounded
quadratic loss is imported.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace QubitOracle.Paper

noncomputable section

open OneQubitPureLinearEstimatorRisk

/-! ## Losses covered by the cited theorem -/

/-- Squared Euclidean norm in finite coordinates. -/
def cyclicPauliNormSq
    {D : Type*} [Fintype D] (x : D -> Real) : Real :=
  ∑ i, x i ^ 2

/-- A finite sum of squared linear functionals.  This representation includes
all positive-semidefinite quadratic losses needed below. -/
structure CyclicPauliSquareLoss
    (D : Type*) [Fintype D] where
  featureCount : Nat
  coefficient : Fin featureCount -> D -> Real

/-- Value of a represented quadratic loss. -/
def cyclicPauliSquareLossValue
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) (x : D -> Real) : Real :=
  ∑ a : Fin L.featureCount, (∑ i, L.coefficient a i * x i) ^ 2

/-- The stronger Jensen-convex condition used to certify Beran's subconvex
loss hypothesis. -/
def CyclicPauliSubconvex
    {D : Type*} [Fintype D] (w : (D -> Real) -> Real) : Prop :=
  forall (x y : D -> Real) (t : Real), 0 <= t -> t <= 1 ->
    w (fun i => t * x i + (1 - t) * y i) <=
      t * w x + (1 - t) * w y

/-- Machine-readable loss assumptions in Beran (1995), Theorem 4.1. -/
structure Beran1995LossConditions
    {D : Type*} [Fintype D] (w : (D -> Real) -> Real) : Prop where
  nonnegative : forall x, 0 <= w x
  symmetric : forall x, w (-x) = w x
  continuous : Continuous w
  subconvex : CyclicPauliSubconvex w

theorem cyclicPauliSquareLossValue_nonnegative
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) (x : D -> Real) :
    0 <= cyclicPauliSquareLossValue L x := by
  unfold cyclicPauliSquareLossValue
  positivity

theorem cyclicPauliSquareLossValue_symmetric
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) (x : D -> Real) :
    cyclicPauliSquareLossValue L (-x) =
      cyclicPauliSquareLossValue L x := by
  unfold cyclicPauliSquareLossValue
  apply Finset.sum_congr rfl
  intro a _ha
  have hlinear :
      (∑ i, L.coefficient a i * (-x) i) =
        -(∑ i, L.coefficient a i * x i) := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [hlinear]
  ring

theorem cyclicPauliSquareLossValue_continuous
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) :
    Continuous (cyclicPauliSquareLossValue L) := by
  unfold cyclicPauliSquareLossValue
  fun_prop

theorem cyclicPauliSquareLossValue_subconvex
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) :
    CyclicPauliSubconvex (cyclicPauliSquareLossValue L) := by
  intro x y t ht0 ht1
  unfold cyclicPauliSquareLossValue
  calc
    (∑ a : Fin L.featureCount,
        (∑ i, L.coefficient a i *
          (t * x i + (1 - t) * y i)) ^ 2) <=
      ∑ a : Fin L.featureCount,
        (t * (∑ i, L.coefficient a i * x i) ^ 2 +
          (1 - t) * (∑ i, L.coefficient a i * y i) ^ 2) := by
        apply Finset.sum_le_sum
        intro a _ha
        have hlinear :
            (∑ i, L.coefficient a i *
              (t * x i + (1 - t) * y i)) =
              t * (∑ i, L.coefficient a i * x i) +
                (1 - t) * (∑ i, L.coefficient a i * y i) := by
          rw [show (∑ i, L.coefficient a i *
              (t * x i + (1 - t) * y i)) =
              (∑ i, t * (L.coefficient a i * x i)) +
                ∑ i, (1 - t) * (L.coefficient a i * y i) by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            ring]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [hlinear]
        have hgap :
            0 <= t * (1 - t) *
              ((∑ i, L.coefficient a i * x i) -
                (∑ i, L.coefficient a i * y i)) ^ 2 :=
          mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg _)
        nlinarith
    _ = t * (∑ a : Fin L.featureCount,
          (∑ i, L.coefficient a i * x i) ^ 2) +
        (1 - t) * (∑ a : Fin L.featureCount,
          (∑ i, L.coefficient a i * y i) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Every finite square loss satisfies Beran's loss assumptions. -/
theorem cyclicPauliSquareLoss_beranConditions
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) :
    Beran1995LossConditions (cyclicPauliSquareLossValue L) where
  nonnegative := cyclicPauliSquareLossValue_nonnegative L
  symmetric := cyclicPauliSquareLossValue_symmetric L
  continuous := cyclicPauliSquareLossValue_continuous L
  subconvex := cyclicPauliSquareLossValue_subconvex L

/-- Gaussian expectation of a finite square loss, evaluated from the
covariance matrix. -/
def cyclicPauliGaussianSquareBenchmark
    {D : Type*} [Fintype D]
    (L : CyclicPauliSquareLoss D) (covariance : Matrix D D Real) : Real :=
  ∑ a : Fin L.featureCount,
    ∑ i, ∑ j,
      L.coefficient a i * L.coefficient a j * covariance i j

/-- Euclidean squared loss as a finite square loss. -/
def cyclicPauliEuclideanSquareLoss
    (d : Nat) : CyclicPauliSquareLoss (Fin d) where
  featureCount := d
  coefficient := fun a i => if a = i then 1 else 0

theorem cyclicPauliEuclideanSquareLoss_value
    (d : Nat) (x : Fin d -> Real) :
    cyclicPauliSquareLossValue (cyclicPauliEuclideanSquareLoss d) x =
      cyclicPauliNormSq x := by
  simp [cyclicPauliSquareLossValue, cyclicPauliEuclideanSquareLoss,
    cyclicPauliNormSq] <;> rfl

/-! ## Exact finite pure-state local experiment -/

theorem pureCyclicPauliLocalTilt_sq_le_one
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h) (axis : Fin 2) :
    pureCyclicPauliLocalTilt q h axis ^ 2 <= 1 := by
  fin_cases axis
  · change pureCyclicPauliLocalTilt q h 0 ^ 2 <= 1
    nlinarith [hvalid.2,
      sq_nonneg (pureCyclicPauliLocalTilt q h 1)]
  · change pureCyclicPauliLocalTilt q h 1 ^ 2 <= 1
    nlinarith [hvalid.2,
      sq_nonneg (pureCyclicPauliLocalTilt q h 0)]

theorem pureCyclicPauliLocalTilt_abs_le_one
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h) (axis : Fin 2) :
    |pureCyclicPauliLocalTilt q h axis| <= 1 := by
  rw [abs_le]
  have hsquare := pureCyclicPauliLocalTilt_sq_le_one hvalid axis
  constructor <;> nlinarith

theorem pureCyclicPauliLocalBornProbability_nonnegative
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h)
    (axis : Fin 2) (outcome : Bool) :
    0 <= pureCyclicPauliLocalBornProbability q h axis outcome := by
  have habs := pureCyclicPauliLocalTilt_abs_le_one hvalid axis
  have hb := abs_le.mp habs
  cases outcome <;>
    simp [pureCyclicPauliLocalBornProbability] <;> linarith

theorem pureCyclicPauliLocalBornProbability_sum_one
    (q : Nat) (h : Fin 2 -> Real) (axis : Fin 2) :
    pureCyclicPauliLocalBornProbability q h axis false +
      pureCyclicPauliLocalBornProbability q h axis true = 1 := by
  simp [pureCyclicPauliLocalBornProbability]
  ring

/-- One tilted tangent-Pauli outcome law. -/
def pureCyclicPauliLocalBoolMeasure
    (q : Nat) (h : Fin 2 -> Real) (axis : Fin 2) : Measure Bool :=
  ENNReal.ofReal
      (pureCyclicPauliLocalBornProbability q h axis false) • Measure.dirac false +
    ENNReal.ofReal
      (pureCyclicPauliLocalBornProbability q h axis true) • Measure.dirac true

theorem pureCyclicPauliLocalBoolMeasure_univ
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h) (axis : Fin 2) :
    pureCyclicPauliLocalBoolMeasure q h axis Set.univ = 1 := by
  simp only [pureCyclicPauliLocalBoolMeasure, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  change
    ENNReal.ofReal
        (pureCyclicPauliLocalBornProbability q h axis false) +
      ENNReal.ofReal
        (pureCyclicPauliLocalBornProbability q h axis true) = 1
  rw [← ENNReal.ofReal_add
    (pureCyclicPauliLocalBornProbability_nonnegative hvalid axis false)
    (pureCyclicPauliLocalBornProbability_nonnegative hvalid axis true)]
  rw [pureCyclicPauliLocalBornProbability_sum_one]
  norm_num

theorem pureCyclicPauliLocalBoolMeasure_isProbabilityMeasure
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h) (axis : Fin 2) :
    IsProbabilityMeasure (pureCyclicPauliLocalBoolMeasure q h axis) :=
  ⟨pureCyclicPauliLocalBoolMeasure_univ hvalid axis⟩

/-- Product Born law of the finite `q`-block pure tangent experiment. -/
def pureCyclicPauliFiniteLocalMeasure
    (q : Nat) (h : Fin 2 -> Real) : Measure (PureLinearSampleSpace q) :=
  Measure.infinitePi (fun index : PureLinearShotIndex q =>
    pureCyclicPauliLocalBoolMeasure q h index.1)

theorem pureCyclicPauliFiniteLocalMeasure_isProbabilityMeasure
    {q : Nat} {h : Fin 2 -> Real}
    (hvalid : PureCyclicPauliLocalChartValid q h) :
    IsProbabilityMeasure (pureCyclicPauliFiniteLocalMeasure q h) := by
  letI : forall index : PureLinearShotIndex q,
      IsProbabilityMeasure
        (pureCyclicPauliLocalBoolMeasure q h index.1) :=
    fun index => pureCyclicPauliLocalBoolMeasure_isProbabilityMeasure
      hvalid index.1
  unfold pureCyclicPauliFiniteLocalMeasure
  infer_instance

/-! ## Finite-row risks and exact minimax order -/

/-- A pure row estimator returns the local two-coordinate chart parameter. -/
abbrev PureCyclicPauliRowEstimator (q : Nat) :=
  PureLinearSampleSpace q -> (Fin 2 -> Real)

/-- A mixed row estimator returns a Bloch vector. -/
abbrev MixedCyclicPauliRowEstimator (q : Nat) :=
  PauliPilotPath q -> RLSVector 3

/-- Pure row risk at local chart parameter `h / sqrt(q)`. -/
def pureCyclicPauliLocalRisk
    (L : CyclicPauliSquareLoss (Fin 2))
    (q : Nat) (T : PureCyclicPauliRowEstimator q)
    (h : Fin 2 -> Real) : ENNReal :=
  ∫⁻ sample,
    ENNReal.ofReal
      (cyclicPauliSquareLossValue L (fun i =>
        Real.sqrt q *
          (T sample i - (Real.sqrt q)⁻¹ * h i)))
    ∂pureCyclicPauliFiniteLocalMeasure q h

/-- Mixed row risk at the exact local Bloch alternative.  The scaling is
`sqrt(3q)` because one complete block contains three physical shots. -/
def mixedCyclicPauliLocalRisk
    (theta : RLSVector 3)
    (L : CyclicPauliSquareLoss (Fin 3))
    (q : Nat) (T : MixedCyclicPauliRowEstimator q)
    (h : RLSVector 3) : ENNReal :=
  ∫⁻ sample,
    ENNReal.ofReal
      (cyclicPauliSquareLossValue L (fun i =>
        (Real.sqrt 3 * Real.sqrt q) *
          (T sample i - mixedCyclicPauliLocalBloch theta h q i)))
    ∂pauliPilotBornProductMeasure
      (q := q) (mixedCyclicPauliLocalBloch theta h q)

/-- Infimum over all pure row estimators of their worst risk in a local ball. -/
def pureCyclicPauliRowMinimaxRisk
    (L : CyclicPauliSquareLoss (Fin 2))
    (radius : Real) (q : Nat) : ENNReal :=
  ⨅ T : PureCyclicPauliRowEstimator q,
    ⨆ h : Fin 2 -> Real,
      ⨆ (_hRadius : cyclicPauliNormSq h < radius ^ 2),
        ⨆ (_hValid : PureCyclicPauliLocalChartValid q h),
          pureCyclicPauliLocalRisk L q T h

/-- Infimum over all mixed row estimators of their worst risk in a local ball. -/
def mixedCyclicPauliRowMinimaxRisk
    (theta : RLSVector 3)
    (L : CyclicPauliSquareLoss (Fin 3))
    (radius : Real) (q : Nat) : ENNReal :=
  ⨅ T : MixedCyclicPauliRowEstimator q,
    ⨆ h : RLSVector 3,
      ⨆ (_hRadius : cyclicPauliNormSq h < radius ^ 2),
        ⨆ (_hValid : MixedCyclicPauliStrictInterior
          (mixedCyclicPauliLocalBloch theta h q)),
          mixedCyclicPauliLocalRisk theta L q T h

/-- `radius -> infinity`, then `liminf q`, with the row estimator infimum
inside the asymptotic limits, exactly as in Beran's formula (4.1). -/
def pureCyclicPauliLocalAsymptoticMinimaxRisk
    (L : CyclicPauliSquareLoss (Fin 2)) : ENNReal :=
  ⨆ radius : Nat,
    Filter.liminf
      (fun q => pureCyclicPauliRowMinimaxRisk L (radius + 1) q) atTop

/-- Mixed analogue of the exact Beran minimax order. -/
def mixedCyclicPauliLocalAsymptoticMinimaxRisk
    (theta : RLSVector 3)
    (L : CyclicPauliSquareLoss (Fin 3)) : ENNReal :=
  ⨆ radius : Nat,
    Filter.liminf
      (fun q => mixedCyclicPauliRowMinimaxRisk theta L (radius + 1) q) atTop

/-! ## Fisher matrices and their exact inverses -/

def pureCyclicPauliInformationMatrix : Matrix (Fin 2) (Fin 2) Real :=
  fun i j => if i = j then 2 else 0

def pureCyclicPauliCovarianceMatrix : Matrix (Fin 2) (Fin 2) Real :=
  fun i j => if i = j then 1 / 2 else 0

theorem pureCyclicPauliFisherQuadratic_matrix
    (h : Fin 2 -> Real) :
    pureCyclicPauliFisherQuadratic h =
      dotProduct h (pureCyclicPauliInformationMatrix.mulVec h) := by
  simp [pureCyclicPauliFisherQuadratic,
    pureCyclicPauliInformationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

theorem pureCyclicPauliInformation_covariance_inverse :
    pureCyclicPauliInformationMatrix * pureCyclicPauliCovarianceMatrix = 1 ∧
      pureCyclicPauliCovarianceMatrix * pureCyclicPauliInformationMatrix = 1 := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, pureCyclicPauliInformationMatrix,
      pureCyclicPauliCovarianceMatrix, Fin.sum_univ_two]

def mixedCyclicPauliInformationMatrix
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    if i = j then (1 / 3 : Real) / (1 - theta i ^ 2) else 0

def mixedCyclicPauliCovarianceMatrix
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j => if i = j then 3 * (1 - theta i ^ 2) else 0

theorem mixedCyclicPauliFisherQuadratic_matrix
    (theta h : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    mixedCyclicPauliFisherQuadratic theta h =
      dotProduct h (mixedCyclicPauliInformationMatrix theta |>.mulVec h) := by
  rw [mixedCyclicPauliFisherQuadratic_eq theta h hInterior]
  have h0 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 0)
  have h1 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 1)
  have h2 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 2)
  simp [mixedCyclicPauliInformationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  field_simp [h0, h1, h2]
  all_goals ring

theorem mixedCyclicPauliInformation_covariance_inverse
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    mixedCyclicPauliInformationMatrix theta *
        mixedCyclicPauliCovarianceMatrix theta = 1 ∧
      mixedCyclicPauliCovarianceMatrix theta *
        mixedCyclicPauliInformationMatrix theta = 1 := by
  have h0 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 0)
  have h1 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 1)
  have h2 := ne_of_gt
    (mixedCyclicPauli_varianceDenominator_pos theta hInterior 2)
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mixedCyclicPauliInformationMatrix,
      mixedCyclicPauliCovarianceMatrix, Fin.sum_univ_three] <;>
    field_simp [h0, h1, h2] <;> ring

/-! ## Bures and fidelity quadratic-limit losses -/

/-- In the pure tangent chart used by the proved LAN theorem, squared Bures
and ordinary infidelity both have Euclidean quadratic limit. -/
abbrev pureCyclicPauliBuresQuadraticLoss :
    CyclicPauliSquareLoss (Fin 2) :=
  cyclicPauliEuclideanSquareLoss 2

/-- Mixed-qubit Bures metric as four squared linear features: three Euclidean
features and one radial feature. -/
def mixedCyclicPauliBuresQuadraticLoss
    (theta : RLSVector 3) : CyclicPauliSquareLoss (Fin 3) where
  featureCount := 4
  coefficient := fun a i =>
    if a.val = 3 then
      theta i / (2 * Real.sqrt (1 - QubitOracle.blochNormSq theta))
    else if a.val = i.val then 1 / 2 else 0

def mixedCyclicPauliBuresQuadraticValue
    (theta x : RLSVector 3) : Real :=
  (1 / 4 : Real) *
    (cyclicPauliNormSq x +
      (∑ i, theta i * x i) ^ 2 /
        (1 - QubitOracle.blochNormSq theta))

theorem mixedCyclicPauliBuresQuadraticLoss_value
    (theta x : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    cyclicPauliSquareLossValue
        (mixedCyclicPauliBuresQuadraticLoss theta) x =
      mixedCyclicPauliBuresQuadraticValue theta x := by
  have hden : 0 < 1 - QubitOracle.blochNormSq theta := by
    unfold MixedCyclicPauliStrictInterior at hInterior
    linarith
  have hsqrt : Real.sqrt (1 - QubitOracle.blochNormSq theta) ^ 2 =
      1 - QubitOracle.blochNormSq theta :=
    Real.sq_sqrt (le_of_lt hden)
  change
    (∑ a : Fin 4,
      (∑ i : Fin 3,
        (if a.val = 3 then
          theta i / (2 * Real.sqrt (1 - QubitOracle.blochNormSq theta))
        else if a.val = i.val then 1 / 2 else 0) * x i) ^ 2) =
      mixedCyclicPauliBuresQuadraticValue theta x
  rw [Fin.sum_univ_four]
  simp [Fin.sum_univ_three, mixedCyclicPauliBuresQuadraticValue,
    cyclicPauliNormSq]
  field_simp [ne_of_gt hden, Real.sqrt_ne_zero'.mpr hden]
  nlinarith [hsqrt]

theorem pureCyclicPauliBuresGaussianBenchmark_eq_one :
    cyclicPauliGaussianSquareBenchmark pureCyclicPauliBuresQuadraticLoss
      pureCyclicPauliCovarianceMatrix = 1 := by
  change
    (∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2,
      (if a = i then 1 else 0) * (if a = j then 1 else 0) *
        (if i = j then 1 / 2 else 0)) = 1
  norm_num [Fin.sum_univ_two]

/-- Exact mixed Bures/fidelity Gaussian benchmark for the cyclic `X,Y,Z`
design at an arbitrary strict-interior Bloch vector. -/
def mixedCyclicPauliBuresGaussianBenchmark
    (theta : RLSVector 3) : Real :=
  (3 / 4 : Real) *
    ((1 - theta 0 ^ 2) + (1 - theta 1 ^ 2) + (1 - theta 2 ^ 2) +
      (theta 0 ^ 2 * (1 - theta 0 ^ 2) +
        theta 1 ^ 2 * (1 - theta 1 ^ 2) +
        theta 2 ^ 2 * (1 - theta 2 ^ 2)) /
          (1 - QubitOracle.blochNormSq theta))

theorem mixedCyclicPauliBuresGaussianBenchmark_eq
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    cyclicPauliGaussianSquareBenchmark
        (mixedCyclicPauliBuresQuadraticLoss theta)
        (mixedCyclicPauliCovarianceMatrix theta) =
      mixedCyclicPauliBuresGaussianBenchmark theta := by
  have hden : 0 < 1 - QubitOracle.blochNormSq theta := by
    unfold MixedCyclicPauliStrictInterior at hInterior
    linarith
  have hsqrt : Real.sqrt (1 - QubitOracle.blochNormSq theta) ^ 2 =
      1 - QubitOracle.blochNormSq theta :=
    Real.sq_sqrt (le_of_lt hden)
  change
    (∑ a : Fin 4, ∑ i : Fin 3, ∑ j : Fin 3,
      (if a.val = 3 then
        theta i / (2 * Real.sqrt (1 - QubitOracle.blochNormSq theta))
      else if a.val = i.val then 1 / 2 else 0) *
      (if a.val = 3 then
        theta j / (2 * Real.sqrt (1 - QubitOracle.blochNormSq theta))
      else if a.val = j.val then 1 / 2 else 0) *
      (if i = j then 3 * (1 - theta i ^ 2) else 0)) =
      mixedCyclicPauliBuresGaussianBenchmark theta
  rw [Fin.sum_univ_four]
  simp [Fin.sum_univ_three, mixedCyclicPauliBuresGaussianBenchmark]
  field_simp [ne_of_gt hden, Real.sqrt_ne_zero'.mpr hden]
  rw [hsqrt]
  ring

/-! ## The sole scientific axiom: Beran (1995), Theorem 4.1 -/

/-- Exact one-qubit specialization of Beran's LAN-to-local-minimax theorem.

The premises expose every model-specific fact that is proved in Lean:
directional LAN for all local vectors, identification of the Fisher quadratic
form, and an explicit two-sided inverse covariance.  The conclusions retain
Beran's infimum over all row estimators and the source's order of limits.

This is the only scientific axiom in the file. -/
structure Beran1995Theorem41CyclicPauliOneQubitTransfer : Prop where
  pure_lower_bound :
    (forall h : Fin 2 -> Real, PureCyclicPauliLAN h) ->
    (forall h : Fin 2 -> Real,
      pureCyclicPauliFisherQuadratic h =
        dotProduct h (pureCyclicPauliInformationMatrix.mulVec h)) ->
    (pureCyclicPauliInformationMatrix *
          pureCyclicPauliCovarianceMatrix = 1 ∧
      pureCyclicPauliCovarianceMatrix *
          pureCyclicPauliInformationMatrix = 1) ->
    forall L : CyclicPauliSquareLoss (Fin 2),
      ENNReal.ofReal
          (cyclicPauliGaussianSquareBenchmark L
            pureCyclicPauliCovarianceMatrix) <=
        pureCyclicPauliLocalAsymptoticMinimaxRisk L
  mixed_lower_bound :
    forall (theta : RLSVector 3)
      (hInterior : MixedCyclicPauliStrictInterior theta),
      (forall h : RLSVector 3,
        MixedCyclicPauliLAN theta h hInterior) ->
      (forall h : RLSVector 3,
        mixedCyclicPauliFisherQuadratic theta h =
          dotProduct h
            ((mixedCyclicPauliInformationMatrix theta).mulVec h)) ->
      (mixedCyclicPauliInformationMatrix theta *
            mixedCyclicPauliCovarianceMatrix theta = 1 ∧
        mixedCyclicPauliCovarianceMatrix theta *
            mixedCyclicPauliInformationMatrix theta = 1) ->
      forall L : CyclicPauliSquareLoss (Fin 3),
        ENNReal.ofReal
            (cyclicPauliGaussianSquareBenchmark L
              (mixedCyclicPauliCovarianceMatrix theta)) <=
          mixedCyclicPauliLocalAsymptoticMinimaxRisk theta L

/-- Rudolf Beran (1995), Theorem 4.1, specialized exactly to the two finite
one-qubit cyclic experiments defined above.

Source: https://www.kybernetika.cz/content/1995/3/221/paper.pdf -/
axiom beran1995_theorem4_1_cyclicPauli_oneQubit :
  Beran1995Theorem41CyclicPauliOneQubitTransfer

/-! ## Lean-derived pure and mixed local minimax theorems -/

theorem pureCyclicPauliLocalMinimax_lowerBound
    (L : CyclicPauliSquareLoss (Fin 2)) :
    ENNReal.ofReal
        (cyclicPauliGaussianSquareBenchmark L
          pureCyclicPauliCovarianceMatrix) <=
      pureCyclicPauliLocalAsymptoticMinimaxRisk L := by
  exact beran1995_theorem4_1_cyclicPauli_oneQubit.pure_lower_bound
    pureCyclicPauli_LAN pureCyclicPauliFisherQuadratic_matrix
    pureCyclicPauliInformation_covariance_inverse L

theorem mixedCyclicPauliLocalMinimax_lowerBound
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta)
    (L : CyclicPauliSquareLoss (Fin 3)) :
    ENNReal.ofReal
        (cyclicPauliGaussianSquareBenchmark L
          (mixedCyclicPauliCovarianceMatrix theta)) <=
      mixedCyclicPauliLocalAsymptoticMinimaxRisk theta L := by
  exact beran1995_theorem4_1_cyclicPauli_oneQubit.mixed_lower_bound
    theta hInterior (fun h => mixedCyclicPauli_LAN theta h hInterior)
    (fun h => mixedCyclicPauliFisherQuadratic_matrix theta h hInterior)
    (mixedCyclicPauliInformation_covariance_inverse theta hInterior) L

/-- Pure squared-Bures and ordinary-infidelity local minimax lower bound. -/
theorem pureCyclicPauliBuresLocalMinimax_lowerBound :
    ENNReal.ofReal 1 <=
      pureCyclicPauliLocalAsymptoticMinimaxRisk
        pureCyclicPauliBuresQuadraticLoss := by
  rw [← pureCyclicPauliBuresGaussianBenchmark_eq_one]
  exact pureCyclicPauliLocalMinimax_lowerBound
    pureCyclicPauliBuresQuadraticLoss

/-- Mixed squared-Bures and ordinary-infidelity local minimax lower bound for
the fixed cyclic `X,Y,Z` design at every strict-interior Bloch vector. -/
theorem mixedCyclicPauliBuresLocalMinimax_lowerBound
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    ENNReal.ofReal (mixedCyclicPauliBuresGaussianBenchmark theta) <=
      mixedCyclicPauliLocalAsymptoticMinimaxRisk theta
        (mixedCyclicPauliBuresQuadraticLoss theta) := by
  rw [← mixedCyclicPauliBuresGaussianBenchmark_eq theta hInterior]
  exact mixedCyclicPauliLocalMinimax_lowerBound theta hInterior
    (mixedCyclicPauliBuresQuadraticLoss theta)

/-- Bundled paper-facing one-qubit cyclic local-minimax endpoint. -/
structure CyclicPauliOneQubitLocalMinimaxComplete : Prop where
  pure_all_quadratic_losses :
    forall L : CyclicPauliSquareLoss (Fin 2),
      ENNReal.ofReal
          (cyclicPauliGaussianSquareBenchmark L
            pureCyclicPauliCovarianceMatrix) <=
        pureCyclicPauliLocalAsymptoticMinimaxRisk L
  mixed_all_quadratic_losses :
    forall (theta : RLSVector 3)
      (hInterior : MixedCyclicPauliStrictInterior theta)
      (L : CyclicPauliSquareLoss (Fin 3)),
      ENNReal.ofReal
          (cyclicPauliGaussianSquareBenchmark L
            (mixedCyclicPauliCovarianceMatrix theta)) <=
        mixedCyclicPauliLocalAsymptoticMinimaxRisk theta L
  pure_bures_and_infidelity :
    ENNReal.ofReal 1 <=
      pureCyclicPauliLocalAsymptoticMinimaxRisk
        pureCyclicPauliBuresQuadraticLoss
  mixed_bures_and_infidelity :
    forall (theta : RLSVector 3)
      (hInterior : MixedCyclicPauliStrictInterior theta),
      ENNReal.ofReal (mixedCyclicPauliBuresGaussianBenchmark theta) <=
        mixedCyclicPauliLocalAsymptoticMinimaxRisk theta
          (mixedCyclicPauliBuresQuadraticLoss theta)

theorem cyclicPauliOneQubit_localMinimax_complete :
    CyclicPauliOneQubitLocalMinimaxComplete where
  pure_all_quadratic_losses := pureCyclicPauliLocalMinimax_lowerBound
  mixed_all_quadratic_losses := mixedCyclicPauliLocalMinimax_lowerBound
  pure_bures_and_infidelity := pureCyclicPauliBuresLocalMinimax_lowerBound
  mixed_bures_and_infidelity :=
    mixedCyclicPauliBuresLocalMinimax_lowerBound

end

end QubitOracle.Paper
