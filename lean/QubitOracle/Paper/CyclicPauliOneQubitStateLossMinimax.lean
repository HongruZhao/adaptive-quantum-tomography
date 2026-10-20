import QubitOracle.Paper.CyclicPauliOneQubitLocalMinimax
import QubitOracle.Paper.OneQubitMixedPolynomialOrdinaryInfidelityEndpoint

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Exact squared Frobenius (Hilbert--Schmidt) loss for qubit states,
written in Bloch coordinates. -/
def qubitBlochFrobeniusSq (theta sigma : RLSVector 3) : ℝ :=
  (1 / 2 : ℝ) * cyclicPauliNormSq (fun j => sigma j - theta j)

/-- A scalar multiple of the coordinate Euclidean square loss. -/
def cyclicPauliScaledEuclideanSquareLoss (d : ℕ) (scale : ℝ) :
    CyclicPauliSquareLoss (Fin d) where
  featureCount := d
  coefficient := fun a i => if a = i then scale else 0

theorem cyclicPauliNormSq_smul
    {D : Type*} [Fintype D] (scale : ℝ) (x : D → ℝ) :
    cyclicPauliNormSq (fun i => scale * x i) =
      scale ^ 2 * cyclicPauliNormSq x := by
  simp [cyclicPauliNormSq, mul_pow, Finset.mul_sum]

theorem cyclicPauliScaledEuclideanSquareLoss_value
    (d : ℕ) (scale : ℝ) (x : Fin d → ℝ) :
    cyclicPauliSquareLossValue
        (cyclicPauliScaledEuclideanSquareLoss d scale) x =
      scale ^ 2 * cyclicPauliNormSq x := by
  simp [cyclicPauliSquareLossValue,
    cyclicPauliScaledEuclideanSquareLoss, cyclicPauliNormSq,
    mul_pow, Finset.mul_sum]
  rfl

theorem cyclicPauliScaledEuclideanSquareLoss_benchmark
    (d : ℕ) (scale : ℝ) (covariance : Matrix (Fin d) (Fin d) ℝ) :
    cyclicPauliGaussianSquareBenchmark
        (cyclicPauliScaledEuclideanSquareLoss d scale) covariance =
      scale ^ 2 * ∑ i : Fin d, covariance i i := by
  simp [cyclicPauliGaussianSquareBenchmark,
    cyclicPauliScaledEuclideanSquareLoss, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coordinate loss exactly matching mixed-qubit Frobenius risk. -/
def mixedCyclicPauliFrobeniusCoordinateLoss :
    CyclicPauliSquareLoss (Fin 3) :=
  cyclicPauliScaledEuclideanSquareLoss 3 (Real.sqrt 2 / 2)

/-- The coordinate loss dominated globally by mixed-qubit squared Bures risk. -/
def mixedCyclicPauliBuresDirectCoordinateLoss :
    CyclicPauliSquareLoss (Fin 3) :=
  cyclicPauliScaledEuclideanSquareLoss 3 (1 / 2 : ℝ)

/-- The tangent-coordinate loss exactly matching the pure-qubit Frobenius lower comparison. -/
def pureCyclicPauliFrobeniusCoordinateLoss :
    CyclicPauliSquareLoss (Fin 2) :=
  cyclicPauliScaledEuclideanSquareLoss 2 (Real.sqrt 2)

/-- The tangent-coordinate loss dominated globally by pure-qubit squared Bures risk. -/
def pureCyclicPauliBuresDirectCoordinateLoss :
    CyclicPauliSquareLoss (Fin 2) :=
  cyclicPauliEuclideanSquareLoss 2

theorem mixedCyclicPauliFrobeniusCoordinateLoss_value
    (x : Fin 3 → ℝ) :
    cyclicPauliSquareLossValue mixedCyclicPauliFrobeniusCoordinateLoss x =
      (1 / 2 : ℝ) * cyclicPauliNormSq x := by
  rw [show mixedCyclicPauliFrobeniusCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 3 (Real.sqrt 2 / 2) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_value]
  have hTwo : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hScale : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, hTwo]
    norm_num
  rw [hScale]

theorem mixedCyclicPauliBuresDirectCoordinateLoss_value
    (x : Fin 3 → ℝ) :
    cyclicPauliSquareLossValue mixedCyclicPauliBuresDirectCoordinateLoss x =
      (1 / 4 : ℝ) * cyclicPauliNormSq x := by
  rw [show mixedCyclicPauliBuresDirectCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 3 (1 / 2 : ℝ) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_value]
  ring

theorem pureCyclicPauliFrobeniusCoordinateLoss_value
    (x : Fin 2 → ℝ) :
    cyclicPauliSquareLossValue pureCyclicPauliFrobeniusCoordinateLoss x =
      2 * cyclicPauliNormSq x := by
  rw [show pureCyclicPauliFrobeniusCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 2 (Real.sqrt 2) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_value,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem pureCyclicPauliBuresDirectCoordinateLoss_value
    (x : Fin 2 → ℝ) :
    cyclicPauliSquareLossValue pureCyclicPauliBuresDirectCoordinateLoss x =
      cyclicPauliNormSq x :=
  cyclicPauliEuclideanSquareLoss_value 2 x

theorem cyclicPauliNormSq_sub_eq
    (theta sigma : RLSVector 3) :
    cyclicPauliNormSq (fun j => sigma j - theta j) =
      blochNormSq sigma + blochNormSq theta - 2 * blochDot theta sigma := by
  simp [cyclicPauliNormSq, blochNormSq, blochDot, Fin.sum_univ_succ]
  ring

/-- Global physical-state comparison: squared Bures distance dominates one
quarter of squared Bloch Euclidean distance. -/
theorem mixedQubitBlochBuresSqBetween_ge_quarter_normSq
    {theta sigma : RLSVector 3}
    (hTheta : PauliPilotPhysicalBloch theta)
    (hSigma : PauliPilotPhysicalBloch sigma) :
    (1 / 4 : ℝ) * cyclicPauliNormSq (fun j => sigma j - theta j) ≤
      mixedQubitBlochBuresSqBetween theta sigma := by
  have hTheta' : blochNormSq theta ≤ 1 := hTheta
  have hSigma' : blochNormSq sigma ≤ 1 := hSigma
  have hA : 0 ≤ 1 - blochNormSq theta := sub_nonneg.mpr hTheta'
  have hB : 0 ≤ 1 - blochNormSq sigma := sub_nonneg.mpr hSigma'
  have hSqrtMul :
      Real.sqrt ((1 - blochNormSq theta) * (1 - blochNormSq sigma)) =
        Real.sqrt (1 - blochNormSq theta) *
          Real.sqrt (1 - blochNormSq sigma) := by
    rw [Real.sqrt_mul hA]
  have hSquareA :
      Real.sqrt (1 - blochNormSq theta) ^ 2 =
        1 - blochNormSq theta := Real.sq_sqrt hA
  have hSquareB :
      Real.sqrt (1 - blochNormSq sigma) ^ 2 =
        1 - blochNormSq sigma := Real.sq_sqrt hB
  have hInfidelity :
      (1 / 4 : ℝ) * cyclicPauliNormSq (fun j => sigma j - theta j) ≤
        mixedQubitBlochInfidelityBetween theta sigma := by
    rw [cyclicPauliNormSq_sub_eq]
    unfold mixedQubitBlochInfidelityBetween
      mixedQubitBlochFidelitySqBetween
    rw [hSqrtMul]
    nlinarith [sq_nonneg
      (Real.sqrt (1 - blochNormSq theta) -
        Real.sqrt (1 - blochNormSq sigma))]
  have hRoot :=
    mixedQubitBlochRootFidelityBetween_mem_Icc hTheta' hSigma'
  have hRootSquare :
      mixedQubitBlochRootFidelityBetween theta sigma ^ 2 =
        mixedQubitBlochFidelitySqBetween theta sigma := by
    unfold mixedQubitBlochRootFidelityBetween
    exact Real.sq_sqrt
      (mixedQubitBlochFidelitySqBetween_mem_Icc hTheta' hSigma').1
  have hInfidelityLeBures :
      mixedQubitBlochInfidelityBetween theta sigma ≤
        mixedQubitBlochBuresSqBetween theta sigma := by
    unfold mixedQubitBlochInfidelityBetween
      mixedQubitBlochBuresSqBetween
      mixedQubitBlochRootInfidelityBetween
    nlinarith [sq_nonneg
      (1 - mixedQubitBlochRootFidelityBetween theta sigma)]
  exact hInfidelity.trans hInfidelityLeBures

/-! ## Physical state-valued estimator classes and exact risks -/

/-- A mixed-qubit estimator is required to return a physical Bloch vector on
every data path. -/
structure MixedCyclicPauliPhysicalStateEstimator (q : ℕ) where
  bloch : PauliPilotPath q → RLSVector 3
  physical : ∀ sample, PauliPilotPhysicalBloch (bloch sample)

/-- A pure-qubit experiment may still use a mixed-state estimate.  Requiring
only Bloch-ball physicality makes the lower bound apply to all physical output
states, not merely estimates constrained to the pure sphere. -/
structure PureCyclicPauliPhysicalStateEstimator (q : ℕ) where
  bloch :
    OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → RLSVector 3
  physical : ∀ sample, PauliPilotPhysicalBloch (bloch sample)

def MixedCyclicPauliPhysicalStateEstimator.toRowEstimator
    {q : ℕ} (T : MixedCyclicPauliPhysicalStateEstimator q) :
    MixedCyclicPauliRowEstimator q :=
  T.bloch

/-- The first two Bloch coordinates, normalized to the paper's pure tangent
chart. -/
def PureCyclicPauliPhysicalStateEstimator.toRowEstimator
    {q : ℕ} (T : PureCyclicPauliPhysicalStateEstimator q) :
    PureCyclicPauliRowEstimator q :=
  fun sample i => (Real.sqrt 2 / 2) * T.bloch sample i.castSucc

/-- Exact total-shot-normalized risk for a mixed cyclic-Pauli experiment. -/
def mixedCyclicPauliStateLossRisk
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (theta : RLSVector 3) (q : ℕ)
    (T : MixedCyclicPauliPhysicalStateEstimator q) (h : RLSVector 3) :
    ENNReal :=
  ∫⁻ sample,
    ENNReal.ofReal
      ((3 * (q : ℝ)) *
        loss (mixedCyclicPauliLocalBloch theta h q) (T.bloch sample))
    ∂pauliPilotBornProductMeasure (mixedCyclicPauliLocalBloch theta h q)

/-- Exact total-shot-normalized risk for the pure two-axis cyclic experiment. -/
def pureCyclicPauliStateLossRisk
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (q : ℕ) (T : PureCyclicPauliPhysicalStateEstimator q)
    (h : Fin 2 → ℝ) : ENNReal :=
  ∫⁻ sample,
    ENNReal.ofReal
      ((2 * (q : ℝ)) *
        loss (pureCyclicPauliLocalBloch q h) (T.bloch sample))
    ∂pureCyclicPauliFiniteLocalMeasure q h

def mixedCyclicPauliStateRowMinimaxRisk
    (theta : RLSVector 3)
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (radius : ℝ) (q : ℕ) : ENNReal :=
  ⨅ T : MixedCyclicPauliPhysicalStateEstimator q,
    ⨆ h : RLSVector 3,
      ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
        ⨆ (_ : MixedCyclicPauliStrictInterior
          (mixedCyclicPauliLocalBloch theta h q)),
          mixedCyclicPauliStateLossRisk loss theta q T h

def pureCyclicPauliStateRowMinimaxRisk
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (radius : ℝ) (q : ℕ) : ENNReal :=
  ⨅ T : PureCyclicPauliPhysicalStateEstimator q,
    ⨆ h : Fin 2 → ℝ,
      ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
        ⨆ (_ : PureCyclicPauliLocalChartValid q h),
          pureCyclicPauliStateLossRisk loss q T h

def mixedCyclicPauliStateLocalAsymptoticMinimaxRisk
    (theta : RLSVector 3)
    (loss : RLSVector 3 → RLSVector 3 → ℝ) : ENNReal :=
  ⨆ radius : ℕ,
    Filter.liminf
      (fun q => mixedCyclicPauliStateRowMinimaxRisk theta loss
        ((radius : ℝ) + 1) q) Filter.atTop

def pureCyclicPauliStateLocalAsymptoticMinimaxRisk
    (loss : RLSVector 3 → RLSVector 3 → ℝ) : ENNReal :=
  ⨆ radius : ℕ,
    Filter.liminf
      (fun q => pureCyclicPauliStateRowMinimaxRisk loss
        ((radius : ℝ) + 1) q) Filter.atTop

theorem mixedCyclicPauliLocalBloch_physical
    {theta h : RLSVector 3} {q : ℕ}
    (hValid : MixedCyclicPauliStrictInterior
      (mixedCyclicPauliLocalBloch theta h q)) :
    PauliPilotPhysicalBloch (mixedCyclicPauliLocalBloch theta h q) := by
  exact le_of_lt hValid

theorem pureCyclicPauliLocalBloch_physical
    {q : ℕ} {h : Fin 2 → ℝ}
    (hValid : PureCyclicPauliLocalChartValid q h) :
    PauliPilotPhysicalBloch (pureCyclicPauliLocalBloch q h) := by
  have hRadicand :
      0 ≤ 1 - pureCyclicPauliLocalTilt q h 0 ^ 2 -
        pureCyclicPauliLocalTilt q h 1 ^ 2 := by
    linarith [hValid.2]
  unfold PauliPilotPhysicalBloch
  simp [pureCyclicPauliLocalBloch, Fin.sum_univ_succ,
    Real.sq_sqrt hRadicand]

theorem cyclicPauliNormSq_firstTwo_le
    (x : RLSVector 3) :
    cyclicPauliNormSq (fun i : Fin 2 => x i.castSucc) ≤
      cyclicPauliNormSq x := by
  simp [cyclicPauliNormSq, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 2)]

/-! ## Pointwise and expected-risk transfer -/

theorem mixedCyclicPauliFrobeniusCoordinateValue_eq
    (q : ℕ) (theta sigma : RLSVector 3) :
    cyclicPauliSquareLossValue mixedCyclicPauliFrobeniusCoordinateLoss
        (fun j => Real.sqrt 3 * Real.sqrt (q : ℝ) *
          (sigma j - theta j)) =
      (3 * (q : ℝ)) * qubitBlochFrobeniusSq theta sigma := by
  rw [mixedCyclicPauliFrobeniusCoordinateLoss_value,
    cyclicPauliNormSq_smul,
    mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt (Nat.cast_nonneg q)]
  unfold qubitBlochFrobeniusSq
  ring

theorem mixedCyclicPauliBuresCoordinateValue_le
    (q : ℕ) {theta sigma : RLSVector 3}
    (hTheta : PauliPilotPhysicalBloch theta)
    (hSigma : PauliPilotPhysicalBloch sigma) :
    cyclicPauliSquareLossValue mixedCyclicPauliBuresDirectCoordinateLoss
        (fun j => Real.sqrt 3 * Real.sqrt (q : ℝ) *
          (sigma j - theta j)) ≤
      (3 * (q : ℝ)) * mixedQubitBlochBuresSqBetween theta sigma := by
  rw [mixedCyclicPauliBuresDirectCoordinateLoss_value,
    cyclicPauliNormSq_smul,
    mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt (Nat.cast_nonneg q)]
  have hBures :=
    mixedQubitBlochBuresSqBetween_ge_quarter_normSq hTheta hSigma
  have hScaled := mul_le_mul_of_nonneg_left hBures
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg q))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hScaled

theorem pureCyclicPauliTangentCenter_eq
    {q : ℕ} {h : Fin 2 → ℝ}
    (hValid : PureCyclicPauliLocalChartValid q h) (i : Fin 2) :
    (Real.sqrt 2 / 2) * pureCyclicPauliLocalBloch q h i.castSucc =
      (Real.sqrt (q : ℝ))⁻¹ * h i := by
  have hTwo : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hq : Real.sqrt (q : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hValid.1)
  fin_cases i <;>
    simp [pureCyclicPauliLocalBloch, pureCyclicPauliLocalTilt] <;>
    field_simp [hq] <;>
    rw [hTwo]

theorem pureCyclicPauliCoordinateNormSq_eq
    {q : ℕ} (T : PureCyclicPauliPhysicalStateEstimator q)
    (h : Fin 2 → ℝ) (sample :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q)
    (hValid : PureCyclicPauliLocalChartValid q h) :
    cyclicPauliNormSq (fun i =>
        Real.sqrt (q : ℝ) *
          (T.toRowEstimator sample i -
            (Real.sqrt (q : ℝ))⁻¹ * h i)) =
      ((q : ℝ) / 2) *
        cyclicPauliNormSq (fun i : Fin 2 =>
          T.bloch sample i.castSucc -
            pureCyclicPauliLocalBloch q h i.castSucc) := by
  have hTwo : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  have hPointwise :
      (fun i : Fin 2 =>
        Real.sqrt (q : ℝ) *
          (T.toRowEstimator sample i -
            (Real.sqrt (q : ℝ))⁻¹ * h i)) =
        (fun i : Fin 2 =>
          (Real.sqrt (q : ℝ) * (Real.sqrt 2 / 2)) *
            (T.bloch sample i.castSucc -
              pureCyclicPauliLocalBloch q h i.castSucc)) := by
    funext i
    rw [← pureCyclicPauliTangentCenter_eq hValid i]
    unfold PureCyclicPauliPhysicalStateEstimator.toRowEstimator
    ring
  rw [hPointwise, cyclicPauliNormSq_smul]
  congr 1
  rw [mul_pow, hq]
  nlinarith

theorem mixedCyclicPauliFrobeniusLocalRisk_eq_stateRisk
    (theta : RLSVector 3) (q : ℕ)
    (T : MixedCyclicPauliPhysicalStateEstimator q) (h : RLSVector 3) :
    mixedCyclicPauliLocalRisk theta
        mixedCyclicPauliFrobeniusCoordinateLoss q T.toRowEstimator h =
      mixedCyclicPauliStateLossRisk qubitBlochFrobeniusSq theta q T h := by
  unfold mixedCyclicPauliLocalRisk mixedCyclicPauliStateLossRisk
  apply lintegral_congr
  intro sample
  congr 1
  exact mixedCyclicPauliFrobeniusCoordinateValue_eq q
    (mixedCyclicPauliLocalBloch theta h q) (T.bloch sample)

theorem mixedCyclicPauliBuresLocalRisk_le_stateRisk
    (theta : RLSVector 3) (q : ℕ)
    (T : MixedCyclicPauliPhysicalStateEstimator q) (h : RLSVector 3)
    (hValid : MixedCyclicPauliStrictInterior
      (mixedCyclicPauliLocalBloch theta h q)) :
    mixedCyclicPauliLocalRisk theta
        mixedCyclicPauliBuresDirectCoordinateLoss q T.toRowEstimator h ≤
      mixedCyclicPauliStateLossRisk mixedQubitBlochBuresSqBetween
        theta q T h := by
  unfold mixedCyclicPauliLocalRisk mixedCyclicPauliStateLossRisk
  apply lintegral_mono
  intro sample
  apply ENNReal.ofReal_le_ofReal
  exact mixedCyclicPauliBuresCoordinateValue_le q
    (mixedCyclicPauliLocalBloch_physical hValid) (T.physical sample)

theorem pureCyclicPauliFrobeniusLocalRisk_le_stateRisk
    (q : ℕ) (T : PureCyclicPauliPhysicalStateEstimator q)
    (h : Fin 2 → ℝ) (hValid : PureCyclicPauliLocalChartValid q h) :
    pureCyclicPauliLocalRisk pureCyclicPauliFrobeniusCoordinateLoss
        q T.toRowEstimator h ≤
      pureCyclicPauliStateLossRisk qubitBlochFrobeniusSq q T h := by
  unfold pureCyclicPauliLocalRisk pureCyclicPauliStateLossRisk
  apply lintegral_mono
  intro sample
  apply ENNReal.ofReal_le_ofReal
  rw [pureCyclicPauliFrobeniusCoordinateLoss_value,
    pureCyclicPauliCoordinateNormSq_eq T h sample hValid]
  unfold qubitBlochFrobeniusSq
  have hTangent := cyclicPauliNormSq_firstTwo_le
    (fun j => T.bloch sample j - pureCyclicPauliLocalBloch q h j)
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith

theorem pureCyclicPauliBuresLocalRisk_le_stateRisk
    (q : ℕ) (T : PureCyclicPauliPhysicalStateEstimator q)
    (h : Fin 2 → ℝ) (hValid : PureCyclicPauliLocalChartValid q h) :
    pureCyclicPauliLocalRisk pureCyclicPauliBuresDirectCoordinateLoss
        q T.toRowEstimator h ≤
      pureCyclicPauliStateLossRisk mixedQubitBlochBuresSqBetween q T h := by
  unfold pureCyclicPauliLocalRisk pureCyclicPauliStateLossRisk
  apply lintegral_mono
  intro sample
  apply ENNReal.ofReal_le_ofReal
  rw [pureCyclicPauliBuresDirectCoordinateLoss_value,
    pureCyclicPauliCoordinateNormSq_eq T h sample hValid]
  have hTangent := cyclicPauliNormSq_firstTwo_le
    (fun j => T.bloch sample j - pureCyclicPauliLocalBloch q h j)
  have hBures := mixedQubitBlochBuresSqBetween_ge_quarter_normSq
    (pureCyclicPauliLocalBloch_physical hValid) (T.physical sample)
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith

/-! ## Minimax-order transfer -/

theorem mixedCyclicPauliRowMinimax_le_stateRow_of_local
    (theta : RLSVector 3) (L : CyclicPauliSquareLoss (Fin 3))
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (radius : ℝ) (q : ℕ)
    (hTransfer : ∀ (T : MixedCyclicPauliPhysicalStateEstimator q)
      (h : RLSVector 3),
      MixedCyclicPauliStrictInterior
        (mixedCyclicPauliLocalBloch theta h q) →
      mixedCyclicPauliLocalRisk theta L q T.toRowEstimator h ≤
        mixedCyclicPauliStateLossRisk loss theta q T h) :
    mixedCyclicPauliRowMinimaxRisk theta L radius q ≤
      mixedCyclicPauliStateRowMinimaxRisk theta loss radius q := by
  unfold mixedCyclicPauliRowMinimaxRisk
    mixedCyclicPauliStateRowMinimaxRisk
  apply le_iInf
  intro T
  calc
    (⨅ S : MixedCyclicPauliRowEstimator q,
      ⨆ h : RLSVector 3,
        ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
          ⨆ (_ : MixedCyclicPauliStrictInterior
            (mixedCyclicPauliLocalBloch theta h q)),
              mixedCyclicPauliLocalRisk theta L q S h) ≤
        ⨆ h : RLSVector 3,
          ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
            ⨆ (_ : MixedCyclicPauliStrictInterior
              (mixedCyclicPauliLocalBloch theta h q)),
                mixedCyclicPauliLocalRisk theta L q T.toRowEstimator h :=
      iInf_le _ T.toRowEstimator
    _ ≤ ⨆ h : RLSVector 3,
          ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
            ⨆ (_ : MixedCyclicPauliStrictInterior
              (mixedCyclicPauliLocalBloch theta h q)),
                mixedCyclicPauliStateLossRisk loss theta q T h := by
      apply iSup_le
      intro h
      refine le_iSup_of_le h ?_
      apply iSup_le
      intro hRadius
      refine le_iSup_of_le hRadius ?_
      apply iSup_le
      intro hValid
      exact le_iSup_of_le hValid (hTransfer T h hValid)

theorem pureCyclicPauliRowMinimax_le_stateRow_of_local
    (L : CyclicPauliSquareLoss (Fin 2))
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (radius : ℝ) (q : ℕ)
    (hTransfer : ∀ (T : PureCyclicPauliPhysicalStateEstimator q)
      (h : Fin 2 → ℝ), PureCyclicPauliLocalChartValid q h →
      pureCyclicPauliLocalRisk L q T.toRowEstimator h ≤
        pureCyclicPauliStateLossRisk loss q T h) :
    pureCyclicPauliRowMinimaxRisk L radius q ≤
      pureCyclicPauliStateRowMinimaxRisk loss radius q := by
  unfold pureCyclicPauliRowMinimaxRisk pureCyclicPauliStateRowMinimaxRisk
  apply le_iInf
  intro T
  calc
    (⨅ S : PureCyclicPauliRowEstimator q,
      ⨆ h : Fin 2 → ℝ,
        ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
          ⨆ (_ : PureCyclicPauliLocalChartValid q h),
            pureCyclicPauliLocalRisk L q S h) ≤
        ⨆ h : Fin 2 → ℝ,
          ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
            ⨆ (_ : PureCyclicPauliLocalChartValid q h),
              pureCyclicPauliLocalRisk L q T.toRowEstimator h :=
      iInf_le _ T.toRowEstimator
    _ ≤ ⨆ h : Fin 2 → ℝ,
          ⨆ (_ : cyclicPauliNormSq h < radius ^ 2),
            ⨆ (_ : PureCyclicPauliLocalChartValid q h),
              pureCyclicPauliStateLossRisk loss q T h := by
      apply iSup_le
      intro h
      refine le_iSup_of_le h ?_
      apply iSup_le
      intro hRadius
      refine le_iSup_of_le hRadius ?_
      apply iSup_le
      intro hValid
      exact le_iSup_of_le hValid (hTransfer T h hValid)

theorem mixedCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
    (theta : RLSVector 3) (L : CyclicPauliSquareLoss (Fin 3))
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (hRows : ∀ (radius : ℝ) (q : ℕ),
      mixedCyclicPauliRowMinimaxRisk theta L radius q ≤
        mixedCyclicPauliStateRowMinimaxRisk theta loss radius q) :
    mixedCyclicPauliLocalAsymptoticMinimaxRisk theta L ≤
      mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta loss := by
  unfold mixedCyclicPauliLocalAsymptoticMinimaxRisk
    mixedCyclicPauliStateLocalAsymptoticMinimaxRisk
  apply iSup_le
  intro radius
  refine le_iSup_of_le radius ?_
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall fun q => hRows ((radius : ℝ) + 1) q)

theorem pureCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
    (L : CyclicPauliSquareLoss (Fin 2))
    (loss : RLSVector 3 → RLSVector 3 → ℝ)
    (hRows : ∀ (radius : ℝ) (q : ℕ),
      pureCyclicPauliRowMinimaxRisk L radius q ≤
        pureCyclicPauliStateRowMinimaxRisk loss radius q) :
    pureCyclicPauliLocalAsymptoticMinimaxRisk L ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk loss := by
  unfold pureCyclicPauliLocalAsymptoticMinimaxRisk
    pureCyclicPauliStateLocalAsymptoticMinimaxRisk
  apply iSup_le
  intro radius
  refine le_iSup_of_le radius ?_
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall fun q => hRows ((radius : ℝ) + 1) q)

theorem mixedCyclicPauliFrobeniusCoordinateMinimax_le_state :
    ∀ theta : RLSVector 3,
      mixedCyclicPauliLocalAsymptoticMinimaxRisk theta
          mixedCyclicPauliFrobeniusCoordinateLoss ≤
        mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
          qubitBlochFrobeniusSq := by
  intro theta
  apply mixedCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
  intro radius q
  apply mixedCyclicPauliRowMinimax_le_stateRow_of_local
  intro T h hValid
  exact (mixedCyclicPauliFrobeniusLocalRisk_eq_stateRisk theta q T h).le

theorem mixedCyclicPauliBuresCoordinateMinimax_le_state :
    ∀ theta : RLSVector 3,
      mixedCyclicPauliLocalAsymptoticMinimaxRisk theta
          mixedCyclicPauliBuresDirectCoordinateLoss ≤
        mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
          mixedQubitBlochBuresSqBetween := by
  intro theta
  apply mixedCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
  intro radius q
  apply mixedCyclicPauliRowMinimax_le_stateRow_of_local
  intro T h hValid
  exact mixedCyclicPauliBuresLocalRisk_le_stateRisk theta q T h hValid

theorem pureCyclicPauliFrobeniusCoordinateMinimax_le_state :
    pureCyclicPauliLocalAsymptoticMinimaxRisk
        pureCyclicPauliFrobeniusCoordinateLoss ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        qubitBlochFrobeniusSq := by
  apply pureCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
  intro radius q
  apply pureCyclicPauliRowMinimax_le_stateRow_of_local
  intro T h hValid
  exact pureCyclicPauliFrobeniusLocalRisk_le_stateRisk q T h hValid

theorem pureCyclicPauliBuresCoordinateMinimax_le_state :
    pureCyclicPauliLocalAsymptoticMinimaxRisk
        pureCyclicPauliBuresDirectCoordinateLoss ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        mixedQubitBlochBuresSqBetween := by
  apply pureCyclicPauliLocalAsymptoticMinimax_le_state_of_rows
  intro radius q
  apply pureCyclicPauliRowMinimax_le_stateRow_of_local
  intro T h hValid
  exact pureCyclicPauliBuresLocalRisk_le_stateRisk q T h hValid

/-! ## Explicit Gaussian benchmarks and final state-loss minimax endpoints -/

theorem pureCyclicPauliFrobeniusCoordinateBenchmark_eq_two :
    cyclicPauliGaussianSquareBenchmark
      pureCyclicPauliFrobeniusCoordinateLoss
      pureCyclicPauliCovarianceMatrix = 2 := by
  rw [show pureCyclicPauliFrobeniusCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 2 (Real.sqrt 2) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_benchmark,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [pureCyclicPauliCovarianceMatrix, Fin.sum_univ_succ]

theorem pureCyclicPauliBuresDirectCoordinateBenchmark_eq_one :
    cyclicPauliGaussianSquareBenchmark
      pureCyclicPauliBuresDirectCoordinateLoss
      pureCyclicPauliCovarianceMatrix = 1 := by
  rw [show pureCyclicPauliBuresDirectCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 2 1 by rfl,
    cyclicPauliScaledEuclideanSquareLoss_benchmark]
  norm_num [pureCyclicPauliCovarianceMatrix, Fin.sum_univ_succ]

theorem mixedCyclicPauliFrobeniusCoordinateBenchmark_eq
    (theta : RLSVector 3) :
    cyclicPauliGaussianSquareBenchmark
      mixedCyclicPauliFrobeniusCoordinateLoss
      (mixedCyclicPauliCovarianceMatrix theta) =
      (3 / 2 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2) := by
  rw [show mixedCyclicPauliFrobeniusCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 3 (Real.sqrt 2 / 2) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_benchmark]
  have hTwo : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  rw [div_pow, hTwo]
  simp [mixedCyclicPauliCovarianceMatrix, Fin.sum_univ_succ]
  ring

theorem mixedCyclicPauliBuresDirectCoordinateBenchmark_eq
    (theta : RLSVector 3) :
    cyclicPauliGaussianSquareBenchmark
      mixedCyclicPauliBuresDirectCoordinateLoss
      (mixedCyclicPauliCovarianceMatrix theta) =
      (3 / 4 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2) := by
  rw [show mixedCyclicPauliBuresDirectCoordinateLoss =
      cyclicPauliScaledEuclideanSquareLoss 3 (1 / 2 : ℝ) by rfl,
    cyclicPauliScaledEuclideanSquareLoss_benchmark]
  simp [mixedCyclicPauliCovarianceMatrix, Fin.sum_univ_succ]
  ring

/-- Sharp direct Frobenius local-minimax lower bound for the mixed cyclic-Pauli
qubit experiment.  The infimum is over all physical state-valued estimators. -/
theorem mixedCyclicPauliFrobeniusStateLocalMinimax_lowerBound
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    ENNReal.ofReal
        ((3 / 2 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2)) ≤
      mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
        qubitBlochFrobeniusSq := by
  rw [← mixedCyclicPauliFrobeniusCoordinateBenchmark_eq theta]
  exact (mixedCyclicPauliLocalMinimax_lowerBound theta hInterior
    mixedCyclicPauliFrobeniusCoordinateLoss).trans
      (mixedCyclicPauliFrobeniusCoordinateMinimax_le_state theta)

/-- Globally valid direct squared-Bures local-minimax lower bound for the mixed
cyclic-Pauli qubit experiment.  It is sharp at the maximally mixed state and is
generally conservative away from that point. -/
theorem mixedCyclicPauliBuresStateLocalMinimax_lowerBound
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    ENNReal.ofReal
        ((3 / 4 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2)) ≤
      mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
        mixedQubitBlochBuresSqBetween := by
  rw [← mixedCyclicPauliBuresDirectCoordinateBenchmark_eq theta]
  exact (mixedCyclicPauliLocalMinimax_lowerBound theta hInterior
    mixedCyclicPauliBuresDirectCoordinateLoss).trans
      (mixedCyclicPauliBuresCoordinateMinimax_le_state theta)

/-- Sharp direct Frobenius local-minimax lower bound for the pure cyclic-Pauli
qubit experiment, allowing the estimator to output any physical mixed state. -/
theorem pureCyclicPauliFrobeniusStateLocalMinimax_lowerBound :
    ENNReal.ofReal 2 ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        qubitBlochFrobeniusSq := by
  rw [← pureCyclicPauliFrobeniusCoordinateBenchmark_eq_two]
  exact (pureCyclicPauliLocalMinimax_lowerBound
    pureCyclicPauliFrobeniusCoordinateLoss).trans
      pureCyclicPauliFrobeniusCoordinateMinimax_le_state

/-- Direct squared-Bures local-minimax lower bound for the pure cyclic-Pauli
qubit experiment, allowing the estimator to output any physical mixed state. -/
theorem pureCyclicPauliBuresStateLocalMinimax_lowerBound :
    ENNReal.ofReal 1 ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        mixedQubitBlochBuresSqBetween := by
  rw [← pureCyclicPauliBuresDirectCoordinateBenchmark_eq_one]
  exact (pureCyclicPauliLocalMinimax_lowerBound
    pureCyclicPauliBuresDirectCoordinateLoss).trans
      pureCyclicPauliBuresCoordinateMinimax_le_state

/-- One-qubit loss-induced local-minimax package: exact Frobenius and direct
squared-Bures lower bounds for both mixed and pure cyclic-Pauli experiments. -/
theorem cyclicPauliOneQubit_stateLossLocalMinimax_complete
    (theta : RLSVector 3)
    (hInterior : MixedCyclicPauliStrictInterior theta) :
    (ENNReal.ofReal
        ((3 / 2 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2)) ≤
      mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
        qubitBlochFrobeniusSq) ∧
    (ENNReal.ofReal
        ((3 / 4 : ℝ) * ∑ j : Fin 3, (1 - theta j ^ 2)) ≤
      mixedCyclicPauliStateLocalAsymptoticMinimaxRisk theta
        mixedQubitBlochBuresSqBetween) ∧
    (ENNReal.ofReal 2 ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        qubitBlochFrobeniusSq) ∧
    (ENNReal.ofReal 1 ≤
      pureCyclicPauliStateLocalAsymptoticMinimaxRisk
        mixedQubitBlochBuresSqBetween) := by
  exact ⟨mixedCyclicPauliFrobeniusStateLocalMinimax_lowerBound theta hInterior,
    mixedCyclicPauliBuresStateLocalMinimax_lowerBound theta hInterior,
    pureCyclicPauliFrobeniusStateLocalMinimax_lowerBound,
    pureCyclicPauliBuresStateLocalMinimax_lowerBound⟩

end

end QubitOracle.Paper
