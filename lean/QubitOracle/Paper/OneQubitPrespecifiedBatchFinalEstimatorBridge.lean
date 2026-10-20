import QubitOracle.Paper.OneQubitPrespecifiedBatchSafeguardedEstimatorAsymptotics
import QubitOracle.Paper.OneQubitPrespecifiedBatchObservedInformationSharpRate

namespace QubitOracle.Paper

open Filter Matrix
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 800000

/-- The exact normalized Fisher average over the flattened implemented shots. -/
def prespecifiedBatchImplementedShotFisherAverage
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    (prespecifiedBatchTotalObservations K : Real)⁻¹ *
      ∑ s : PrespecifiedBatchEstimatorShotIndex K,
        prespecifiedBatchAxisFisherEntry x
          (prespecifiedBatchEstimatorShotAxis K b omega s) i j

/-- Flattening does not change the implemented normalized information. -/
theorem prespecifiedBatchImplementedShotFisherAverage_eq
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    prespecifiedBatchImplementedShotFisherAverage K b x omega =
      fun i j => (prespecifiedBatchTotalObservations K : Real)⁻¹ *
        prespecifiedBatchInformation K b x omega i j := by
  classical
  ext i j
  unfold prespecifiedBatchImplementedShotFisherAverage
    prespecifiedBatchInformation prespecifiedBatchPilotInformation
    prespecifiedBatchFinalInformation
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  unfold prespecifiedBatchEstimatorShotAxis
  ring

/-- Equality with the normalized information consumed by the corrected
estimator.  Every Fisher contribution is evaluated at the safe pilot. -/
theorem prespecifiedBatchImplementedShotFisherAverage_safe_eq_normalizedInformation
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    prespecifiedBatchImplementedShotFisherAverage K b
        (prespecifiedBatchSafeEvaluationPilot K omega) omega =
      prespecifiedBatchNormalizedInformation K b omega := by
  rw [prespecifiedBatchImplementedShotFisherAverage_eq]
  rfl

/-- The flattened dependent shot type has exactly the protocol sample count. -/
theorem prespecifiedBatchEstimatorShotIndex_card (K : Nat) :
    Fintype.card (PrespecifiedBatchEstimatorShotIndex K) =
      prespecifiedBatchTotalObservations K := by
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  unfold prespecifiedBatchTotalObservations
  unfold PureMultilevelSequentialBatchAdaptive.cumulativeCount
  rw [← Fin.sum_univ_eq_sum_range exactConcreteBatchSize K]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [exactConcreteBatchSize_decompose]
  unfold exactConcreteBatchExplorationSize
  ring

/-! ## Quantitative row-controller schedule -/

/-- A summable-Hoeffding-compatible row-controller envelope.  Its exponent
`11/8` is strictly larger than the `5/4` scale carried by the pooled pilot in
the Newton product. -/
noncomputable def prespecifiedBatchRowControllerDelta (k : Nat) : Real :=
  Real.rpow ((k : Real) + 1) (-(11 / 8 : Real))

theorem prespecifiedBatchRowControllerDelta_pos (k : Nat) :
    0 < prespecifiedBatchRowControllerDelta k := by
  unfold prespecifiedBatchRowControllerDelta
  exact Real.rpow_pos_of_pos (by positivity) _

theorem prespecifiedBatchRowControllerDelta_sq (k : Nat) :
    prespecifiedBatchRowControllerDelta k ^ 2 =
      Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) := by
  unfold prespecifiedBatchRowControllerDelta
  calc
    Real.rpow ((k : Real) + 1) (-(11 / 8 : Real)) ^ 2 =
        Real.rpow ((k : Real) + 1) (-(11 / 8 : Real) * 2) :=
      (Real.rpow_mul_natCast (by positivity)
        (-(11 / 8 : Real)) 2).symm
    _ = Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) := by norm_num

/-- The literal cubic row-pilot schedule dominates `27 (k+1)^3`. -/
theorem exactConcreteBatchPilotBlocks_ge_twentySeven_cube (k : Nat) :
    27 * ((k : Real) + 1) ^ 3 <=
      (exactConcreteBatchPilotBlocks k : Real) := by
  unfold exactConcreteBatchPilotBlocks
  push_cast
  have hk : 0 <= (k : Real) := by positivity
  nlinarith [sq_nonneg (k : Real),
    mul_nonneg hk (sq_nonneg (k : Real))]

/-- Exact schedule calculation behind the proposed `11/8` envelope: the
Hoeffding exponent grows at least as `27 (k+1)^(1/4)`. -/
theorem exactConcreteBatchPilot_rowControllerExponent_lower (k : Nat) :
    27 * Real.rpow ((k : Real) + 1) (1 / 4 : Real) <=
      (exactConcreteBatchPilotBlocks k : Real) *
        prespecifiedBatchRowControllerDelta k ^ 2 := by
  rw [prespecifiedBatchRowControllerDelta_sq]
  have hx : 0 < (k : Real) + 1 := by positivity
  have hpow : 0 <=
      Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) :=
    Real.rpow_nonneg hx.le _
  calc
    27 * Real.rpow ((k : Real) + 1) (1 / 4 : Real) =
        (27 * ((k : Real) + 1) ^ 3) *
          Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) := by
      symm
      calc
        (27 * ((k : Real) + 1) ^ 3) *
            Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) =
          27 * (Real.rpow ((k : Real) + 1) (3 : Real) *
            Real.rpow ((k : Real) + 1) (-(11 / 4 : Real))) := by
              have hnat : ((k : Real) + 1) ^ (3 : Nat) =
                  Real.rpow ((k : Real) + 1) (3 : Real) :=
                (Real.rpow_natCast ((k : Real) + 1) 3).symm
              rw [hnat]
              ring
        _ = 27 * Real.rpow ((k : Real) + 1)
            ((3 : Real) + (-(11 / 4 : Real))) := by
          congr 1
          exact (Real.rpow_add hx (3 : Real) (-(11 / 4 : Real))).symm
        _ = 27 * Real.rpow ((k : Real) + 1) (1 / 4 : Real) := by
          norm_num
    _ <= (exactConcreteBatchPilotBlocks k : Real) *
          Real.rpow ((k : Real) + 1) (-(11 / 4 : Real)) :=
      mul_le_mul_of_nonneg_right
        (exactConcreteBatchPilotBlocks_ge_twentySeven_cube k) hpow

/-- The actual finite-row Hoeffding tail is bounded by a stretched exponential
with the exact quarter-power exponent supplied by the cubic pilot schedule. -/
theorem exactConcreteBatchPilot_rowControllerHoeffdingEnvelope_le (k : Nat) :
    pauliPilotCoordinateHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k)
        (prespecifiedBatchRowControllerDelta k) <=
      2 * ENNReal.ofReal
        (Real.exp (-(27 / 2 : Real) *
          Real.rpow ((k : Real) + 1) (1 / 4 : Real))) := by
  unfold pauliPilotCoordinateHoeffdingEnvelope
  rw [Nat.succ_eq_add_one, exactConcreteBatchPilotIndex_succ]
  gcongr
  have h := exactConcreteBatchPilot_rowControllerExponent_lower k
  nlinarith

/-- The exponent gap is concrete: multiplying the row-controller envelope by
the pooled-pilot Newton scale `(K+1)^(5/4)` leaves `(K+1)^(-1/8)`, hence zero. -/
theorem prespecifiedBatchRowControllerDelta_mul_fiveQuarter_tendsto_zero :
    Tendsto
      (fun K : Nat =>
        Real.rpow ((K : Real) + 1) (5 / 4 : Real) *
          prespecifiedBatchRowControllerDelta K)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun K : Nat => (K : Real) + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro a
    filter_upwards
      [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with K hK
    linarith
  have hneg : Tendsto
      (fun K : Nat => Real.rpow ((K : Real) + 1) (-(1 / 8 : Real)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : Real) < 1 / 8)).comp hbase
  convert hneg using 1
  funext K
  unfold prespecifiedBatchRowControllerDelta
  have hx : 0 < (K : Real) + 1 := by positivity
  calc
    Real.rpow ((K : Real) + 1) (5 / 4 : Real) *
        Real.rpow ((K : Real) + 1) (-(11 / 8 : Real)) =
      Real.rpow ((K : Real) + 1)
        ((5 / 4 : Real) + (-(11 / 8 : Real))) :=
      (Real.rpow_add hx (5 / 4 : Real) (-(11 / 8 : Real))).symm
    _ = Real.rpow ((K : Real) + 1) (-(1 / 8 : Real)) := by norm_num

/-- Coordinatewise control gives a three-dimensional overlap bound. -/
theorem prespecifiedBatch_blochDot_sub_abs_le_three
    (x z axis : RLSVector 3) (eta : Real)
    (heta : 0 <= eta)
    (hcoord : forall k : Fin 3, |x k - z k| <= eta)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    |QubitOracle.blochDot x axis - QubitOracle.blochDot z axis| <= 3 * eta := by
  have haxisCoord (k : Fin 3) : |axis k| <= 1 :=
    unitBlochAxis_coordinate_abs_le_one axis haxis k
  have hterm (k : Fin 3) : |(x k - z k) * axis k| <= eta := by
    rw [abs_mul]
    calc
      |x k - z k| * |axis k| <= eta * |axis k| :=
        mul_le_mul_of_nonneg_right (hcoord k) (abs_nonneg _)
      _ <= eta * 1 := mul_le_mul_of_nonneg_left (haxisCoord k) heta
      _ = eta := mul_one eta
  have hdot : QubitOracle.blochDot x axis - QubitOracle.blochDot z axis =
      ∑ k : Fin 3, (x k - z k) * axis k := by
    unfold QubitOracle.blochDot
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hdot, Fin.sum_univ_three]
  calc
    |(x 0 - z 0) * axis 0 + (x 1 - z 1) * axis 1 +
        (x 2 - z 2) * axis 2| <=
        |(x 0 - z 0) * axis 0| + |(x 1 - z 1) * axis 1| +
        |(x 2 - z 2) * axis 2| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ <= eta + eta + eta :=
      add_le_add (add_le_add (hterm 0) (hterm 1)) (hterm 2)
    _ = 3 * eta := by ring

/-- Exact denominator algebra for one Fisher entry. -/
theorem prespecifiedBatchAxisFisherEntry_sub_exact
    (x z axis : RLSVector 3) (i j : Fin 3)
    (hx : 1 - QubitOracle.blochDot x axis ^ 2 ≠ 0)
    (hz : 1 - QubitOracle.blochDot z axis ^ 2 ≠ 0) :
    prespecifiedBatchAxisFisherEntry x axis i j -
        prespecifiedBatchAxisFisherEntry z axis i j =
      axis i * axis j *
        (QubitOracle.blochDot x axis ^ 2 -
          QubitOracle.blochDot z axis ^ 2) /
        ((1 - QubitOracle.blochDot x axis ^ 2) *
          (1 - QubitOracle.blochDot z axis ^ 2)) := by
  unfold prespecifiedBatchAxisFisherEntry
  field_simp [hx, hz]
  ring

/-- Uniform fixed-interior Lipschitz bound for every Fisher entry. -/
theorem prespecifiedBatchAxisFisherEntry_sub_abs_le
    (x z axis : RLSVector 3) (i j : Fin 3)
    (floor eta : Real)
    (hfloor : 0 < floor) (heta : 0 <= eta)
    (haxis : QubitOracle.blochNormSq axis = 1)
    (hcoord : forall k : Fin 3, |x k - z k| <= eta)
    (hxAbs : |QubitOracle.blochDot x axis| <= 1)
    (hzAbs : |QubitOracle.blochDot z axis| <= 1)
    (hxFloor : floor <= 1 - QubitOracle.blochDot x axis ^ 2)
    (hzFloor : floor <= 1 - QubitOracle.blochDot z axis ^ 2) :
    |prespecifiedBatchAxisFisherEntry x axis i j -
        prespecifiedBatchAxisFisherEntry z axis i j| <=
      6 * eta / floor ^ 2 := by
  have hxPos : 0 < 1 - QubitOracle.blochDot x axis ^ 2 :=
    lt_of_lt_of_le hfloor hxFloor
  have hzPos : 0 < 1 - QubitOracle.blochDot z axis ^ 2 :=
    lt_of_lt_of_le hfloor hzFloor
  rw [prespecifiedBatchAxisFisherEntry_sub_exact x z axis i j
    (ne_of_gt hxPos) (ne_of_gt hzPos)]
  rw [abs_div, abs_mul, abs_mul, abs_mul,
    abs_of_pos hxPos, abs_of_pos hzPos]
  have hi := unitBlochAxis_coordinate_abs_le_one axis haxis i
  have hj := unitBlochAxis_coordinate_abs_le_one axis haxis j
  have hdot := prespecifiedBatch_blochDot_sub_abs_le_three
    x z axis eta heta hcoord haxis
  have hsum : |QubitOracle.blochDot x axis +
      QubitOracle.blochDot z axis| <= 2 := by
    calc
      |_ + _| <= |QubitOracle.blochDot x axis| +
          |QubitOracle.blochDot z axis| := abs_add_le _ _
      _ <= 1 + 1 := add_le_add hxAbs hzAbs
      _ = 2 := by norm_num
  have hsq : |QubitOracle.blochDot x axis ^ 2 -
      QubitOracle.blochDot z axis ^ 2| <= 6 * eta := by
    rw [show QubitOracle.blochDot x axis ^ 2 -
        QubitOracle.blochDot z axis ^ 2 =
      (QubitOracle.blochDot x axis - QubitOracle.blochDot z axis) *
        (QubitOracle.blochDot x axis + QubitOracle.blochDot z axis) by ring,
      abs_mul]
    calc
      |_ - _| * |_ + _| <= (3 * eta) * 2 := by gcongr
      _ = 6 * eta := by ring
  calc
    |axis i| * |axis j| *
          |QubitOracle.blochDot x axis ^ 2 -
            QubitOracle.blochDot z axis ^ 2| /
        ((1 - QubitOracle.blochDot x axis ^ 2) *
          (1 - QubitOracle.blochDot z axis ^ 2)) <=
      1 * 1 * (6 * eta) / (floor * floor) := by
        gcongr
    _ = 6 * eta / floor ^ 2 := by ring

/-- Uniform Fisher continuity after averaging all implemented shots. -/
theorem prespecifiedBatchImplementedShotFisherAverage_sub_abs_le
    (K : Nat) (b x z : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (i j : Fin 3) (floor eta : Real)
    (hN : 0 < prespecifiedBatchTotalObservations K)
    (hfloor : 0 < floor) (heta : 0 <= eta)
    (hcoord : forall k : Fin 3, |x k - z k| <= eta)
    (hAbs : forall s : PrespecifiedBatchEstimatorShotIndex K,
      |QubitOracle.blochDot x
        (prespecifiedBatchEstimatorShotAxis K b omega s)| <= 1 ∧
      |QubitOracle.blochDot z
        (prespecifiedBatchEstimatorShotAxis K b omega s)| <= 1)
    (hFloor : forall s : PrespecifiedBatchEstimatorShotIndex K,
      floor <= 1 - QubitOracle.blochDot x
        (prespecifiedBatchEstimatorShotAxis K b omega s) ^ 2 ∧
      floor <= 1 - QubitOracle.blochDot z
        (prespecifiedBatchEstimatorShotAxis K b omega s) ^ 2) :
    |prespecifiedBatchImplementedShotFisherAverage K b x omega i j -
        prespecifiedBatchImplementedShotFisherAverage K b z omega i j| <=
      6 * eta / floor ^ 2 := by
  unfold prespecifiedBatchImplementedShotFisherAverage
  rw [← mul_sub]
  rw [← Finset.sum_sub_distrib]
  rw [abs_mul, abs_inv]
  have hsum : |∑ s : PrespecifiedBatchEstimatorShotIndex K,
      (prespecifiedBatchAxisFisherEntry x
          (prespecifiedBatchEstimatorShotAxis K b omega s) i j -
        prespecifiedBatchAxisFisherEntry z
          (prespecifiedBatchEstimatorShotAxis K b omega s) i j)| <=
      Fintype.card (PrespecifiedBatchEstimatorShotIndex K) *
        (6 * eta / floor ^ 2) := by
    calc
      |∑ s : PrespecifiedBatchEstimatorShotIndex K, _| <=
          ∑ s : PrespecifiedBatchEstimatorShotIndex K,
            |prespecifiedBatchAxisFisherEntry x
                (prespecifiedBatchEstimatorShotAxis K b omega s) i j -
              prespecifiedBatchAxisFisherEntry z
                (prespecifiedBatchEstimatorShotAxis K b omega s) i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _s : PrespecifiedBatchEstimatorShotIndex K,
          (6 * eta / floor ^ 2) := by
        gcongr with s
        exact prespecifiedBatchAxisFisherEntry_sub_abs_le x z _ i j floor eta
          hfloor heta (prespecifiedBatchEstimatorShotAxis_unit K b omega s)
          hcoord (hAbs s).1 (hAbs s).2 (hFloor s).1 (hFloor s).2
      _ = Fintype.card (PrespecifiedBatchEstimatorShotIndex K) *
          (6 * eta / floor ^ 2) := by simp
  rw [prespecifiedBatchEstimatorShotIndex_card] at hsum
  have hNreal : (0 : Real) < prespecifiedBatchTotalObservations K := by
    exact_mod_cast hN
  rw [abs_of_pos hNreal]
  calc
    (prespecifiedBatchTotalObservations K : Real)⁻¹ * |∑ s, _| <=
        (prespecifiedBatchTotalObservations K : Real)⁻¹ *
          ((prespecifiedBatchTotalObservations K : Real) *
            (6 * eta / floor ^ 2)) := by gcongr
    _ = 6 * eta / floor ^ 2 := by field_simp

/-! ## Exact information-defect decomposition -/

/-- Term (i): changing only the Fisher evaluation point while retaining the
same realized axes. -/
def prespecifiedBatchFisherEvaluationDefect
    (K : Nat) (b x theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  prespecifiedBatchImplementedShotFisherAverage K b x omega -
    prespecifiedBatchImplementedShotFisherAverage K b theta omega

/-- Term (ii): truth-evaluated conditional Fisher for the selected axes minus
the deterministic Bures target.  This is precisely the controller term. -/
def prespecifiedBatchControllerFisherDefect
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  prespecifiedBatchImplementedShotFisherAverage K b theta omega -
    mixedBuresTarget theta

/-- Term (iii): conditional Fisher at the truth minus the outcome-dependent
truth-observed information matrix. -/
def prespecifiedBatchOutcomeHessianDefect
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  prespecifiedBatchImplementedShotFisherAverage K b theta omega -
    prespecifiedBatchTruthObservedInformationMatrix theta b K
      (prespecifiedBatchEstimatorPrefixToFinitePrefix K omega)

/-- The target-to-observed bridge that relates the controller and Hessian
decompositions without double-counting truth Fisher. -/
def prespecifiedBatchTargetToObservedDefect
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  mixedBuresTarget theta -
    prespecifiedBatchTruthObservedInformationMatrix theta b K
      (prespecifiedBatchEstimatorPrefixToFinitePrefix K omega)

/-- Controller defect plus target-to-observed defect is exactly the
conditional-Fisher minus observed-Hessian defect. -/
theorem prespecifiedBatchOutcomeHessianDefect_eq_controller_add_targetToObserved
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    prespecifiedBatchOutcomeHessianDefect K theta b omega =
      prespecifiedBatchControllerFisherDefect K theta b omega +
        prespecifiedBatchTargetToObservedDefect K theta b omega := by
  unfold prespecifiedBatchOutcomeHessianDefect
    prespecifiedBatchControllerFisherDefect
    prespecifiedBatchTargetToObservedDefect
  abel

/-- Exact target-information identity: terms (i), (ii), and (iv). -/
theorem prespecifiedBatchRegularizedInformation_sub_target_decomposition
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K) - mixedBuresTarget theta =
      prespecifiedBatchFisherEvaluationDefect K b
          (prespecifiedBatchSafeEvaluationPilot K omega) theta omega +
        prespecifiedBatchControllerFisherDefect K theta b omega +
        prespecifiedBatchRidge K • (1 : Matrix (Fin 3) (Fin 3) Real) := by
  rw [← prespecifiedBatchImplementedShotFisherAverage_safe_eq_normalizedInformation]
  unfold regularizedNormalizedInformation
    prespecifiedBatchFisherEvaluationDefect
    prespecifiedBatchControllerFisherDefect
  abel

/-- Exact Newton-information identity: terms (i), (iii), and (iv). -/
theorem prespecifiedBatchRegularizedInformation_sub_observed_decomposition
    (K : Nat) (theta b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K) -
        prespecifiedBatchTruthObservedInformationMatrix theta b K
          (prespecifiedBatchEstimatorPrefixToFinitePrefix K omega) =
      prespecifiedBatchFisherEvaluationDefect K b
          (prespecifiedBatchSafeEvaluationPilot K omega) theta omega +
        prespecifiedBatchOutcomeHessianDefect K theta b omega +
        prespecifiedBatchRidge K • (1 : Matrix (Fin 3) (Fin 3) Real) := by
  rw [← prespecifiedBatchImplementedShotFisherAverage_safe_eq_normalizedInformation]
  unfold regularizedNormalizedInformation
    prespecifiedBatchFisherEvaluationDefect
    prespecifiedBatchOutcomeHessianDefect
  abel

/-! ## Deterministic quadratic score remainder -/

/-- One Bernoulli score remainder is quadratically bounded on a common
denominator floor. -/
theorem prespecifiedBatchBernoulliQuadraticRemainder_abs_le
    (z d : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (floor : Real) (hfloor : 0 < floor)
    (haxis : QubitOracle.blochNormSq axis = 1)
    (hzFloor : floor <=
      |1 + pauliOutcomeSign outcome * z|)
    (hzdFloor : floor <=
      |1 + pauliOutcomeSign outcome * (z + d)|) :
    |pauliOutcomeSign outcome * axis i * d ^ 2 /
        ((1 + pauliOutcomeSign outcome * (z + d)) *
          (1 + pauliOutcomeSign outcome * z) ^ 2)| <=
      d ^ 2 / floor ^ 3 := by
  have hsign : |pauliOutcomeSign outcome| = 1 := by
    cases outcome <;> norm_num [pauliOutcomeSign]
  have haxisCoord : |axis i| <= 1 :=
    unitBlochAxis_coordinate_abs_le_one axis haxis i
  have hnum : |pauliOutcomeSign outcome * axis i * d ^ 2| <= d ^ 2 := by
    rw [abs_mul, abs_mul, hsign, one_mul, abs_pow, sq_abs]
    calc
      |axis i| * d ^ 2 <= 1 * d ^ 2 :=
        mul_le_mul_of_nonneg_right haxisCoord (sq_nonneg d)
      _ = d ^ 2 := one_mul _
  have hden : floor ^ 3 <=
      |(1 + pauliOutcomeSign outcome * (z + d)) *
        (1 + pauliOutcomeSign outcome * z) ^ 2| := by
    rw [abs_mul, abs_pow]
    calc
      floor ^ 3 = floor * floor ^ 2 := by ring
      _ <= |1 + pauliOutcomeSign outcome * (z + d)| * floor ^ 2 :=
        mul_le_mul_of_nonneg_right hzdFloor (sq_nonneg floor)
      _ <= |1 + pauliOutcomeSign outcome * (z + d)| *
          |1 + pauliOutcomeSign outcome * z| ^ 2 := by
        gcongr
  have hdenPos : 0 <
      |(1 + pauliOutcomeSign outcome * (z + d)) *
        (1 + pauliOutcomeSign outcome * z) ^ 2| :=
    lt_of_lt_of_le (pow_pos hfloor 3) hden
  rw [abs_div]
  apply (div_le_div_iff₀ hdenPos (pow_pos hfloor 3)).2
  calc
    |pauliOutcomeSign outcome * axis i * d ^ 2| * floor ^ 3 <=
        d ^ 2 * floor ^ 3 :=
      mul_le_mul_of_nonneg_right hnum (pow_pos hfloor 3).le
    _ <= d ^ 2 *
        |(1 + pauliOutcomeSign outcome * (z + d)) *
          (1 + pauliOutcomeSign outcome * z) ^ 2| :=
      mul_le_mul_of_nonneg_left hden (sq_nonneg d)

/-- Literal sum of the exact per-shot quadratic score remainders. -/
def prespecifiedBatchScoreQuadraticRemainder
    (K : Nat) (theta b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3) : Real :=
  ∑ s : PrespecifiedBatchEstimatorShotIndex K,
    pauliOutcomeSign
        (prespecifiedBatchEstimatorShotOutcome K omega s) *
      prespecifiedBatchEstimatorShotAxis K b omega s i *
      QubitOracle.blochDot (fun j => x j - theta j)
          (prespecifiedBatchEstimatorShotAxis K b omega s) ^ 2 /
    ((1 + pauliOutcomeSign
          (prespecifiedBatchEstimatorShotOutcome K omega s) *
        (QubitOracle.blochDot theta
            (prespecifiedBatchEstimatorShotAxis K b omega s) +
          QubitOracle.blochDot (fun j => x j - theta j)
            (prespecifiedBatchEstimatorShotAxis K b omega s))) *
      (1 + pauliOutcomeSign
          (prespecifiedBatchEstimatorShotOutcome K omega s) *
        QubitOracle.blochDot theta
          (prespecifiedBatchEstimatorShotAxis K b omega s)) ^ 2)

/-- Every exact prefix has a uniform all-shot quadratic remainder bound. -/
theorem prespecifiedBatchScoreQuadraticRemainder_abs_le
    (K : Nat) (theta b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3)
    (floor : Real) (hfloor : 0 < floor)
    (hTruthFloor : forall s : PrespecifiedBatchEstimatorShotIndex K,
      floor <=
        |1 + pauliOutcomeSign
            (prespecifiedBatchEstimatorShotOutcome K omega s) *
          QubitOracle.blochDot theta
            (prespecifiedBatchEstimatorShotAxis K b omega s)|)
    (hSegmentFloor : forall s : PrespecifiedBatchEstimatorShotIndex K,
      floor <=
        |1 + pauliOutcomeSign
            (prespecifiedBatchEstimatorShotOutcome K omega s) *
          (QubitOracle.blochDot theta
              (prespecifiedBatchEstimatorShotAxis K b omega s) +
            QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s))|) :
    |prespecifiedBatchScoreQuadraticRemainder K theta b x omega i| <=
      (prespecifiedBatchTotalObservations K : Real) *
        (QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3) := by
  classical
  unfold prespecifiedBatchScoreQuadraticRemainder
  calc
    |∑ s : PrespecifiedBatchEstimatorShotIndex K, _| <=
        ∑ s : PrespecifiedBatchEstimatorShotIndex K,
          |pauliOutcomeSign
                (prespecifiedBatchEstimatorShotOutcome K omega s) *
              prespecifiedBatchEstimatorShotAxis K b omega s i *
              QubitOracle.blochDot (fun j => x j - theta j)
                  (prespecifiedBatchEstimatorShotAxis K b omega s) ^ 2 /
            ((1 + pauliOutcomeSign
                  (prespecifiedBatchEstimatorShotOutcome K omega s) *
                (QubitOracle.blochDot theta
                    (prespecifiedBatchEstimatorShotAxis K b omega s) +
                  QubitOracle.blochDot (fun j => x j - theta j)
                    (prespecifiedBatchEstimatorShotAxis K b omega s))) *
              (1 + pauliOutcomeSign
                  (prespecifiedBatchEstimatorShotOutcome K omega s) *
                QubitOracle.blochDot theta
                  (prespecifiedBatchEstimatorShotAxis K b omega s)) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _s : PrespecifiedBatchEstimatorShotIndex K,
        (QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3) := by
      apply Finset.sum_le_sum
      intro s hs
      have hone := prespecifiedBatchBernoulliQuadraticRemainder_abs_le
        (QubitOracle.blochDot theta
          (prespecifiedBatchEstimatorShotAxis K b omega s))
        (QubitOracle.blochDot (fun j => x j - theta j)
          (prespecifiedBatchEstimatorShotAxis K b omega s))
        (prespecifiedBatchEstimatorShotAxis K b omega s)
        (prespecifiedBatchEstimatorShotOutcome K omega s) i floor hfloor
        (prespecifiedBatchEstimatorShotAxis_unit K b omega s)
        (hTruthFloor s) (hSegmentFloor s)
      have hcauchy := QubitOracle.bloch_cauchy_schwarz
        (fun j => x j - theta j)
        (prespecifiedBatchEstimatorShotAxis K b omega s)
      rw [prespecifiedBatchEstimatorShotAxis_unit K b omega s, mul_one] at hcauchy
      exact hone.trans (div_le_div_of_nonneg_right hcauchy (pow_pos hfloor 3).le)
    _ = (prespecifiedBatchTotalObservations K : Real) *
        (QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ,
        prespecifiedBatchEstimatorShotIndex_card]

/-- After score normalization, the deterministic quadratic remainder has the
root-sample-size envelope used by the Newton argument. -/
theorem prespecifiedBatchNormalizedScoreQuadraticRemainder_abs_le
    (K : Nat) (hK : 0 < K) (theta b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3)
    (floor : Real) (hfloor : 0 < floor)
    (hTruthFloor : forall s : PrespecifiedBatchEstimatorShotIndex K,
      floor <=
        |1 + pauliOutcomeSign
            (prespecifiedBatchEstimatorShotOutcome K omega s) *
          QubitOracle.blochDot theta
            (prespecifiedBatchEstimatorShotAxis K b omega s)|)
    (hSegmentFloor : forall s : PrespecifiedBatchEstimatorShotIndex K,
      floor <=
        |1 + pauliOutcomeSign
            (prespecifiedBatchEstimatorShotOutcome K omega s) *
          (QubitOracle.blochDot theta
              (prespecifiedBatchEstimatorShotAxis K b omega s) +
            QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s))|) :
    |(prespecifiedBatchSampleScale K)⁻¹ *
        prespecifiedBatchScoreQuadraticRemainder K theta b x omega i| <=
      prespecifiedBatchSampleScale K *
        QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3 := by
  have hscalePos : 0 < prespecifiedBatchSampleScale K := by
    rw [prespecifiedBatchSampleScale_eq]
    positivity
  rw [abs_mul, abs_inv, abs_of_pos hscalePos]
  have hrem := prespecifiedBatchScoreQuadraticRemainder_abs_le
    K theta b x omega i floor hfloor hTruthFloor hSegmentFloor
  calc
    (prespecifiedBatchSampleScale K)⁻¹ *
        |prespecifiedBatchScoreQuadraticRemainder K theta b x omega i| <=
      (prespecifiedBatchSampleScale K)⁻¹ *
        ((prespecifiedBatchTotalObservations K : Real) *
          (QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3)) :=
      mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr hscalePos.le)
    _ = prespecifiedBatchSampleScale K *
        QubitOracle.blochNormSq (fun j => x j - theta j) / floor ^ 3 := by
      rw [prespecifiedBatchSampleScale_eq, prespecifiedBatchTotalObservations_eq]
      push_cast
      field_simp
      ring

/-! ## Sharp observed-Hessian input and exact estimator algebra -/

/-- Gauss's term (iii), named as the final-row conditional-Fisher minus
outcome-Hessian defect. -/
abbrev prespecifiedBatchFinalOutcomeHessianDefect :=
  prespecifiedBatchShotInformationMatrixError

/-- The sharp full-matrix L2 inequality imported from the concrete martingale
proof. -/
theorem prespecifiedBatchFinalOutcomeHessianDefect_frobeniusSq_integral_le
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    (∫ omega,
      prespecifiedBatchShotInformationMatrixErrorSq
        theta b hInterior K omega
      ∂exactConcretePredeterminedBatchPathMeasure theta b
        (le_of_lt hInterior)) <=
      prespecifiedBatchObservedInformationMatrixSharpConstant theta /
        (prespecifiedBatchTotalObservations K : Real) :=
  prespecifiedBatchShotInformationMatrixErrorSq_integral_le
    theta b hInterior K

/-- The sharp L2 Hessian rate remains negligible after multiplication by the
`K`-order pilot-error envelope used in the Newton product. -/
theorem prespecifiedBatchFinalOutcomeHessianDefect_pilotOrder_l2_tendsto_zero
    (theta : RLSVector 3) :
    Tendsto
      (fun K : Nat =>
        (K : Real) ^ 2 *
          (prespecifiedBatchObservedInformationMatrixSharpConstant theta /
            (prespecifiedBatchTotalObservations K : Real)))
      atTop (nhds 0) :=
  prespecifiedBatch_pilotOrderK_matrixError_l2_bound_tendsto_zero theta

/-- Exact asymptotic-linearity identity for the raw implemented estimator.
No positivity premise remains: the safe Fisher matrix plus positive ridge is
positive definite for every finite prefix. -/
theorem prespecifiedBatchRawEstimator_exact_asymptoticLinearityIdentity
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (centralScore : LANParameter (Fin 3)) :
    prespecifiedBatchRawNormalizedError K b theta omega -
        lanMatrixAction
          (regularizedNormalizedInformation
            (prespecifiedBatchNormalizedInformation K b omega)
            (prespecifiedBatchRidge K))⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K))⁻¹
        (normalizedNewtonDefect
          (prespecifiedBatchLANVector fun i =>
            prespecifiedBatchSampleScale K *
              (prespecifiedBatchPooledPilot K omega i - theta i))
          (prespecifiedBatchNormalizedScore K b omega) centralScore
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K)) :=
  prespecifiedBatchRawNormalizedError_exact_unconditional
    K b theta omega centralScore

/-- Whenever radial clipping is inactive, the concrete physical estimator has
the same exact normalized Newton identity as the raw one-step update. -/
theorem prespecifiedBatchProjectedEstimator_exact_asymptoticLinearityIdentity_of_rawPhysical
    (K : Nat) (hK : 0 < K) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (centralScore : LANParameter (Fin 3))
    (hphysical : QubitOracle.blochNormSq
      (prespecifiedBatchRawOneStepEstimator K b omega) <= 1) :
    (prespecifiedBatchLANVector fun i =>
        prespecifiedBatchSampleScale K *
          (prespecifiedBatchProjectedOneStepEstimator K b omega i - theta i)) -
        lanMatrixAction
          (regularizedNormalizedInformation
            (prespecifiedBatchNormalizedInformation K b omega)
            (prespecifiedBatchRidge K))⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K))⁻¹
        (normalizedNewtonDefect
          (prespecifiedBatchLANVector fun i =>
            prespecifiedBatchSampleScale K *
              (prespecifiedBatchPooledPilot K omega i - theta i))
          (prespecifiedBatchNormalizedScore K b omega) centralScore
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K)) := by
  rw [prespecifiedBatchProjectedOneStepEstimator_eq_raw_of_physical
    K b omega hphysical]
  rw [prespecifiedBatchRawOneStepEstimator_scaledError K b theta omega]
  · exact prespecifiedBatchRawEstimator_exact_asymptoticLinearityIdentity
      K b theta omega centralScore
  · rw [prespecifiedBatchSampleScale_eq]
    positivity

/-- Joint continuity of ridge-regularized matrix inversion at a positive-definite target. -/
theorem regularizedInformationInverse_continuousAt
    (M : Matrix (Fin 3) (Fin 3) Real) (hM : M.PosDef) :
    ContinuousAt
      (fun p : Matrix (Fin 3) (Fin 3) Real × Real =>
        (regularizedNormalizedInformation p.1 p.2)⁻¹)
      (M, 0) := by
  have hdetUnit : IsUnit M.det :=
    (M.isUnit_iff_isUnit_det).mp hM.isUnit
  have hscalarInverse : ContinuousAt Ring.inverse M.det := by
    simpa only [hdetUnit.unit_spec] using
      NormedRing.inverse_continuousAt hdetUnit.unit
  have hinv : ContinuousAt
      (fun A : Matrix (Fin 3) (Fin 3) Real => A⁻¹) M :=
    continuousAt_matrix_inv M hscalarInverse
  have hreg : ContinuousAt
      (fun p : Matrix (Fin 3) (Fin 3) Real × Real =>
        regularizedNormalizedInformation p.1 p.2) (M, 0) := by
    unfold regularizedNormalizedInformation
    fun_prop
  have hzero : regularizedNormalizedInformation M 0 = M := by
    simp [regularizedNormalizedInformation]
  have hinv' : ContinuousAt
      (fun A : Matrix (Fin 3) (Fin 3) Real => A⁻¹)
      (regularizedNormalizedInformation M 0) := by
    rw [hzero]
    exact hinv
  simpa [Function.comp_def] using
    (ContinuousAt.comp
      (x := (M, 0))
      (f := fun p : Matrix (Fin 3) (Fin 3) Real × Real =>
        regularizedNormalizedInformation p.1 p.2)
      (g := fun A : Matrix (Fin 3) (Fin 3) Real => A⁻¹)
      hinv' hreg)

/-- Sequential form consumed once stochastic matrix and ridge convergence land. -/
theorem regularizedInformationInverse_tendsto
    {I : Type} {l : Filter I}
    (A : I -> Matrix (Fin 3) (Fin 3) Real) (ridge : I -> Real)
    (M : Matrix (Fin 3) (Fin 3) Real) (hM : M.PosDef)
    (hA : Tendsto A l (nhds M)) (hridge : Tendsto ridge l (nhds 0)) :
    Tendsto (fun n => (regularizedNormalizedInformation (A n) (ridge n))⁻¹)
      l (nhds M⁻¹) := by
  have hp : Tendsto (fun n => (A n, ridge n)) l (nhds (M, 0)) :=
    hA.prodMk_nhds hridge
  have hlim :=
    (regularizedInformationInverse_continuousAt M hM).tendsto.comp hp
  have hzero : regularizedNormalizedInformation M 0 = M := by
    simp [regularizedNormalizedInformation]
  rw [hzero] at hlim
  change Tendsto
    ((fun p : Matrix (Fin 3) (Fin 3) Real × Real =>
        (regularizedNormalizedInformation p.1 p.2)⁻¹) ∘
      fun n => (A n, ridge n)) l (nhds M⁻¹)
  exact hlim

/-- Specialized inverse-continuity endpoint at the concrete Bures target. -/
theorem mixedBuresRegularizedInformationInverse_tendsto
    {I : Type} {l : Filter I}
    (A : I -> Matrix (Fin 3) (Fin 3) Real) (ridge : I -> Real)
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hA : Tendsto A l (nhds (mixedBuresTarget theta)))
    (hridge : Tendsto ridge l (nhds 0)) :
    Tendsto (fun n => (regularizedNormalizedInformation (A n) (ridge n))⁻¹)
      l (nhds ((mixedBuresTarget theta)⁻¹)) :=
  regularizedInformationInverse_tendsto A ridge (mixedBuresTarget theta)
    (mixedBuresTarget_posDef theta b hTruth hSeed) hA hridge

end

end QubitOracle.Paper
