import QubitOracle.Paper.OneQubitMixedFinalEstimatorFourthMoment
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw

open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory Filter Finset
open ProbabilityTheory

namespace QubitOracle.Paper

/- Keep the exact measurable-space instance used by the finite Born-product law. -/
local instance mixedCyclicPauliPathMeasurableSpace :
    MeasurableSpace (PauliPilotPath 1) :=
  pauliPilotBornPathMeasurableSpace 1

/-- Strict interior of the one-qubit Bloch ball. -/
def MixedCyclicPauliStrictInterior (theta : RLSVector 3) : Prop :=
  QubitOracle.blochNormSq theta < 1

/-- A strict-interior Bloch vector is a physical mixed qubit state. -/
theorem mixedCyclicPauliStrictInterior_physical
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    PauliPilotPhysicalBloch theta :=
  le_of_lt hInterior

/-- Every Pauli coordinate of a strict-interior Bloch vector lies strictly in `(-1,1)`. -/
theorem mixedCyclicPauliStrictInterior_coordinate_abs_lt_one
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    |theta j| < 1 := by
  have hj : theta j ^ 2 ≤ QubitOracle.blochNormSq theta := by
    unfold QubitOracle.blochNormSq
    exact Finset.single_le_sum (fun i _ => sq_nonneg (theta i)) (Finset.mem_univ j)
  have hsq : theta j ^ 2 < 1 := hj.trans_lt hInterior
  have habsSq : |theta j| ^ 2 < 1 := by simpa [sq_abs] using hsq
  nlinarith [abs_nonneg (theta j)]

/-- The Bernoulli variance denominator is positive in the strict interior. -/
theorem mixedCyclicPauli_varianceDenominator_pos
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    0 < 1 - theta j ^ 2 := by
  have h := mixedCyclicPauliStrictInterior_coordinate_abs_lt_one theta hInterior j
  have hsq : theta j ^ 2 < 1 := by nlinarith [le_abs_self (theta j), neg_le_abs (theta j)]
  linarith

/-- Exact three-axis Born-product law for one cycle. -/
noncomputable abbrev mixedCyclicPauliBlockMeasure (theta : RLSVector 3) :
    Measure (PauliPilotPath 1) :=
  pauliPilotBornProductMeasure (q := 1) theta

/-- Infinite iid sequence of three-shot Pauli cycles. -/
abbrev MixedCyclicPauliOmega := ℕ → PauliPilotPath 1

/-- Product law of the iid cyclic blocks. -/
noncomputable abbrev mixedCyclicPauliMeasure (theta : RLSVector 3) :
    Measure MixedCyclicPauliOmega :=
  Measure.infinitePi (fun _ : ℕ => mixedCyclicPauliBlockMeasure theta)

/-- Signed outcome on axis `j` in a single three-shot cycle. -/
def mixedCyclicPauliBlockCoordinate (j : Fin 3) (block : PauliPilotPath 1) : ℝ :=
  pauliOutcomeSign (block 0 j)

/-- Centered signed outcome on axis `j`. -/
def mixedCyclicPauliCenteredCoordinate
    (theta : RLSVector 3) (j : Fin 3) (block : PauliPilotPath 1) : ℝ :=
  mixedCyclicPauliBlockCoordinate j block - theta j

/-- Directional score coefficient per three-shot block, normalized by total shots `3q`. -/
noncomputable def mixedCyclicPauliScoreCoefficient
    (theta h : RLSVector 3) (j : Fin 3) : ℝ :=
  (Real.sqrt 3)⁻¹ * h j / (1 - theta j ^ 2)

/-- Scalar score in direction `h` contributed by one complete `X,Y,Z` cycle. -/
noncomputable def mixedCyclicPauliBlockScore
    (theta h : RLSVector 3) (block : PauliPilotPath 1) : ℝ :=
  mixedCyclicPauliScoreCoefficient theta h 0 * mixedCyclicPauliCenteredCoordinate theta 0 block +
  mixedCyclicPauliScoreCoefficient theta h 1 * mixedCyclicPauliCenteredCoordinate theta 1 block +
  mixedCyclicPauliScoreCoefficient theta h 2 * mixedCyclicPauliCenteredCoordinate theta 2 block

/-- Directional Fisher information per physical shot for the deterministic `X,Y,Z` cycle. -/
noncomputable def mixedCyclicPauliFisherQuadratic
    (theta h : RLSVector 3) : ℝ :=
  mixedCyclicPauliScoreCoefficient theta h 0 ^ 2 * (1 - theta 0 ^ 2) +
  mixedCyclicPauliScoreCoefficient theta h 1 ^ 2 * (1 - theta 1 ^ 2) +
  mixedCyclicPauliScoreCoefficient theta h 2 ^ 2 * (1 - theta 2 ^ 2)

/-- Paper form of the mixed-state cyclic Fisher information. -/
theorem mixedCyclicPauliFisherQuadratic_eq
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    mixedCyclicPauliFisherQuadratic theta h =
      (1 / 3 : ℝ) *
        (h 0 ^ 2 / (1 - theta 0 ^ 2) +
         h 1 ^ 2 / (1 - theta 1 ^ 2) +
         h 2 ^ 2 / (1 - theta 2 ^ 2)) := by
  have h0 := ne_of_gt (mixedCyclicPauli_varianceDenominator_pos theta hInterior 0)
  have h1 := ne_of_gt (mixedCyclicPauli_varianceDenominator_pos theta hInterior 1)
  have h2 := ne_of_gt (mixedCyclicPauli_varianceDenominator_pos theta hInterior 2)
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [mixedCyclicPauliFisherQuadratic, mixedCyclicPauliScoreCoefficient]
  field_simp [h0, h1, h2, hsqrt0]
  rw [hsqrt]
  ring

private theorem mixedCyclicFiniteExpectation_add
    {q : ℕ} (theta : RLSVector 3) (f g : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation theta (fun path => f path + g path) =
      pauliPilotFiniteExpectation theta f + pauliPilotFiniteExpectation theta g := by
  simp only [pauliPilotFiniteExpectation, mul_add, sum_add_distrib]

private theorem mixedCyclicFiniteExpectation_sub
    {q : ℕ} (theta : RLSVector 3) (f g : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation theta (fun path => f path - g path) =
      pauliPilotFiniteExpectation theta f - pauliPilotFiniteExpectation theta g := by
  simp only [pauliPilotFiniteExpectation, mul_sub, sum_sub_distrib]

private theorem mixedCyclicFiniteExpectation_const_mul
    {q : ℕ} (theta : RLSVector 3) (c : ℝ) (f : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation theta (fun path => c * f path) =
      c * pauliPilotFiniteExpectation theta f := by
  simp only [pauliPilotFiniteExpectation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path _
  ring

private theorem mixedCyclicFiniteExpectation_const
    {q : ℕ} (theta : RLSVector 3) (c : ℝ) :
    pauliPilotFiniteExpectation theta (fun _ : PauliPilotPath q => c) = c := by
  simp only [pauliPilotFiniteExpectation]
  rw [← Finset.sum_mul, pauliPilotPathMass_sum_one]
  simp

private theorem mixedCyclicPauliBlockCoordinate_finiteMean
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    pauliPilotFiniteExpectation (q := 1) theta (mixedCyclicPauliBlockCoordinate j) = theta j := by
  calc
    pauliPilotFiniteExpectation (q := 1) theta (mixedCyclicPauliBlockCoordinate j) =
        ∫ block, mixedCyclicPauliBlockCoordinate j block
          ∂pauliPilotBornProductMeasure (q := 1) theta := by
      symm
      simpa [pauliPilotFiniteExpectation] using
        integral_pauliPilotBornProductMeasure (q := 1) theta
          (mixedCyclicPauliStrictInterior_physical theta hInterior)
          (mixedCyclicPauliBlockCoordinate j)
    _ = theta j := by
      simpa [mixedCyclicPauliBlockCoordinate, pauliPilotCoordinateVariable] using
        integral_pauliPilotCoordinateVariable_eq (q := 1) theta
          (mixedCyclicPauliStrictInterior_physical theta hInterior) j (0 : Fin 1)

private theorem mixedCyclicPauliCenteredCoordinate_finiteMean_zero
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    pauliPilotFiniteExpectation (q := 1) theta
      (mixedCyclicPauliCenteredCoordinate theta j) = 0 := by
  rw [show mixedCyclicPauliCenteredCoordinate theta j =
      fun block => mixedCyclicPauliBlockCoordinate j block - (fun _ => theta j) block by rfl]
  rw [mixedCyclicFiniteExpectation_sub,
    mixedCyclicPauliBlockCoordinate_finiteMean theta hInterior j,
    mixedCyclicFiniteExpectation_const]
  ring

private theorem mixedCyclicPauliBlockCoordinate_sq_one
    (j : Fin 3) (block : PauliPilotPath 1) :
    mixedCyclicPauliBlockCoordinate j block ^ 2 = 1 := by
  simp only [mixedCyclicPauliBlockCoordinate]
  cases h : block 0 j <;> simp [pauliOutcomeSign, h]

private theorem mixedCyclicPauliCenteredCoordinate_finiteSecondMoment
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    pauliPilotFiniteExpectation (q := 1) theta
      (fun block => mixedCyclicPauliCenteredCoordinate theta j block ^ 2) =
      1 - theta j ^ 2 := by
  let X : PauliPilotPath 1 → ℝ := mixedCyclicPauliBlockCoordinate j
  have hpoint : (fun block => mixedCyclicPauliCenteredCoordinate theta j block ^ 2) =
      (fun block => X block ^ 2 - (2 * theta j) * X block + theta j ^ 2) := by
    funext block
    simp only [mixedCyclicPauliCenteredCoordinate, X]
    ring
  rw [hpoint]
  rw [show (fun block => X block ^ 2 - (2 * theta j) * X block + theta j ^ 2) =
      (fun block => (X block ^ 2 - (2 * theta j) * X block) + (fun _ => theta j ^ 2) block) by rfl]
  rw [mixedCyclicFiniteExpectation_add]
  rw [show (fun block => X block ^ 2 - (2 * theta j) * X block) =
      (fun block => X block ^ 2 - (fun block => (2 * theta j) * X block) block) by rfl]
  rw [mixedCyclicFiniteExpectation_sub, mixedCyclicFiniteExpectation_const_mul,
    mixedCyclicFiniteExpectation_const]
  have hXsq : pauliPilotFiniteExpectation (q := 1) theta (fun block => X block ^ 2) = 1 := by
    rw [show (fun block => X block ^ 2) = (fun _ => (1 : ℝ)) by
      funext block
      exact mixedCyclicPauliBlockCoordinate_sq_one j block]
    exact mixedCyclicFiniteExpectation_const theta 1
  rw [hXsq]
  change 1 - (2 * theta j) *
      pauliPilotFiniteExpectation (q := 1) theta (mixedCyclicPauliBlockCoordinate j) + theta j ^ 2 =
    1 - theta j ^ 2
  rw [mixedCyclicPauliBlockCoordinate_finiteMean theta hInterior j]
  ring

private theorem mixedCyclicPauliCenteredCoordinate_finiteCrossMoment_zero
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j k : Fin 3) (hjk : j ≠ k) :
    pauliPilotFiniteExpectation (q := 1) theta
      (fun block => mixedCyclicPauliCenteredCoordinate theta j block *
        mixedCyclicPauliCenteredCoordinate theta k block) = 0 := by
  let f : MixedPauliAxisPath 1 → ℝ := fun axisPath =>
    pauliOutcomeSign (axisPath 0) - theta j
  let g : MixedPauliAxisPath 1 → ℝ := fun axisPath =>
    pauliOutcomeSign (axisPath 0) - theta k
  have hfactor := pauliPilotFiniteExpectation_distinctAxis_mul_factorization
    (q := 1) theta j k hjk f g
  have hfj : pauliPilotFiniteExpectation (q := 1) theta
      (fun path => f (fun b => path b j)) = 0 := by
    change pauliPilotFiniteExpectation (q := 1) theta
      (mixedCyclicPauliCenteredCoordinate theta j) = 0
    exact mixedCyclicPauliCenteredCoordinate_finiteMean_zero theta hInterior j
  have hgk : pauliPilotFiniteExpectation (q := 1) theta
      (fun path => g (fun b => path b k)) = 0 := by
    change pauliPilotFiniteExpectation (q := 1) theta
      (mixedCyclicPauliCenteredCoordinate theta k) = 0
    exact mixedCyclicPauliCenteredCoordinate_finiteMean_zero theta hInterior k
  rw [hfj, hgk] at hfactor
  simpa [f, g, mixedCyclicPauliCenteredCoordinate, mixedCyclicPauliBlockCoordinate] using hfactor

private theorem mixedCyclicPauliFiniteExpectation_eq_integral
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (f : PauliPilotPath 1 → ℝ) :
    pauliPilotFiniteExpectation (q := 1) theta f =
      ∫ block, f block ∂mixedCyclicPauliBlockMeasure theta := by
  symm
  simpa [pauliPilotFiniteExpectation] using
    integral_pauliPilotBornProductMeasure (q := 1) theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior) f

/-- Every centered axis score has exact zero mean. -/
theorem mixedCyclicPauliCenteredCoordinate_mean_zero
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    ∫ block, mixedCyclicPauliCenteredCoordinate theta j block
      ∂mixedCyclicPauliBlockMeasure theta = 0 := by
  rw [← mixedCyclicPauliFiniteExpectation_eq_integral theta hInterior]
  exact mixedCyclicPauliCenteredCoordinate_finiteMean_zero theta hInterior j

/-- Exact variance of one centered Pauli outcome. -/
theorem mixedCyclicPauliCenteredCoordinate_secondMoment
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j : Fin 3) :
    ∫ block, mixedCyclicPauliCenteredCoordinate theta j block ^ 2
      ∂mixedCyclicPauliBlockMeasure theta = 1 - theta j ^ 2 := by
  rw [← mixedCyclicPauliFiniteExpectation_eq_integral theta hInterior]
  exact mixedCyclicPauliCenteredCoordinate_finiteSecondMoment theta hInterior j

/-- Distinct Pauli axes have zero centered cross moment in one Born-product block. -/
theorem mixedCyclicPauliCenteredCoordinate_crossMoment_zero
    (theta : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (j k : Fin 3) (hjk : j ≠ k) :
    ∫ block, mixedCyclicPauliCenteredCoordinate theta j block *
        mixedCyclicPauliCenteredCoordinate theta k block
      ∂mixedCyclicPauliBlockMeasure theta = 0 := by
  rw [← mixedCyclicPauliFiniteExpectation_eq_integral theta hInterior]
  exact mixedCyclicPauliCenteredCoordinate_finiteCrossMoment_zero theta hInterior j k hjk

/-- Exact zero mean of one cyclic directional score block. -/
theorem mixedCyclicPauliBlockScore_mean_zero
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∫ block, mixedCyclicPauliBlockScore theta h block
      ∂mixedCyclicPauliBlockMeasure theta = 0 := by
  let c0 := mixedCyclicPauliScoreCoefficient theta h 0
  let c1 := mixedCyclicPauliScoreCoefficient theta h 1
  let c2 := mixedCyclicPauliScoreCoefficient theta h 2
  rw [← mixedCyclicPauliFiniteExpectation_eq_integral theta hInterior]
  change pauliPilotFiniteExpectation (q := 1) theta (fun block =>
      c0 * mixedCyclicPauliCenteredCoordinate theta 0 block +
      c1 * mixedCyclicPauliCenteredCoordinate theta 1 block +
      c2 * mixedCyclicPauliCenteredCoordinate theta 2 block) = 0
  rw [mixedCyclicFiniteExpectation_add, mixedCyclicFiniteExpectation_add]
  simp_rw [mixedCyclicFiniteExpectation_const_mul,
    mixedCyclicPauliCenteredCoordinate_finiteMean_zero theta hInterior]
  ring

/-- Exact second moment of one mixed-state cyclic score block. -/
theorem mixedCyclicPauliBlockScore_secondMoment
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∫ block, mixedCyclicPauliBlockScore theta h block ^ 2
      ∂mixedCyclicPauliBlockMeasure theta = mixedCyclicPauliFisherQuadratic theta h := by
  let c0 := mixedCyclicPauliScoreCoefficient theta h 0
  let c1 := mixedCyclicPauliScoreCoefficient theta h 1
  let c2 := mixedCyclicPauliScoreCoefficient theta h 2
  let z0 : PauliPilotPath 1 → ℝ := mixedCyclicPauliCenteredCoordinate theta 0
  let z1 : PauliPilotPath 1 → ℝ := mixedCyclicPauliCenteredCoordinate theta 1
  let z2 : PauliPilotPath 1 → ℝ := mixedCyclicPauliCenteredCoordinate theta 2
  have hsquare : (fun block => mixedCyclicPauliBlockScore theta h block ^ 2) =
      (fun block =>
        c0 ^ 2 * z0 block ^ 2 + c1 ^ 2 * z1 block ^ 2 + c2 ^ 2 * z2 block ^ 2 +
        (2 * c0 * c1) * (z0 block * z1 block) +
        (2 * c0 * c2) * (z0 block * z2 block) +
        (2 * c1 * c2) * (z1 block * z2 block)) := by
    funext block
    simp only [mixedCyclicPauliBlockScore, c0, c1, c2, z0, z1, z2]
    ring
  rw [← mixedCyclicPauliFiniteExpectation_eq_integral theta hInterior]
  rw [hsquare]
  simp only [mixedCyclicFiniteExpectation_add, mixedCyclicFiniteExpectation_const_mul]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z0 block ^ 2) =
      1 - theta 0 ^ 2 by
      exact mixedCyclicPauliCenteredCoordinate_finiteSecondMoment theta hInterior 0]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z1 block ^ 2) =
      1 - theta 1 ^ 2 by
      exact mixedCyclicPauliCenteredCoordinate_finiteSecondMoment theta hInterior 1]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z2 block ^ 2) =
      1 - theta 2 ^ 2 by
      exact mixedCyclicPauliCenteredCoordinate_finiteSecondMoment theta hInterior 2]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z0 block * z1 block) = 0 by
      exact mixedCyclicPauliCenteredCoordinate_finiteCrossMoment_zero theta hInterior 0 1 (by decide)]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z0 block * z2 block) = 0 by
      exact mixedCyclicPauliCenteredCoordinate_finiteCrossMoment_zero theta hInterior 0 2 (by decide)]
  rw [show pauliPilotFiniteExpectation (q := 1) theta (fun block => z1 block * z2 block) = 0 by
      exact mixedCyclicPauliCenteredCoordinate_finiteCrossMoment_zero theta hInterior 1 2 (by decide)]
  simp only [mul_zero, add_zero]
  rfl

/-- Variance of one cyclic score block equals the directional Fisher information. -/
theorem mixedCyclicPauliBlockScore_variance
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    Var[mixedCyclicPauliBlockScore theta h; mixedCyclicPauliBlockMeasure theta] =
      mixedCyclicPauliFisherQuadratic theta h := by
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable]
  rw [mixedCyclicPauliBlockScore_mean_zero theta h hInterior]
  simpa using mixedCyclicPauliBlockScore_secondMoment theta h hInterior

private noncomputable def mixedCyclicPauliBlockScoreEnvelope (theta h : RLSVector 3) : ℝ :=
  |mixedCyclicPauliScoreCoefficient theta h 0| * (1 + |theta 0|) +
  |mixedCyclicPauliScoreCoefficient theta h 1| * (1 + |theta 1|) +
  |mixedCyclicPauliScoreCoefficient theta h 2| * (1 + |theta 2|)

private theorem mixedCyclicPauliBlockScore_abs_le
    (theta h : RLSVector 3) (block : PauliPilotPath 1) :
    |mixedCyclicPauliBlockScore theta h block| ≤
      mixedCyclicPauliBlockScoreEnvelope theta h := by
  have hz (j : Fin 3) : |mixedCyclicPauliCenteredCoordinate theta j block| ≤ 1 + |theta j| := by
    rw [mixedCyclicPauliCenteredCoordinate]
    calc
      |mixedCyclicPauliBlockCoordinate j block - theta j| ≤
          |mixedCyclicPauliBlockCoordinate j block| + |theta j| := abs_sub _ _
      _ = 1 + |theta j| := by
        have hs := mixedCyclicPauliBlockCoordinate_sq_one j block
        have hsabs : |mixedCyclicPauliBlockCoordinate j block| ^ 2 = 1 := by
          simpa [sq_abs] using hs
        have ha : |mixedCyclicPauliBlockCoordinate j block| = 1 := by
          nlinarith [abs_nonneg (mixedCyclicPauliBlockCoordinate j block)]
        rw [ha]
  simp only [mixedCyclicPauliBlockScore, mixedCyclicPauliBlockScoreEnvelope]
  calc
    |mixedCyclicPauliScoreCoefficient theta h 0 * mixedCyclicPauliCenteredCoordinate theta 0 block +
        mixedCyclicPauliScoreCoefficient theta h 1 * mixedCyclicPauliCenteredCoordinate theta 1 block +
        mixedCyclicPauliScoreCoefficient theta h 2 * mixedCyclicPauliCenteredCoordinate theta 2 block| ≤
        |mixedCyclicPauliScoreCoefficient theta h 0 * mixedCyclicPauliCenteredCoordinate theta 0 block +
          mixedCyclicPauliScoreCoefficient theta h 1 * mixedCyclicPauliCenteredCoordinate theta 1 block| +
        |mixedCyclicPauliScoreCoefficient theta h 2 * mixedCyclicPauliCenteredCoordinate theta 2 block| :=
      abs_add_le _ _
    _ ≤ (|mixedCyclicPauliScoreCoefficient theta h 0 * mixedCyclicPauliCenteredCoordinate theta 0 block| +
          |mixedCyclicPauliScoreCoefficient theta h 1 * mixedCyclicPauliCenteredCoordinate theta 1 block|) +
        |mixedCyclicPauliScoreCoefficient theta h 2 * mixedCyclicPauliCenteredCoordinate theta 2 block| :=
      add_le_add_left (abs_add_le _ _)
        |mixedCyclicPauliScoreCoefficient theta h 2 *
          mixedCyclicPauliCenteredCoordinate theta 2 block|
    _ = |mixedCyclicPauliScoreCoefficient theta h 0| *
          |mixedCyclicPauliCenteredCoordinate theta 0 block| +
        |mixedCyclicPauliScoreCoefficient theta h 1| *
          |mixedCyclicPauliCenteredCoordinate theta 1 block| +
        |mixedCyclicPauliScoreCoefficient theta h 2| *
          |mixedCyclicPauliCenteredCoordinate theta 2 block| := by simp only [abs_mul]
    _ ≤ |mixedCyclicPauliScoreCoefficient theta h 0| * (1 + |theta 0|) +
        |mixedCyclicPauliScoreCoefficient theta h 1| * (1 + |theta 1|) +
        |mixedCyclicPauliScoreCoefficient theta h 2| * (1 + |theta 2|) := by
      gcongr
      · exact hz 0
      · exact hz 1
      · exact hz 2

private theorem mixedCyclicPauliBlockScore_memLp_two
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    MemLp (mixedCyclicPauliBlockScore theta h) 2 (mixedCyclicPauliBlockMeasure theta) :=
  by
    letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
      ⟨pauliPilotBornProductMeasure_univ theta
        (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
    exact MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (mixedCyclicPauliBlockScoreEnvelope theta h)
      (Filter.univ_mem' (mixedCyclicPauliBlockScore_abs_le theta h))

/-- Score increment from block `k`. -/
noncomputable def mixedCyclicPauliScoreIncrement
    (theta h : RLSVector 3) (k : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  mixedCyclicPauliBlockScore theta h (omega k)

/-- Normalized directional score after `q` complete cycles, hence `3q` physical shots. -/
noncomputable def mixedCyclicPauliNormalizedScore
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  (Real.sqrt q)⁻¹ * ∑ k ∈ Finset.range q, mixedCyclicPauliScoreIncrement theta h k omega

private theorem mixedCyclicPauliScoreIncrement_hasLaw
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) (k : ℕ) :
    HasLaw (mixedCyclicPauliScoreIncrement theta h k)
      (Measure.map (mixedCyclicPauliBlockScore theta h) (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  refine ⟨((measurable_of_finite _).comp (measurable_pi_apply k)).aemeasurable, ?_⟩
  change Measure.map
      (mixedCyclicPauliBlockScore theta h ∘ fun omega : MixedCyclicPauliOmega => omega k)
      (mixedCyclicPauliMeasure theta) = _
  calc
    Measure.map
        (mixedCyclicPauliBlockScore theta h ∘ fun omega : MixedCyclicPauliOmega => omega k)
        (mixedCyclicPauliMeasure theta) =
        Measure.map (mixedCyclicPauliBlockScore theta h)
          (Measure.map (fun omega : MixedCyclicPauliOmega => omega k)
            (mixedCyclicPauliMeasure theta)) := by
      symm
      exact Measure.map_map Measurable.of_discrete (measurable_pi_apply k)
    _ = Measure.map (mixedCyclicPauliBlockScore theta h)
        (mixedCyclicPauliBlockMeasure theta) := by
      rw [Measure.infinitePi_map_eval]

/-- The cyclic score blocks are independent. -/
theorem mixedCyclicPauliScoreIncrement_iIndepFun
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    iIndepFun (mixedCyclicPauliScoreIncrement theta h) (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  exact iIndepFun_infinitePi (fun _ => measurable_of_finite _)

/-- The cyclic score blocks are identically distributed. -/
theorem mixedCyclicPauliScoreIncrement_identDistrib
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) (k : ℕ) :
    IdentDistrib (mixedCyclicPauliScoreIncrement theta h k)
      (mixedCyclicPauliScoreIncrement theta h 0)
      (mixedCyclicPauliMeasure theta) (mixedCyclicPauliMeasure theta) := by
  exact HasLaw.identDistrib
    (mixedCyclicPauliScoreIncrement_hasLaw theta h hInterior k)
    (mixedCyclicPauliScoreIncrement_hasLaw theta h hInterior 0)

private theorem mixedCyclicPauliScoreIncrement_memLp_two
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    MemLp (mixedCyclicPauliScoreIncrement theta h 0) 2 (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  exact (mixedCyclicPauliBlockScore_memLp_two theta h hInterior).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => mixedCyclicPauliBlockMeasure theta) 0)

private theorem mixedCyclicPauliScoreIncrement_mean_zero
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∫ omega, mixedCyclicPauliScoreIncrement theta h 0 omega
      ∂mixedCyclicPauliMeasure theta = 0 := by
  let hSelf : HasLaw (mixedCyclicPauliBlockScore theta h)
      (Measure.map (mixedCyclicPauliBlockScore theta h) (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliBlockMeasure theta) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  have hIdent := HasLaw.identDistrib
    (mixedCyclicPauliScoreIncrement_hasLaw theta h hInterior 0) hSelf
  rw [IdentDistrib.integral_eq hIdent]
  exact mixedCyclicPauliBlockScore_mean_zero theta h hInterior

private theorem mixedCyclicPauliScoreIncrement_variance
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    Var[mixedCyclicPauliScoreIncrement theta h 0; mixedCyclicPauliMeasure theta] =
      mixedCyclicPauliFisherQuadratic theta h := by
  let hSelf : HasLaw (mixedCyclicPauliBlockScore theta h)
      (Measure.map (mixedCyclicPauliBlockScore theta h) (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliBlockMeasure theta) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  have hIdent := HasLaw.identDistrib
    (mixedCyclicPauliScoreIncrement_hasLaw theta h hInterior 0) hSelf
  rw [IdentDistrib.variance_eq hIdent]
  exact mixedCyclicPauliBlockScore_variance theta h hInterior

/-- Kernel-proved scalar CLT for the mixed-state cyclic-Pauli score. -/
theorem mixedCyclicPauliNormalizedScore_CLT
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    let _ : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
      ⟨pauliPilotBornProductMeasure_univ theta
        (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
    let _ : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
      fun _ => inferInstance
    let _ : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliMeasure theta) :=
      fun _ => inferInstance
    TendstoInDistribution (mixedCyclicPauliNormalizedScore theta h) atTop id
      (fun _ => mixedCyclicPauliMeasure theta)
      (gaussianReal 0 (mixedCyclicPauliFisherQuadratic theta h).toNNReal) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  letI : IsProbabilityMeasure (mixedCyclicPauliMeasure theta) := inferInstance
  let gaussian := gaussianReal 0
    (Var[mixedCyclicPauliScoreIncrement theta h 0; mixedCyclicPauliMeasure theta]).toNNReal
  have hGaussian : HasLaw id gaussian gaussian :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub hGaussian
    (mixedCyclicPauliScoreIncrement_memLp_two theta h hInterior)
    (mixedCyclicPauliScoreIncrement_iIndepFun theta h hInterior)
    (mixedCyclicPauliScoreIncrement_identDistrib theta h hInterior)
  convert hCLT using 1
  · funext q omega
    rw [mixedCyclicPauliNormalizedScore,
      mixedCyclicPauliScoreIncrement_mean_zero theta h hInterior]
    ring
  · change gaussianReal 0 (mixedCyclicPauliFisherQuadratic theta h).toNNReal =
      gaussianReal 0
        (Var[mixedCyclicPauliScoreIncrement theta h 0;
          mixedCyclicPauliMeasure theta]).toNNReal
    rw [mixedCyclicPauliScoreIncrement_variance theta h hInterior]

end QubitOracle.Paper
