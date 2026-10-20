import QubitOracle.Paper.OneQubitPrespecifiedBatchBuresMinimaxAlgebra
import QubitOracle.Paper.OneQubitMixedConcreteProtocolToMinimax

/-!
# Orthogonal LAN transfer and the prespecified-batch Bures lower bound

This module proves the finite-dimensional reparameterization step that turns
raw Bloch-coordinate LAN into tangent--tangent--radial LAN.  The legacy
shrinking-neighborhood risk below is intentionally conditional on an explicit
`ExactLANLocalMinimaxQuadraticTransfer`; it is not identified with Beran's
source-faithful growing-ball theorem.

The protocol-specific input is one bundled raw LAN proof value.  Its second
field merely records the information matrix already carried by the LAN record;
there are no additional controller, concentration, likelihood, or estimator
premises.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology Matrix

noncomputable section

universe u

/-! ## A conflict-free orthogonal reparameterization -/

/-- Pull an experiment back by the raw-coordinate map `eta |-> Rᵀ eta`.
Thus `eta = R theta` are the new coordinates when `R` is orthogonal. -/
def orthogonalReparameterizedHajekExperiment
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) (R : Matrix D D Real) :
    HajekExperimentSequence D where
  Sample := E.Sample
  measurableSpace := E.measurableSpace
  parameterSet := {eta | R.transpose.mulVec eta ∈ E.parameterSet}
  law n eta := E.law n (R.transpose.mulVec eta)
  probabilityMeasure n eta := E.probabilityMeasure n (R.transpose.mulVec eta)

/-- Orthogonality data used by the LAN transport. -/
def IsOrthogonalRealMatrix
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : Matrix D D Real) : Prop :=
  R * R.transpose = 1 ∧ R.transpose * R = 1

theorem dotProduct_mulVec_eq_transpose_mulVec_dotProduct
    {D : Type*} [Fintype D]
    (R : Matrix D D Real) (x y : D → Real) :
    dotProduct x (R.mulVec y) =
      dotProduct (R.transpose.mulVec x) y := by
  unfold Matrix.mulVec
  simp only [dotProduct]
  calc
    (∑ i, x i * ∑ j, R i j * y j) =
        ∑ i, ∑ j, x i * (R i j * y j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, x i * (R i j * y j) := by
      rw [Finset.sum_comm]
    _ = ∑ j, (∑ i, R.transpose j i * x i) * y j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Matrix.transpose_apply]
      ring

theorem orthogonalReparameterized_localParameter_zero
    {D : Type*} [Fintype D]
    (R : Matrix D D Real) (h : HajekParameter D) (n : Nat) :
    R.transpose.mulVec (hajekLocalParameter 0 h n) =
      hajekLocalParameter 0 (R.transpose.mulVec h) n := by
  funext i
  simp only [hajekLocalParameter, Pi.zero_apply, zero_add]
  unfold Matrix.mulVec
  simp only [dotProduct, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [hajekLocalParameter]
  ring

theorem orthogonalReparameterized_hajekLikelihoodRatio_zero
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) (R : Matrix D D Real)
    (n : Nat) (eta : HajekParameter D) :
    hajekLikelihoodRatio
        (orthogonalReparameterizedHajekExperiment E R) n eta 0 =
      hajekLikelihoodRatio E n (R.transpose.mulVec eta) 0 := by
  funext x
  simp [hajekLikelihoodRatio, orthogonalReparameterizedHajekExperiment,
    Matrix.mulVec]
  rfl

theorem orthogonalReparameterized_quadraticForm
    {D : Type*} [Fintype D]
    (R J : Matrix D D Real) (h : HajekParameter D) :
    hajekQuadraticForm (R * J * R.transpose) h =
      hajekQuadraticForm J (R.transpose.mulVec h) := by
  unfold hajekQuadraticForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec_eq_transpose_mulVec_dotProduct]

theorem orthogonal_congruence_posDef
    {D : Type*} [Fintype D] [DecidableEq D]
    (R J : Matrix D D Real)
    (hR : IsOrthogonalRealMatrix R) (hJ : J.PosDef) :
    (R * J * R.transpose).PosDef := by
  have hInjective : Function.Injective R.transpose.mulVec := by
    apply Function.LeftInverse.injective (g := R.mulVec)
    intro x
    rw [Matrix.mulVec_mulVec, hR.1, Matrix.one_mulVec]
  simpa using hJ.conjTranspose_mul_mul_same
    (B := R.transpose) hInjective

/-- Raw LAN at zero transports exactly through an orthogonal coordinate map.
The score is `R Delta_n`, the information is `R J Rᵀ`, and the remainder at
`h` is the raw remainder at `Rᵀ h`. -/
noncomputable def orthogonalReparameterizedHajekLAN
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : HajekExperimentSequence D) (R : Matrix D D Real)
    (hR : IsOrthogonalRealMatrix R)
    (rawLAN : Hajek1972Assumption31LAN E 0) :
    Hajek1972Assumption31LAN
      (orthogonalReparameterizedHajekExperiment E R) 0 where
  truth_mem := by
    simpa [orthogonalReparameterizedHajekExperiment, Matrix.mulVec] using
      rawLAN.truth_mem
  information := R * rawLAN.information * R.transpose
  information_posDef :=
    orthogonal_congruence_posDef R rawLAN.information hR
      rawLAN.information_posDef
  score n x := R.mulVec (rawLAN.score n x)
  score_measurable n i := by
    unfold Matrix.mulVec
    simp only [dotProduct]
    apply Finset.measurable_sum
    intro j _hj
    exact measurable_const.mul (rawLAN.score_measurable n j)
  remainder n h x := rawLAN.remainder n (R.transpose.mulVec h) x
  remainder_measurable n h := rawLAN.remainder_measurable n _
  local_parameter_eventually_mem h := by
    obtain ⟨N, hN⟩ := rawLAN.local_parameter_eventually_mem
      (R.transpose.mulVec h)
    refine ⟨N, ?_⟩
    intro n hn
    change R.transpose.mulVec (hajekLocalParameter 0 h n) ∈ E.parameterSet
    rw [orthogonalReparameterized_localParameter_zero]
    exact hN n hn
  likelihood_ratio_expansion h := by
    obtain ⟨N, hN⟩ := rawLAN.likelihood_ratio_expansion
      (R.transpose.mulVec h)
    refine ⟨N, ?_⟩
    intro n hn x
    rw [orthogonalReparameterized_hajekLikelihoodRatio_zero,
      orthogonalReparameterized_localParameter_zero, hN n hn x]
    rw [dotProduct_mulVec_eq_transpose_mulVec_dotProduct,
      orthogonalReparameterized_quadraticForm]
  score_converges := by
    intro z
    have hz := rawLAN.score_converges (R.transpose.mulVec z)
    change Tendsto
      (fun n =>
        letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
        integral (E.law n (R.transpose.mulVec 0))
          (fun x => Complex.exp
            (Complex.I * Complex.ofReal
              (dotProduct z (R.mulVec (rawLAN.score n x))))))
      atTop
      (nhds (Complex.exp
        (-((hajekQuadraticForm
          (R * rawLAN.information * R.transpose) z : Real) : Complex) / 2)))
    simpa [Matrix.mulVec,
      dotProduct_mulVec_eq_transpose_mulVec_dotProduct,
      orthogonalReparameterized_quadraticForm] using hz
  remainder_converges := by
    intro h epsilon hepsilon
    have hh := rawLAN.remainder_converges
      (R.transpose.mulVec h) epsilon hepsilon
    change Tendsto
      (fun n =>
        letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
        E.law n (R.transpose.mulVec 0)
          {x | epsilon <=
            |rawLAN.remainder n (R.transpose.mulVec h) x|})
      atTop (nhds 0)
    simpa [Matrix.mulVec] using hh

/-! ## Exact mixed-qubit specialization -/

/-- One supplied raw prespecified-batch LAN proof, bundled with the exact
information normalization needed to state the Bures result. -/
structure PrespecifiedBatchRawBuresLANProof
    (E : HajekExperimentSequence (Fin 3))
    (theta : RLSVector 3) where
  lan : Hajek1972Assumption31LAN E 0
  information_eq : lan.information = mixedBuresTarget theta

/-- The prespecified-batch experiment in local tangent--tangent--radial
coordinates. -/
def prespecifiedBatchOrthogonalExperiment
    (E : HajekExperimentSequence (Fin 3))
    (theta b : RLSVector 3) : HajekExperimentSequence (Fin 3) :=
  orthogonalReparameterizedHajekExperiment E
    (localRadialTangentCoordinateMatrix b theta)

theorem localRadialTangentCoordinateMatrix_isOrthogonal
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    IsOrthogonalRealMatrix (localRadialTangentCoordinateMatrix b theta) :=
  localRadialTangentCoordinateMatrix_orthogonal theta b hTruth hSeed

/-- The transported LAN certificate obtained from the sole supplied raw LAN
proof value. -/
noncomputable def prespecifiedBatchOrthogonalLAN
    {E : HajekExperimentSequence (Fin 3)}
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (raw : PrespecifiedBatchRawBuresLANProof E theta) :
    Hajek1972Assumption31LAN
      (prespecifiedBatchOrthogonalExperiment E theta b) 0 :=
  orthogonalReparameterizedHajekLAN E
    (localRadialTangentCoordinateMatrix b theta)
    (localRadialTangentCoordinateMatrix_isOrthogonal
      theta b hTruth hSeed)
    raw.lan

theorem prespecifiedBatchOrthogonalLAN_information_eq
    {E : HajekExperimentSequence (Fin 3)}
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (raw : PrespecifiedBatchRawBuresLANProof E theta) :
    (prespecifiedBatchOrthogonalLAN theta b hTruth hSeed raw).information =
      mixedBuresCoordinateInformation theta := by
  change localRadialTangentTransform b theta raw.lan.information = _
  rw [raw.information_eq]
  exact localRadialTangentTransform_mixedBuresTarget
    theta b hTruth hSeed

/-- Coordinate Bures/ordinary-infidelity quadratic-limit loss. -/
def prespecifiedBatchCoordinateBuresLoss
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    NonnegativeCoordinateQuadraticLimitLoss (Fin 3) where
  weight := mixedBuresInfidelityCoordinateWeightEigenvalues theta
  weight_nonnegative := by
    intro i
    have hgap := mixedInteriorBlochGap_pos theta hTruth
    fin_cases i <;>
      simp [mixedBuresInfidelityCoordinateWeightEigenvalues] <;>
      positivity

theorem coordinateBuresBenchmark_eq_covarianceQuadraticRisk
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (Sigma : Matrix (Fin 3) (Fin 3) Real) :
    coordinateGaussianQuadraticBenchmark
        (prespecifiedBatchCoordinateBuresLoss theta hTruth) Sigma =
      covarianceQuadraticRisk
        (mixedBuresInfidelityCoordinateWeight theta) Sigma := by
  simp [coordinateGaussianQuadraticBenchmark,
    prespecifiedBatchCoordinateBuresLoss, covarianceQuadraticRisk,
    mixedBuresInfidelityCoordinateWeight, Matrix.diagonal_apply,
    Fin.sum_univ_succ]

theorem prespecifiedBatchOrthogonalLAN_buresBenchmark_eq_nine_fourths
    {E : HajekExperimentSequence (Fin 3)}
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (raw : PrespecifiedBatchRawBuresLANProof E theta) :
    coordinateGaussianQuadraticBenchmark
        (prespecifiedBatchCoordinateBuresLoss theta hTruth)
        (prespecifiedBatchOrthogonalLAN
          theta b hTruth hSeed raw).information⁻¹ = 9 / 4 := by
  rw [prespecifiedBatchOrthogonalLAN_information_eq
    theta b hTruth hSeed raw]
  rw [coordinateBuresBenchmark_eq_covarianceQuadraticRisk theta hTruth]
  exact mixedBuresInfidelityGaussianBenchmark_eq_nine_fourths theta hTruth

/-- Exact all-estimator local-minimax Bures/ordinary-infidelity lower bound for
the legacy shrinking-neighborhood risk, conditional on the exact transfer
contract for that risk.  The source-faithful Beran theorem is applied elsewhere
to its published growing-ball risk functional. -/
theorem prespecifiedBatchOrthogonal_bures_localMinimax_lower_bound
    {E : HajekExperimentSequence (Fin 3)}
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (raw : PrespecifiedBatchRawBuresLANProof E theta)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer
      (prespecifiedBatchOrthogonalExperiment E theta b) 0
      (prespecifiedBatchOrthogonalLAN theta b hTruth hSeed raw))
    (T : HajekVectorEstimator
      (prespecifiedBatchOrthogonalExperiment E theta b)) :
    ENNReal.ofReal (9 / 4 : Real) ≤
      hajekShrinkingNeighborhoodQuadraticRisk
        (prespecifiedBatchOrthogonalExperiment E theta b) 0
        (prespecifiedBatchCoordinateBuresLoss theta hTruth) T := by
  let lan := prespecifiedBatchOrthogonalLAN theta b hTruth hSeed raw
  change ExactLANLocalMinimaxQuadraticTransfer
    (prespecifiedBatchOrthogonalExperiment E theta b) 0 lan at transfer
  have lower := transfer.lower_bound
    (prespecifiedBatchCoordinateBuresLoss theta hTruth) T
  rw [show coordinateGaussianQuadraticBenchmark
      (prespecifiedBatchCoordinateBuresLoss theta hTruth)
      lan.information⁻¹ = 9 / 4 by
    exact prespecifiedBatchOrthogonalLAN_buresBenchmark_eq_nine_fourths
      theta b hTruth hSeed raw] at lower
  exact lower

#print axioms orthogonalReparameterizedHajekLAN
#print axioms prespecifiedBatchOrthogonalLAN_information_eq
#print axioms prespecifiedBatchOrthogonalLAN_buresBenchmark_eq_nine_fourths
#print axioms prespecifiedBatchOrthogonal_bures_localMinimax_lower_bound

end

end QubitOracle.Paper
