import QubitOracle.Paper.OneQubitPrespecifiedBatchObservedInformationClosure

/-!
# Sharp shot-level observed-information rate

The completed batch-major filtration makes the centered squared-score
innovations a bounded martingale-difference sequence. This file proves the
finite-horizon L2 isometry bound at the exact total-observation normalization,
then polarizes the directional result into the full three-by-three observed
information matrix.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open PrespecifiedBatchMartingaleClosure
open MixedExactCycleScalarTriangularArrayData
open scoped BigOperators ENNReal Topology Matrix

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-! ## A finite bounded martingale-difference L2 lemma -/

theorem boundedMartingaleDifference_integrable
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega) (X : Nat -> Omega -> Real)
    (hMeasurable : forall n, Measurable[F.seq (n + 1)] (X n))
    (C : Real) (hC : 0 <= C)
    (hBound : forall n omega, ‖X n omega‖ <= C)
    (n : Nat) :
    Integrable (X n) mu := by
  refine Integrable.of_bound
    ((hMeasurable n).mono (F.le (n + 1)) le_rfl).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall (hBound n)

theorem boundedMartingaleDifference_product_integrable
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega) (X : Nat -> Omega -> Real)
    (hMeasurable : forall n, Measurable[F.seq (n + 1)] (X n))
    (C : Real) (hC : 0 <= C)
    (hBound : forall n omega, ‖X n omega‖ <= C)
    (i j : Nat) :
    Integrable (fun omega => X i omega * X j omega) mu := by
  refine Integrable.of_bound
    ((((hMeasurable i).mono (F.le (i + 1)) le_rfl).mul
      ((hMeasurable j).mono (F.le (j + 1)) le_rfl)).aestronglyMeasurable)
    (C ^ 2) ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |X i omega| * |X j omega| <= C * C :=
      mul_le_mul (by simpa [Real.norm_eq_abs] using hBound i omega)
        (by simpa [Real.norm_eq_abs] using hBound j omega)
        (abs_nonneg _) hC
    _ = C ^ 2 := by ring

theorem boundedMartingaleDifference_cross_integral_zero
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega) (X : Nat -> Omega -> Real)
    (hMeasurable : forall n, Measurable[F.seq (n + 1)] (X n))
    (hCenter : forall n, mu[X n | F.seq n] =ᵐ[mu] (fun _ => (0 : Real)))
    (C : Real) (hC : 0 <= C)
    (hBound : forall n omega, ‖X n omega‖ <= C)
    {i j : Nat} (hij : i < j) :
    (∫ omega, X i omega * X j omega ∂mu) = 0 := by
  have hiStrong : StronglyMeasurable[F.seq j] (X i) :=
    ((hMeasurable i).mono (F.mono (Nat.succ_le_of_lt hij)) le_rfl).stronglyMeasurable
  have hiInt := boundedMartingaleDifference_integrable
    mu F X hMeasurable C hC hBound i
  have hjInt := boundedMartingaleDifference_integrable
    mu F X hMeasurable C hC hBound j
  have hprodInt := boundedMartingaleDifference_product_integrable
    mu F X hMeasurable C hC hBound i j
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := F.seq j) hiStrong hprodInt hjInt
  have hzero :
      (fun omega => X i omega * mu[X j | F.seq j] omega) =ᵐ[mu]
        (fun _ => (0 : Real)) := by
    filter_upwards [hCenter j] with omega homega
    simp [homega]
  calc
    (∫ omega, X i omega * X j omega ∂mu) =
        ∫ omega, mu[(fun z => X i z * X j z) | F.seq j] omega ∂mu := by
          symm
          exact integral_condExp (F.le j)
    _ = ∫ omega, X i omega * mu[X j | F.seq j] omega ∂mu :=
      integral_congr_ae hpull
    _ = 0 := by
      rw [integral_congr_ae hzero]
      simp

theorem boundedMartingaleDifference_increment_integral_zero
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega) (X : Nat -> Omega -> Real)
    (hCenter : forall n, mu[X n | F.seq n] =ᵐ[mu] (fun _ => (0 : Real)))
    (n : Nat) :
    (∫ omega, X n omega ∂mu) = 0 := by
  calc
    (∫ omega, X n omega ∂mu) =
        ∫ omega, mu[X n | F.seq n] omega ∂mu := by
          symm
          exact integral_condExp (F.le n)
    _ = 0 := by
      rw [integral_congr_ae (hCenter n)]
      simp

/-- Finite-horizon martingale orthogonality and the deterministic increment
bound give the exact L2 estimate M C squared. -/
theorem boundedMartingaleDifference_sum_sq_integrable_and_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega) (X : Nat -> Omega -> Real)
    (hMeasurable : forall n, Measurable[F.seq (n + 1)] (X n))
    (hCenter : forall n, mu[X n | F.seq n] =ᵐ[mu] (fun _ => (0 : Real)))
    (C : Real) (hC : 0 <= C)
    (hBound : forall n omega, ‖X n omega‖ <= C)
    (M : Nat) :
    Integrable (fun omega => (∑ n ∈ Finset.range M, X n omega) ^ 2) mu ∧
      (∫ omega, (∑ n ∈ Finset.range M, X n omega) ^ 2 ∂mu) <=
        (M : Real) * C ^ 2 := by
  let s := Finset.range M
  have hprodInt : forall i j,
      Integrable (fun omega => X i omega * X j omega) mu :=
    fun i j => boundedMartingaleDifference_product_integrable
      mu F X hMeasurable C hC hBound i j
  have hexpand :
      (fun omega => (∑ n ∈ s, X n omega) ^ 2) =
        fun omega => ∑ i ∈ s, ∑ j ∈ s, X i omega * X j omega := by
    funext omega
    rw [pow_two, Finset.sum_mul_sum]
  have hdoubleInt :
      Integrable (fun omega => ∑ i ∈ s, ∑ j ∈ s,
        X i omega * X j omega) mu := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hprodInt i j
  refine ⟨by rw [hexpand]; exact hdoubleInt, ?_⟩
  rw [hexpand]
  rw [integral_finset_sum]
  · calc
      (∑ i ∈ s, ∫ omega, ∑ j ∈ s, X i omega * X j omega ∂mu) =
          ∑ i ∈ s, ∑ j ∈ s,
            ∫ omega, X i omega * X j omega ∂mu := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [integral_finset_sum]
            intro j hj
            exact hprodInt i j
      _ = ∑ i ∈ s, ∫ omega, X i omega ^ 2 ∂mu := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_eq_single i]
            · congr 1
              funext omega
              ring
            · intro j hj hji
              rcases lt_or_gt_of_ne hji with hij | hji'
              · have hz := boundedMartingaleDifference_cross_integral_zero
                  mu F X hMeasurable hCenter C hC hBound hij
                simpa [mul_comm] using hz
              · exact boundedMartingaleDifference_cross_integral_zero
                  mu F X hMeasurable hCenter C hC hBound hji'
            · intro hnot
              exact (hnot hi).elim
      _ <= ∑ i ∈ s, C ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hii : Integrable (fun omega => X i omega ^ 2) mu := by
              simpa [pow_two] using hprodInt i i
            have hconst : Integrable (fun _ : Omega => C ^ 2) mu :=
              integrable_const _
            have hmono := integral_mono_ae
              hii
              hconst
              (by
                filter_upwards with omega
                have hiB := hBound i omega
                rw [Real.norm_eq_abs] at hiB
                have hp := mul_nonneg (sub_nonneg.mpr hiB)
                  (add_nonneg hC (abs_nonneg (X i omega)))
                nlinarith [sq_abs (X i omega)])
            simpa [pow_two] using hmono
      _ = (M : Real) * C ^ 2 := by simp [s]
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hprodInt i j

def prespecifiedBatchShotCenteredObservedInformationError
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) : Real :=
  (prespecifiedBatchTotalObservations K : Real)⁻¹ *
    ∑ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
      globalCenteredObservedInformation theta h b hInterior n omega

/-- Predictable final Fisher information from the completed shot-level
conditional-variance certificate. -/
def prespecifiedBatchShotPredictableDirectionalFisher
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) : Real :=
  ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
    prespecifiedBatchCumulativeConditionalVariance theta h b K t omega

/-- Truth-observed final information. The centered addend is literally the
sum of squared score minus its one-shot predictable Fisher contribution. -/
def prespecifiedBatchShotTruthObservedDirectionalInformation
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) : Real :=
  prespecifiedBatchShotPredictableDirectionalFisher
      theta h b hInterior K omega +
    prespecifiedBatchShotCenteredObservedInformationError
      theta h b hInterior K omega

theorem prespecifiedBatchShotCenteredObservedInformationError_eq_sum
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    prespecifiedBatchShotCenteredObservedInformationError theta h b hInterior K =
      fun omega =>
        (prespecifiedBatchTotalObservations K : Real)⁻¹ *
          ∑ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
            globalCenteredObservedInformation theta h b hInterior n omega := by
  funext omega
  rfl

def prespecifiedBatchObservedInformationSharpConstant
    (theta h : RLSVector 3) : Real :=
  4 * mixedProjectedScoreEnvelope theta h ^ 4

theorem prespecifiedBatchShotCenteredObservedInformationError_measurable
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    Measurable
      (prespecifiedBatchShotCenteredObservedInformationError
        theta h b hInterior K) := by
  rw [prespecifiedBatchShotCenteredObservedInformationError_eq_sum]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  exact (globalCenteredObservedInformation_measurable_succ
    theta h b hInterior n).mono
      ((globalFinalFiltration theta h b hInterior).le (n + 1)) le_rfl

theorem prespecifiedBatchShotCenteredObservedInformationError_integral_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    (∫ omega,
      prespecifiedBatchShotCenteredObservedInformationError
        theta h b hInterior K omega
      ∂exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) =
      0 := by
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  rw [prespecifiedBatchShotCenteredObservedInformationError_eq_sum]
  rw [integral_const_mul]
  rw [integral_finset_sum]
  · have hsumZero :
        (∑ i ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
          ∫ a, globalCenteredObservedInformation theta h b hInterior i a ∂mu) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact boundedMartingaleDifference_increment_integral_zero
        mu (globalFinalFiltration theta h b hInterior)
        (globalCenteredObservedInformation theta h b hInterior)
        (globalCenteredObservedInformation_condExp_zero theta h b hInterior) i
    rw [hsumZero, mul_zero]
  · intro n hn
    exact boundedMartingaleDifference_integrable
      mu (globalFinalFiltration theta h b hInterior)
      (globalCenteredObservedInformation theta h b hInterior)
      (globalCenteredObservedInformation_measurable_succ theta h b hInterior)
      (2 * mixedProjectedScoreEnvelope theta h ^ 2) (by positivity)
      (fun m omega => by
        simpa [Real.norm_eq_abs] using
          globalCenteredObservedInformation_abs_le
            theta h b hInterior m omega) n

/-- Sharp shot-level L2 rate: the centered observed information has mean square
at most 4 Envelope(theta,h)^4 / N_K. -/
theorem prespecifiedBatchShotCenteredObservedInformationError_l2_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    (∫ omega,
      prespecifiedBatchShotCenteredObservedInformationError
        theta h b hInterior K omega ^ 2
      ∂exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) <=
      prespecifiedBatchObservedInformationSharpConstant theta h /
        (prespecifiedBatchTotalObservations K : Real) := by
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  let F := globalFinalFiltration theta h b hInterior
  let X := globalCenteredObservedInformation theta h b hInterior
  let M := prespecifiedBatchCumulativeFinalRowLength K
  let N : Real := prespecifiedBatchTotalObservations K
  let C := 2 * mixedProjectedScoreEnvelope theta h ^ 2
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  by_cases hK : K = 0
  · subst K
    simp [prespecifiedBatchShotCenteredObservedInformationError,
      prespecifiedBatchShotTruthObservedDirectionalInformation,
      prespecifiedBatchShotPredictableDirectionalFisher,
      prespecifiedBatchTotalObservations_eq,
      prespecifiedBatchObservedInformationSharpConstant]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hNnat : 0 < prespecifiedBatchTotalObservations K :=
      prespecifiedBatchTotalObservations_pos K hKpos
    have hN : 0 < N := by
      unfold N
      exact_mod_cast hNnat
    obtain ⟨hsumInt, hsumL2⟩ :=
      boundedMartingaleDifference_sum_sq_integrable_and_le
        mu F X
        (globalCenteredObservedInformation_measurable_succ
          theta h b hInterior)
        (globalCenteredObservedInformation_condExp_zero
          theta h b hInterior)
        C (by positivity)
        (fun n omega => by
          simpa [C, Real.norm_eq_abs] using
            globalCenteredObservedInformation_abs_le
              theta h b hInterior n omega)
        M
    have hMnat :
        prespecifiedBatchCumulativeFinalRowLength K <=
          prespecifiedBatchTotalObservations K :=
      prespecifiedBatchCumulativeFinalRowLength_le_totalObservations K
    have hM : (M : Real) <= N := by
      unfold M N
      exact_mod_cast hMnat
    have heq :
        (fun omega =>
          prespecifiedBatchShotCenteredObservedInformationError
            theta h b hInterior K omega ^ 2) =
          fun omega => N⁻¹ ^ 2 *
            (∑ n ∈ Finset.range M, X n omega) ^ 2 := by
      funext omega
      rw [prespecifiedBatchShotCenteredObservedInformationError_eq_sum]
      dsimp [N, M, X]
      ring
    rw [heq, integral_const_mul]
    calc
      N⁻¹ ^ 2 * (∫ omega, (∑ n ∈ Finset.range M, X n omega) ^ 2 ∂mu) <=
          N⁻¹ ^ 2 * ((M : Real) * C ^ 2) :=
        mul_le_mul_of_nonneg_left hsumL2 (sq_nonneg _)
      _ <= N⁻¹ ^ 2 * (N * C ^ 2) := by gcongr
      _ = prespecifiedBatchObservedInformationSharpConstant theta h / N := by
        unfold C prespecifiedBatchObservedInformationSharpConstant
        field_simp [hN.ne']
        ring

theorem prespecifiedBatchShotCenteredObservedInformationError_memLp_two
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    MemLp
      (prespecifiedBatchShotCenteredObservedInformationError
        theta h b hInterior K)
      2 (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) := by
  apply (memLp_two_iff_integrable_sq
    (μ := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))
    (prespecifiedBatchShotCenteredObservedInformationError_measurable
      theta h b hInterior K).aestronglyMeasurable).2
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  let F := globalFinalFiltration theta h b hInterior
  let X := globalCenteredObservedInformation theta h b hInterior
  let M := prespecifiedBatchCumulativeFinalRowLength K
  let N : Real := prespecifiedBatchTotalObservations K
  let C := 2 * mixedProjectedScoreEnvelope theta h ^ 2
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  obtain ⟨hsumInt, _⟩ :=
    boundedMartingaleDifference_sum_sq_integrable_and_le
      mu F X
      (globalCenteredObservedInformation_measurable_succ theta h b hInterior)
      (globalCenteredObservedInformation_condExp_zero theta h b hInterior)
      C (by positivity)
      (fun n omega => by
        simpa [C, Real.norm_eq_abs] using
          globalCenteredObservedInformation_abs_le theta h b hInterior n omega)
      M
  have heq :
      (fun omega =>
        prespecifiedBatchShotCenteredObservedInformationError
          theta h b hInterior K omega ^ 2) =
        fun omega => N⁻¹ ^ 2 *
          (∑ n ∈ Finset.range M, X n omega) ^ 2 := by
    funext omega
    rw [prespecifiedBatchShotCenteredObservedInformationError_eq_sum]
    dsimp [N, M, X]
    ring
  rw [heq]
  exact hsumInt.const_mul _

/-- Chebyshev consequence of the sharp shot-level L2 rate. -/
theorem prespecifiedBatchShotCenteredObservedInformationError_tail_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (K : Nat) :
    exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
      {omega | epsilon <=
        |prespecifiedBatchShotCenteredObservedInformationError
          theta h b hInterior K omega|} <=
      ENNReal.ofReal
        (prespecifiedBatchObservedInformationSharpConstant theta h /
          ((prespecifiedBatchTotalObservations K : Real) * epsilon ^ 2)) := by
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  let Y := prespecifiedBatchShotCenteredObservedInformationError
    theta h b hInterior K
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  have hmem := prespecifiedBatchShotCenteredObservedInformationError_memLp_two
    theta h b hInterior K
  have hmean := prespecifiedBatchShotCenteredObservedInformationError_integral_zero
    theta h b hInterior K
  have hvar :
      variance Y mu <=
        prespecifiedBatchObservedInformationSharpConstant theta h /
          (prespecifiedBatchTotalObservations K : Real) := by
    change variance
      (prespecifiedBatchShotCenteredObservedInformationError
        theta h b hInterior K)
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) <= _
    rw [variance_eq_integral
      (prespecifiedBatchShotCenteredObservedInformationError_measurable
        theta h b hInterior K).aemeasurable, hmean]
    simpa only [sub_zero] using
      prespecifiedBatchShotCenteredObservedInformationError_l2_le
        theta h b hInterior K
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  have hcheb' :
      mu {omega | epsilon <= |Y omega|} <=
        ENNReal.ofReal (variance Y mu / epsilon ^ 2) := by
    simpa only [hmean, sub_zero] using hcheb
  exact hcheb'.trans (ENNReal.ofReal_le_ofReal (by
    calc
      variance Y mu / epsilon ^ 2 <=
          (prespecifiedBatchObservedInformationSharpConstant theta h /
            (prespecifiedBatchTotalObservations K : Real)) / epsilon ^ 2 :=
        div_le_div_of_nonneg_right hvar (sq_nonneg epsilon)
      _ = prespecifiedBatchObservedInformationSharpConstant theta h /
          ((prespecifiedBatchTotalObservations K : Real) * epsilon ^ 2) := by
        ring))

/-! ## Polarization to the full Fin 3 information matrix -/

def prespecifiedBatchPolarizationPlus (i j : Fin 3) : RLSVector 3 :=
  fun k => prespecifiedBatchCoordinateDirection i k +
    prespecifiedBatchCoordinateDirection j k

def prespecifiedBatchPolarizationMinus (i j : Fin 3) : RLSVector 3 :=
  fun k => prespecifiedBatchCoordinateDirection i k -
    prespecifiedBatchCoordinateDirection j k

def prespecifiedBatchShotTruthObservedInformationMatrix
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    (prespecifiedBatchShotTruthObservedDirectionalInformation theta
        (prespecifiedBatchPolarizationPlus i j) b hInterior K omega -
      prespecifiedBatchShotTruthObservedDirectionalInformation theta
        (prespecifiedBatchPolarizationMinus i j) b hInterior K omega) / 4

def prespecifiedBatchShotPredictableFisherMatrix
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    (prespecifiedBatchShotPredictableDirectionalFisher theta
        (prespecifiedBatchPolarizationPlus i j) b hInterior K omega -
      prespecifiedBatchShotPredictableDirectionalFisher theta
        (prespecifiedBatchPolarizationMinus i j) b hInterior K omega) / 4

def prespecifiedBatchShotInformationMatrixError
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    prespecifiedBatchShotTruthObservedInformationMatrix
        theta b hInterior K omega i j -
      prespecifiedBatchShotPredictableFisherMatrix
        theta b hInterior K omega i j

theorem prespecifiedBatchShotInformationMatrixError_apply
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath)
    (i j : Fin 3) :
    prespecifiedBatchShotInformationMatrixError theta b hInterior K omega i j =
      (prespecifiedBatchShotCenteredObservedInformationError theta
          (prespecifiedBatchPolarizationPlus i j) b hInterior K omega -
        prespecifiedBatchShotCenteredObservedInformationError theta
          (prespecifiedBatchPolarizationMinus i j) b hInterior K omega) / 4 := by
  unfold prespecifiedBatchShotInformationMatrixError
    prespecifiedBatchShotTruthObservedInformationMatrix
    prespecifiedBatchShotPredictableFisherMatrix
    prespecifiedBatchShotTruthObservedDirectionalInformation
    prespecifiedBatchShotCenteredObservedInformationError
  ring

def prespecifiedBatchObservedInformationMatrixEntrySharpConstant
    (theta : RLSVector 3) (i j : Fin 3) : Real :=
  (prespecifiedBatchObservedInformationSharpConstant theta
      (prespecifiedBatchPolarizationPlus i j) +
    prespecifiedBatchObservedInformationSharpConstant theta
      (prespecifiedBatchPolarizationMinus i j)) / 8

theorem prespecifiedBatchShotInformationMatrixError_entry_l2_le
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (i j : Fin 3) :
    (∫ omega,
      prespecifiedBatchShotInformationMatrixError
        theta b hInterior K omega i j ^ 2
      ∂exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) <=
      prespecifiedBatchObservedInformationMatrixEntrySharpConstant theta i j /
        (prespecifiedBatchTotalObservations K : Real) := by
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  let hp := prespecifiedBatchPolarizationPlus i j
  let hm := prespecifiedBatchPolarizationMinus i j
  let A := prespecifiedBatchShotCenteredObservedInformationError
    theta hp b hInterior K
  let B := prespecifiedBatchShotCenteredObservedInformationError
    theta hm b hInterior K
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  have hAmem := prespecifiedBatchShotCenteredObservedInformationError_memLp_two
    theta hp b hInterior K
  have hBmem := prespecifiedBatchShotCenteredObservedInformationError_memLp_two
    theta hm b hInterior K
  have hentryMem : MemLp (fun omega => (A omega - B omega) / 4) 2 mu := by
    simpa [div_eq_mul_inv, mul_comm] using (hAmem.sub hBmem).const_mul (4 : Real)⁻¹
  have hleftInt := hentryMem.integrable_sq
  have hrightInt : Integrable (fun omega => (A omega ^ 2 + B omega ^ 2) / 8) mu := by
    exact (hAmem.integrable_sq.add hBmem.integrable_sq).div_const 8
  rw [show (fun omega =>
      prespecifiedBatchShotInformationMatrixError
        theta b hInterior K omega i j ^ 2) =
      fun omega => ((A omega - B omega) / 4) ^ 2 by
        funext omega
        rw [prespecifiedBatchShotInformationMatrixError_apply]
        ]
  calc
    (∫ omega, ((A omega - B omega) / 4) ^ 2 ∂mu) <=
        ∫ omega, (A omega ^ 2 + B omega ^ 2) / 8 ∂mu := by
      apply integral_mono_ae hleftInt hrightInt
      filter_upwards with omega
      nlinarith [sq_nonneg (A omega + B omega)]
    _ = ((∫ omega, A omega ^ 2 ∂mu) +
          (∫ omega, B omega ^ 2 ∂mu)) / 8 := by
      rw [integral_div, integral_add hAmem.integrable_sq hBmem.integrable_sq]
    _ <=
        (prespecifiedBatchObservedInformationSharpConstant theta hp /
            (prespecifiedBatchTotalObservations K : Real) +
          prespecifiedBatchObservedInformationSharpConstant theta hm /
            (prespecifiedBatchTotalObservations K : Real)) / 8 := by
      gcongr
      · exact prespecifiedBatchShotCenteredObservedInformationError_l2_le
          theta hp b hInterior K
      · exact prespecifiedBatchShotCenteredObservedInformationError_l2_le
          theta hm b hInterior K
    _ = prespecifiedBatchObservedInformationMatrixEntrySharpConstant theta i j /
          (prespecifiedBatchTotalObservations K : Real) := by
      unfold prespecifiedBatchObservedInformationMatrixEntrySharpConstant
      ring

def prespecifiedBatchObservedInformationMatrixSharpConstant
    (theta : RLSVector 3) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    prespecifiedBatchObservedInformationMatrixEntrySharpConstant theta i j

def prespecifiedBatchShotInformationMatrixErrorSq
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    prespecifiedBatchShotInformationMatrixError theta b hInterior K omega i j ^ 2

/-- Full matrix mean-square rate at the truth: observed information minus
predictable Fisher is O(1/N_K) in Frobenius square. -/
theorem prespecifiedBatchShotInformationMatrixErrorSq_integral_le
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    (∫ omega,
      prespecifiedBatchShotInformationMatrixErrorSq
        theta b hInterior K omega
      ∂exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) <=
      prespecifiedBatchObservedInformationMatrixSharpConstant theta /
        (prespecifiedBatchTotalObservations K : Real) := by
  unfold prespecifiedBatchShotInformationMatrixErrorSq
    prespecifiedBatchObservedInformationMatrixSharpConstant
  rw [Finset.sum_div]
  rw [integral_finset_sum]
  · apply Finset.sum_le_sum
    intro i hi
    rw [integral_finset_sum]
    · rw [Finset.sum_div]
      exact Finset.sum_le_sum fun j hj =>
        prespecifiedBatchShotInformationMatrixError_entry_l2_le
          theta b hInterior K i j
    · intro j hj
      let hp := prespecifiedBatchPolarizationPlus i j
      let hm := prespecifiedBatchPolarizationMinus i j
      have hmemP :=
        prespecifiedBatchShotCenteredObservedInformationError_memLp_two
          theta hp b hInterior K
      have hmemM :=
        prespecifiedBatchShotCenteredObservedInformationError_memLp_two
          theta hm b hInterior K
      have hmem : MemLp
          (fun omega =>
            prespecifiedBatchShotInformationMatrixError
              theta b hInterior K omega i j) 2
          (exactConcretePredeterminedBatchPathMeasure
            theta b (le_of_lt hInterior)) := by
        rw [show (fun omega =>
            prespecifiedBatchShotInformationMatrixError
              theta b hInterior K omega i j) =
          fun omega =>
            (prespecifiedBatchShotCenteredObservedInformationError
                theta hp b hInterior K omega -
              prespecifiedBatchShotCenteredObservedInformationError
                theta hm b hInterior K omega) / 4 by
          funext omega
          rw [prespecifiedBatchShotInformationMatrixError_apply]]
        simpa [div_eq_mul_inv, mul_comm] using
          (hmemP.sub hmemM).const_mul (4 : Real)⁻¹
      exact hmem.integrable_sq
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    let hp := prespecifiedBatchPolarizationPlus i j
    let hm := prespecifiedBatchPolarizationMinus i j
    have hmemP :=
      prespecifiedBatchShotCenteredObservedInformationError_memLp_two
        theta hp b hInterior K
    have hmemM :=
      prespecifiedBatchShotCenteredObservedInformationError_memLp_two
        theta hm b hInterior K
    have hmem : MemLp
        (fun omega =>
          prespecifiedBatchShotInformationMatrixError
            theta b hInterior K omega i j) 2
        (exactConcretePredeterminedBatchPathMeasure
          theta b (le_of_lt hInterior)) := by
      rw [show (fun omega =>
          prespecifiedBatchShotInformationMatrixError
            theta b hInterior K omega i j) =
        fun omega =>
          (prespecifiedBatchShotCenteredObservedInformationError
              theta hp b hInterior K omega -
            prespecifiedBatchShotCenteredObservedInformationError
              theta hm b hInterior K omega) / 4 by
        funext omega
        rw [prespecifiedBatchShotInformationMatrixError_apply]]
      simpa [div_eq_mul_inv, mul_comm] using
        (hmemP.sub hmemM).const_mul (4 : Real)⁻¹
    exact hmem.integrable_sq

theorem prespecifiedBatch_pilotOrderK_matrixError_l2_bound_tendsto_zero
    (theta : RLSVector 3) :
    Tendsto
      (fun K : Nat =>
        (K : Real) ^ 2 *
          (prespecifiedBatchObservedInformationMatrixSharpConstant theta /
            (prespecifiedBatchTotalObservations K : Real)))
      atTop (nhds 0) := by
  let C := prespecifiedBatchObservedInformationMatrixSharpConstant theta
  have hCnonneg : 0 <= C := by
    unfold C prespecifiedBatchObservedInformationMatrixSharpConstant
      prespecifiedBatchObservedInformationMatrixEntrySharpConstant
      prespecifiedBatchObservedInformationSharpConstant
    positivity
  change Tendsto
    (fun K : Nat =>
      (K : Real) ^ 2 *
        (C / (prespecifiedBatchTotalObservations K : Real)))
    atTop (nhds 0)
  apply squeeze_zero' (g := fun K : Nat => C / (K : Real))
  · filter_upwards with K
    exact mul_nonneg (sq_nonneg (K : Real))
      (div_nonneg hCnonneg
        (Nat.cast_nonneg (prespecifiedBatchTotalObservations K)))
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
    have hKreal : (0 : Real) < K := by exact_mod_cast hK
    rw [prespecifiedBatchTotalObservations_eq]
    calc
      (K : Real) ^ 2 * (C / (((3 * K) ^ 6 : Nat) : Real)) =
        C / (729 * (K : Real) ^ 4) := by
            push_cast
            field_simp
            norm_num
      _ <= C / (K : Real) := by
            rw [div_le_div_iff₀ (by positivity) hKreal]
            have hKone : (1 : Real) <= K := by exact_mod_cast hK
            have hKnonneg : (0 : Real) <= K := le_of_lt hKreal
            have hfactor :
                0 <= (K : Real) * ((K : Real) - 1) *
                  ((K : Real) ^ 2 + (K : Real) + 1) :=
              mul_nonneg
                (mul_nonneg hKnonneg (sub_nonneg.mpr hKone))
                (by nlinarith [sq_nonneg (K : Real)])
            have hKpow : (K : Real) <= (K : Real) ^ 4 := by
              nlinarith
            have hscale : (K : Real) ^ 4 <= 729 * (K : Real) ^ 4 := by
              nlinarith [pow_nonneg hKnonneg 4]
            exact mul_le_mul_of_nonneg_left (hKpow.trans hscale) hCnonneg
  · have hconst :
        Tendsto (fun _ : Nat => C) atTop (nhds C) := tendsto_const_nhds
    simpa [div_eq_mul_inv] using
      hconst.mul
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun K : Nat => (1 : Real) / K) atTop (nhds 0))

end

end QubitOracle.Paper
