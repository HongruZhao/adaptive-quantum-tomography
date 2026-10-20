import QubitOracle.Paper.OneQubitAPSEventualCertificates

namespace QubitOracle.Paper

open MeasureTheory

theorem oneQubitGramEnergy_add
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    oneQubitGramEnergy (A + B) x =
      oneQubitGramEnergy A x + oneQubitGramEnergy B x := by
  simp only [oneQubitGramEnergy, blochDot, Matrix.add_mulVec, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem oneQubitGramEnergy_one (x : Fin 3 → ℝ) :
    oneQubitGramEnergy (1 : Matrix (Fin 3) (Fin 3) ℝ) x = blochNormSq x := by
  simp [oneQubitGramEnergy, blochDot, blochNormSq, Matrix.one_mulVec, pow_two]

theorem oneQubitGramEnergy_vectorOuterProduct
    (v x : Fin 3 → ℝ) :
    oneQubitGramEnergy (SourceFaithfulSelfNormalized.vectorOuterProduct v) x =
      (blochDot v x) ^ 2 := by
  simp only [oneQubitGramEnergy, blochDot,
    SourceFaithfulSelfNormalized.vectorOuterProduct, Matrix.mulVec,
    dotProduct]
  calc
    (∑ i, x i * ∑ j, v i * v j * x j) =
        ∑ i, (x i * v i) * ∑ j, v j * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i, x i * v i) * (∑ j, v j * x j) := by
      rw [Finset.sum_mul]
    _ = (∑ i, v i * x i) ^ 2 := by
      have hswap : (∑ i, x i * v i) = ∑ i, v i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hswap, pow_two]

theorem oneQubitGramEnergy_fin_sum
    {m : ℕ} (A : Fin m → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    oneQubitGramEnergy (∑ q, A q) x = ∑ q, oneQubitGramEnergy (A q) x := by
  classical
  induction m with
  | zero => simp [oneQubitGramEnergy, blochDot]
  | succ m ih =>
      rw [Fin.sum_univ_succ, oneQubitGramEnergy_add, ih]
      conv_rhs => rw [Fin.sum_univ_succ]

/-- Identity regularization plus all leftover rank-one round contributions. -/
def oneQubitScheduleRemainder
    {Omega : Type*} (extraCount : ℕ → ℕ)
    (extraAxis : (n : ℕ) → Fin (extraCount n) → Omega → Fin 3 → ℝ)
    (n : ℕ) (omega : Omega) : Matrix (Fin 3) (Fin 3) ℝ :=
  1 + ∑ q, SourceFaithfulSelfNormalized.vectorOuterProduct (extraAxis n q omega)

theorem oneQubitScheduleRemainder_nonnegative
    {Omega : Type*} (extraCount : ℕ → ℕ)
    (extraAxis : (n : ℕ) → Fin (extraCount n) → Omega → Fin 3 → ℝ)
    (n : ℕ) (omega : Omega) (x : Fin 3 → ℝ) :
    0 ≤ oneQubitGramEnergy
      (oneQubitScheduleRemainder extraCount extraAxis n omega) x := by
  rw [oneQubitScheduleRemainder, oneQubitGramEnergy_add,
    oneQubitGramEnergy_one, oneQubitGramEnergy_fin_sum]
  have hNorm : 0 ≤ blochNormSq x := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have hExtra : 0 ≤ ∑ q, oneQubitGramEnergy
      (SourceFaithfulSelfNormalized.vectorOuterProduct (extraAxis n q omega)) x := by
    apply Finset.sum_nonneg
    intro q hq
    rw [oneQubitGramEnergy_vectorOuterProduct]
    exact sq_nonneg _
  positivity

/-- Schedule-level certificate: only a block count and exact round bookkeeping remain. -/
structure OneQubitPauliBlockScheduleCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (start : ℕ) where
  start_ge_two : 2 ≤ start
  blocks : ℕ → ℕ
  extraCount : ℕ → ℕ
  extraAxis : (n : ℕ) → Fin (extraCount n) → Omega → Fin 3 → ℝ
  gram_decomposition : ∀ n omega,
    PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
      pauliForcedExplorationGram (blocks n) +
        oneQubitScheduleRemainder extraCount extraAxis n omega
  block_lower : ∀ n, start ≤ n →
    oneQubitThreeQuarterExploration n ≤ (blocks n : ℝ)
  round_feasible : ∀ n, start ≤ n → 3 * blocks n ≤ n

def OneQubitPauliBlockScheduleCertificate.toEventualGramCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitPauliBlockScheduleCertificate protocol hTheta start) :
    OneQubitEventualPauliBlockGramCertificate protocol hTheta start where
  start_ge_two := certificate.start_ge_two
  blocks := certificate.blocks
  remainder := oneQubitScheduleRemainder certificate.extraCount certificate.extraAxis
  gram_decomposition := certificate.gram_decomposition
  remainder_nonnegative := oneQubitScheduleRemainder_nonnegative
    certificate.extraCount certificate.extraAxis
  block_lower := certificate.block_lower

theorem OneQubitPauliBlockScheduleCertificate.controllerConvergence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitPauliBlockScheduleCertificate protocol hTheta start) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta 1) theta)
        Filter.atTop (fun _ => 0) :=
  certificate.toEventualGramCertificate.controllerConvergence

end QubitOracle.Paper
