import QubitOracle.Paper.OneQubitRequiredPauliBlocks

/-!
# A fully explicit cyclic-Pauli controller certificate

This module closes the finite schedule algebra for the concrete one-qubit protocol
that measures the three Pauli coordinate axes cyclically.  It is deliberately a
special non-LAN result: the probability-space premises are kept explicit, while
the complete-block Gram decomposition and eventual excitation are proved here.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- The deterministic cyclic Pauli axis at round `k`. -/
def oneQubitCyclicPauliAxis (k : ℕ) : Fin 3 → ℝ :=
  pauliCoordinateAxis ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩

@[simp]
theorem oneQubitCyclicPauliAxis_three_mul_add (block q : ℕ) :
    oneQubitCyclicPauliAxis (3 * block + q) = oneQubitCyclicPauliAxis q := by
  unfold oneQubitCyclicPauliAxis
  congr 1
  apply Fin.ext
  simp [Nat.add_mod]

@[simp]
theorem oneQubitCyclicPauliAxis_fin (q : Fin 3) :
    oneQubitCyclicPauliAxis q.1 = pauliCoordinateAxis q := by
  unfold oneQubitCyclicPauliAxis
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt q.2

/-- Unregularized Gram sum of the first `n` cyclic Pauli regressors. -/
def oneQubitCyclicPauliGram (n : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ k ∈ Finset.range n,
    SourceFaithfulSelfNormalized.vectorOuterProduct (oneQubitCyclicPauliAxis k)

theorem pauliForcedExplorationGram_succ (blocks : ℕ) :
    pauliForcedExplorationGram (blocks + 1) =
      pauliForcedExplorationGram blocks + pauliForcedOneBlockGram := by
  ext i j
  simp [pauliForcedExplorationGram]
  ring

theorem oneQubitCyclicPauli_three_block (blocks : ℕ) :
    (∑ q ∈ Finset.range 3,
        SourceFaithfulSelfNormalized.vectorOuterProduct
          (oneQubitCyclicPauliAxis (3 * blocks + q))) =
      pauliForcedOneBlockGram := by
  rw [← Fin.sum_univ_eq_sum_range]
  ext i j
  simp [pauliForcedOneBlockGram, Matrix.sum_apply,
    SourceFaithfulSelfNormalized.vectorOuterProduct]

theorem oneQubitCyclicPauliGram_three_mul (blocks : ℕ) :
    oneQubitCyclicPauliGram (3 * blocks) =
      pauliForcedExplorationGram blocks := by
  induction blocks with
  | zero =>
      ext i j
      simp [oneQubitCyclicPauliGram, pauliForcedExplorationGram]
  | succ blocks ih =>
      rw [show 3 * (blocks + 1) = 3 * blocks + 3 by omega]
      unfold oneQubitCyclicPauliGram
      rw [Finset.sum_range_add]
      change oneQubitCyclicPauliGram (3 * blocks) +
          (∑ q ∈ Finset.range 3,
            SourceFaithfulSelfNormalized.vectorOuterProduct
              (oneQubitCyclicPauliAxis (3 * blocks + q))) =
        pauliForcedExplorationGram (blocks + 1)
      rw [ih, oneQubitCyclicPauli_three_block,
        pauliForcedExplorationGram_succ]

theorem oneQubitCyclicPauliGram_add (m r : ℕ) :
    oneQubitCyclicPauliGram (m + r) =
      oneQubitCyclicPauliGram m +
        ∑ q ∈ Finset.range r,
          SourceFaithfulSelfNormalized.vectorOuterProduct
            (oneQubitCyclicPauliAxis (m + q)) := by
  unfold oneQubitCyclicPauliGram
  exact Finset.sum_range_add _ m r

theorem oneQubitCyclicPauliGram_div_mod (n : ℕ) :
    oneQubitCyclicPauliGram n =
      pauliForcedExplorationGram (n / 3) +
        ∑ q : Fin (n % 3),
          SourceFaithfulSelfNormalized.vectorOuterProduct
            (oneQubitCyclicPauliAxis q.1) := by
  have hn : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  calc
    oneQubitCyclicPauliGram n =
        oneQubitCyclicPauliGram (3 * (n / 3) + n % 3) := by rw [hn]
    _ = oneQubitCyclicPauliGram (3 * (n / 3)) +
          ∑ q ∈ Finset.range (n % 3),
            SourceFaithfulSelfNormalized.vectorOuterProduct
              (oneQubitCyclicPauliAxis (3 * (n / 3) + q)) :=
      oneQubitCyclicPauliGram_add _ _
    _ = pauliForcedExplorationGram (n / 3) +
          ∑ q ∈ Finset.range (n % 3),
            SourceFaithfulSelfNormalized.vectorOuterProduct
              (oneQubitCyclicPauliAxis q) := by
      rw [oneQubitCyclicPauliGram_three_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro q hq
      rw [oneQubitCyclicPauliAxis_three_mul_add]
    _ = pauliForcedExplorationGram (n / 3) +
          ∑ q : Fin (n % 3),
            SourceFaithfulSelfNormalized.vectorOuterProduct
              (oneQubitCyclicPauliAxis q.1) := by
      congr 1
      exact (Fin.sum_univ_eq_sum_range
        (fun q => SourceFaithfulSelfNormalized.vectorOuterProduct
          (oneQubitCyclicPauliAxis q)) (n % 3)).symm

/-- The at-most-two incomplete axes after all complete cyclic Pauli blocks. -/
def oneQubitCyclicPauliExtraAxis {Omega : Type*}
    (n : ℕ) (q : Fin (n % 3)) (_omega : Omega) : Fin 3 → ℝ :=
  oneQubitCyclicPauliAxis q.1

theorem oneQubitAPSGram_eq_one_add_cyclicPauliGram
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (hAxis : ∀ (k : ℕ) (omega : Omega), axis k omega = oneQubitCyclicPauliAxis k)
    (n : ℕ) (omega : Omega) :
    PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
      1 + oneQubitCyclicPauliGram n := by
  ext i j
  simp [PopularRLSConditions.aps2011Theorem2Gram,
    PopularRLSConditions.aps2011Theorem2Regularizer,
    SourceFaithfulSelfNormalized.regularizedGram,
    SourceFaithfulSelfNormalized.gramProcess,
    BinaryQubitRLSReducedProbabilityPremises.toSelfNormalizedMartingaleData,
    selfNormalizedMartingaleData_of_boundedCenteredNoise,
    oneQubitCyclicPauliGram, hAxis]

theorem oneQubitAPSGram_cyclicPauli_decomposition
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (hAxis : ∀ (k : ℕ) (omega : Omega), axis k omega = oneQubitCyclicPauliAxis k)
    (n : ℕ) (omega : Omega) :
    PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
      pauliForcedExplorationGram (n / 3) +
        oneQubitScheduleRemainder (fun n => n % 3)
          (oneQubitCyclicPauliExtraAxis (Omega := Omega)) n omega := by
  rw [oneQubitAPSGram_eq_one_add_cyclicPauliGram protocol hTheta hAxis]
  rw [oneQubitCyclicPauliGram_div_mod]
  simp [oneQubitScheduleRemainder, oneQubitCyclicPauliExtraAxis]
  abel

/-- Exact finite schedule certificate for the cyclic-Pauli protocol. -/
theorem exists_oneQubitCyclicPauliScheduleCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (hAxis : ∀ (k : ℕ) (omega : Omega), axis k omega = oneQubitCyclicPauliAxis k) :
    Nonempty (Σ start, OneQubitPauliBlockScheduleCertificate protocol hTheta start) := by
  obtain ⟨start, hStart, hRequired⟩ := exists_oneQubitRequiredPauliBlocks_start
  refine ⟨⟨start, ?_⟩⟩
  refine
    { start_ge_two := hStart
      blocks := fun n => n / 3
      extraCount := fun n => n % 3
      extraAxis := oneQubitCyclicPauliExtraAxis (Omega := Omega)
      gram_decomposition := ?_
      block_lower := ?_
      round_feasible := ?_ }
  · intro n omega
    exact oneQubitAPSGram_cyclicPauli_decomposition protocol hTheta hAxis n omega
  · intro n hn
    have hDiv : oneQubitRequiredPauliBlocks n ≤ n / 3 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by
        have h := hRequired n hn
        omega)
    exact (oneQubitThreeQuarterExploration_le_requiredPauliBlocks n).trans
      (by exact_mod_cast hDiv)
  · intro n _hn
    exact Nat.mul_div_le n 3

/--
For the explicit cyclic-Pauli one-qubit design, APS ridge RLS is almost-surely
consistent and converges in measure.  The only scientific input inherited by
this endpoint is APS 2011, Theorem 2; all schedule algebra is kernel-proved.
-/
theorem oneQubitCyclicPauliControllerConvergence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega} [MeasureTheory.IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (hAxis : ∀ (k : ℕ) (omega : Omega), axis k omega = oneQubitCyclicPauliAxis k) :
    AlmostSureControllerRate mu (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu,
        Filter.Tendsto (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
          Filter.atTop (nhds theta)) ∧
      MeasureTheory.TendstoInMeasure mu
        (scaledControllerNormError (oneQubitAPSRidgeController protocol hTheta 1) theta)
        Filter.atTop (fun _ => 0) := by
  obtain ⟨⟨start, certificate⟩⟩ :=
    exists_oneQubitCyclicPauliScheduleCertificate protocol hTheta hAxis
  exact certificate.controllerConvergence

end

end QubitOracle.Paper
