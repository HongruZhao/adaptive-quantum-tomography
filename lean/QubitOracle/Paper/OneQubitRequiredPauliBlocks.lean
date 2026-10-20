import QubitOracle.Paper.OneQubitScheduleGramReduction

namespace QubitOracle.Paper

open Filter MeasureTheory

/-- The least integer number of complete Pauli blocks dominating `n^(3/4)`. -/
noncomputable def oneQubitRequiredPauliBlocks (n : ℕ) : ℕ :=
  ⌈oneQubitThreeQuarterExploration n⌉₊

theorem oneQubitThreeQuarterExploration_le_requiredPauliBlocks (n : ℕ) :
    oneQubitThreeQuarterExploration n ≤ (oneQubitRequiredPauliBlocks n : ℝ) := by
  exact Nat.le_ceil _

theorem oneQubitRequiredPauliBlocks_eventually_round_feasible :
    ∀ᶠ n : ℕ in atTop, 3 * oneQubitRequiredPauliBlocks n ≤ n := by
  have hInv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ :=
    (Metric.tendsto_atTop.1 oneQubitThreeQuarterExploration_fraction_tendsto_zero)
      ((1 : ℝ) / 12) (by norm_num)
  obtain ⟨N₂, hN₂⟩ :=
    (Metric.tendsto_atTop.1 hInv) ((1 : ℝ) / 12) (by norm_num)
  refine Filter.eventually_atTop.2 ⟨max 1 (max N₁ N₂), ?_⟩
  intro n hn
  have hnOne : 1 ≤ n := (le_max_left 1 (max N₁ N₂)).trans hn
  have hn₁ : N₁ ≤ n := (le_max_of_le_right (le_max_left N₁ N₂)).trans hn
  have hn₂ : N₂ ≤ n := (le_max_of_le_right (le_max_right N₁ N₂)).trans hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnOne
  have hRatioDist := hN₁ n hn₁
  have hInvDist := hN₂ n hn₂
  have hRatio : oneQubitThreeQuarterExploration n / (n : ℝ) < (1 : ℝ) / 12 := by
    have hNonnegative : 0 ≤ oneQubitThreeQuarterExploration n := by
      exact Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 4)
    have hRatioNonnegative : 0 ≤ oneQubitThreeQuarterExploration n / (n : ℝ) :=
      div_nonneg hNonnegative hnReal.le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hRatioNonnegative] at hRatioDist
    exact hRatioDist
  have hOneDiv : (1 : ℝ) / (n : ℝ) < (1 : ℝ) / 12 := by
    have hle : ((n : ℝ))⁻¹ ≤ |((n : ℝ))⁻¹| := le_abs_self _
    have hinvlt := hle.trans_lt (by simpa [Real.dist_eq] using hInvDist)
    simpa [one_div] using hinvlt
  have hExploration : oneQubitThreeQuarterExploration n < (1 / 12 : ℝ) * n :=
    (div_lt_iff₀ hnReal).mp hRatio
  have hOne : (1 : ℝ) < (1 / 12 : ℝ) * n :=
    (div_lt_iff₀ hnReal).mp hOneDiv
  have hNonnegative : 0 ≤ oneQubitThreeQuarterExploration n := by
    exact Real.rpow_nonneg (Nat.cast_nonneg n) (3 / 4)
  have hCeil : (oneQubitRequiredPauliBlocks n : ℝ) <
      oneQubitThreeQuarterExploration n + 1 := by
    simpa [oneQubitRequiredPauliBlocks] using Nat.ceil_lt_add_one hNonnegative
  have hReal : (3 : ℝ) * (oneQubitRequiredPauliBlocks n : ℝ) ≤ (n : ℝ) := by
    nlinarith
  exact_mod_cast hReal

theorem exists_oneQubitRequiredPauliBlocks_start :
    ∃ start, 2 ≤ start ∧
      ∀ n, start ≤ n → 3 * oneQubitRequiredPauliBlocks n ≤ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    oneQubitRequiredPauliBlocks_eventually_round_feasible
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  exact hN n ((le_max_right 2 N).trans hn)

theorem exists_oneQubitRequiredPauliScheduleCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (extraCount : ℕ → ℕ)
    (extraAxis : (n : ℕ) → Fin (extraCount n) → Omega → Fin 3 → ℝ)
    (hGram : ∀ n omega,
      PopularRLSConditions.aps2011Theorem2Gram
          (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
        pauliForcedExplorationGram (oneQubitRequiredPauliBlocks n) +
          oneQubitScheduleRemainder extraCount extraAxis n omega) :
    Nonempty (Σ start, OneQubitPauliBlockScheduleCertificate protocol hTheta start) := by
  obtain ⟨start, hStart, hFeasible⟩ := exists_oneQubitRequiredPauliBlocks_start
  refine ⟨⟨start, {
    start_ge_two := hStart
    blocks := oneQubitRequiredPauliBlocks
    extraCount := extraCount
    extraAxis := extraAxis
    gram_decomposition := hGram
    block_lower := ?_
    round_feasible := hFeasible }⟩⟩
  intro n hn
  exact oneQubitThreeQuarterExploration_le_requiredPauliBlocks n

theorem oneQubitControllerConvergence_of_requiredPauliGramDecomposition
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1)
    (extraCount : ℕ → ℕ)
    (extraAxis : (n : ℕ) → Fin (extraCount n) → Omega → Fin 3 → ℝ)
    (hGram : ∀ n omega,
      PopularRLSConditions.aps2011Theorem2Gram
          (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
        pauliForcedExplorationGram (oneQubitRequiredPauliBlocks n) +
          oneQubitScheduleRemainder extraCount extraAxis n omega) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta 1) theta)
        Filter.atTop (fun _ => 0) := by
  obtain ⟨⟨start, certificate⟩⟩ :=
    exists_oneQubitRequiredPauliScheduleCertificate
      protocol hTheta extraCount extraAxis hGram
  exact certificate.controllerConvergence

end QubitOracle.Paper
