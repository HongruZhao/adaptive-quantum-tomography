import QubitOracle.Paper.HistoryDependentInformationMartingale

/-!
# Finite adaptive Born-score closure

This module proves the finite-alphabet probability identities that were
previously hidden behind the score-martingale, covariance, and Lindeberg
interfaces.  The measurement policy may depend on the complete observed
history.  The outcome law is the actual `OutcomeKernel`, and integration is
with respect to the corresponding one-step adaptive joint kernel.

The only model input is the finite Born-score normalization identity
`sum_y p_y score_y = 0` and a deterministic score envelope.  For an explicit
POVM these are finite algebraic obligations, not asymptotic assumptions.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- Conditional Fisher information of a history-dependent finite adaptive
score.  This is the conditional second moment of the score under both the
predictable measurement policy and the Born outcome kernel. -/
def finiteAdaptiveScoreInformation
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (history : SequentialHistory M Y) : Matrix D D Real :=
  fun i j =>
    ∑ m : M, q.mass history m *
      ∑ y : Y, p.mass (theta, m) y *
        (score history m y i * score history m y j)

/-- The finite Born normalization identity implies exact zero conditional
mean of every score coordinate under the adaptive setting-outcome kernel. -/
theorem integral_finiteAdaptiveScore_adaptiveJointKernel_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (hcenter : forall history m i,
      (∑ y : Y, p.mass (theta, m) y * score history m y i) = 0)
    (history : SequentialHistory M Y) (i : D) :
    ∫ z, score history z.1 z.2 i
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass history)
          ((adaptiveJointKernel q p theta).mass_nonneg history)
          ((adaptiveJointKernel q p theta).sum_mass history) = 0 := by
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type]
  change
    (∑ m : M, ∑ y : Y,
      (q.mass history m * p.mass (theta, m) y) *
        score history m y i) = 0
  calc
    (∑ m : M, ∑ y : Y,
        (q.mass history m * p.mass (theta, m) y) *
          score history m y i) =
        ∑ m : M, q.mass history m *
          (∑ y : Y, p.mass (theta, m) y * score history m y i) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rw [hcenter history m i, mul_zero]

/-- Exact conditional covariance/Fisher identity for the actual finite
adaptive setting-outcome kernel. -/
theorem integral_finiteAdaptiveScore_mul_eq_information
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (history : SequentialHistory M Y) (i j : D) :
    ∫ z, score history z.1 z.2 i * score history z.1 z.2 j
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass history)
          ((adaptiveJointKernel q p theta).mass_nonneg history)
          ((adaptiveJointKernel q p theta).sum_mass history) =
      finiteAdaptiveScoreInformation q p theta score history i j := by
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type]
  change
    (∑ m : M, ∑ y : Y,
      (q.mass history m * p.mass (theta, m) y) *
        (score history m y i * score history m y j)) =
      ∑ m : M, q.mass history m *
        ∑ y : Y, p.mass (theta, m) y *
          (score history m y i * score history m y j)
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- One conditional Lindeberg sum for a normalized coordinate score. -/
def finiteAdaptiveScoreConditionalLindeberg
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (normalizer : Nat) (epsilon : Real)
    (history : SequentialHistory M Y) (i : D) : Real :=
  ∑ m : M, q.mass history m *
    ∑ y : Y, p.mass (theta, m) y *
      let x := score history m y i / Real.sqrt (normalizer : Real)
      (x ^ 2 * if epsilon < |x| then 1 else 0)

/-- A uniform unnormalized score bound makes the normalized one-step
conditional Lindeberg contribution exactly zero once `B / sqrt n <= epsilon`.
-/
theorem finiteAdaptiveScoreConditionalLindeberg_eq_zero_of_bound
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (normalizer : Nat) (hnormalizer : 0 < normalizer)
    (epsilon B : Real)
    (i : D)
    (hbound : forall history m y,
      |score history m y i| <= B)
    (hsmall : B / Real.sqrt (normalizer : Real) <= epsilon)
    (history : SequentialHistory M Y) :
    finiteAdaptiveScoreConditionalLindeberg
      q p theta score normalizer epsilon history i = 0 := by
  have hnormalizerReal : 0 < (normalizer : Real) := by
    exact_mod_cast hnormalizer
  have hsqrt : 0 < Real.sqrt (normalizer : Real) :=
    Real.sqrt_pos.2 hnormalizerReal
  unfold finiteAdaptiveScoreConditionalLindeberg
  apply Finset.sum_eq_zero
  intro m _
  suffices hinner :
      (∑ y : Y, p.mass (theta, m) y *
        (let x := score history m y i / Real.sqrt (normalizer : Real)
         x ^ 2 * if epsilon < |x| then 1 else 0)) = 0 by
    rw [hinner, mul_zero]
  apply Finset.sum_eq_zero
  intro y _
  have hx :
      |score history m y i / Real.sqrt (normalizer : Real)| <= epsilon := by
    calc
      |score history m y i / Real.sqrt (normalizer : Real)| =
          |score history m y i| / Real.sqrt (normalizer : Real) := by
            rw [abs_div, abs_of_pos hsqrt]
      _ <= B / Real.sqrt (normalizer : Real) :=
        (div_le_div_iff_of_pos_right hsqrt).2 (hbound history m y)
      _ <= epsilon := hsmall
  have hnot :
      ¬ (epsilon <
        |score history m y i / Real.sqrt (normalizer : Real)|) :=
    not_lt_of_ge hx
  simp [hnot]

/-- Every fixed deterministic score envelope becomes negligible after the
root-sample-size normalization. -/
theorem constant_div_sqrt_nat_tendsto_zero (B : Real) :
    Tendsto (fun n : Nat => B / Real.sqrt (n : Real)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : Nat => Real.sqrt (n : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : Nat => (Real.sqrt (n : Real))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : Nat => B * (Real.sqrt (n : Real))⁻¹)
        atTop (nhds (B * 0)))

/-- Conditional Lindeberg for an arbitrary row of predictable histories is
eventually identically zero.  This is stronger than convergence in
probability and uses no limit theorem. -/
theorem finiteAdaptiveScoreRowLindeberg_eventually_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (score : SequentialHistory M Y -> M -> Y -> D -> Real)
    (histories : Nat -> SequentialHistory M Y)
    (i : D) (B epsilon : Real) (hepsilon : 0 < epsilon)
    (hbound : forall history m y,
      |score history m y i| <= B) :
    Filter.Eventually (fun n : Nat =>
      (∑ k ∈ Finset.range n,
        finiteAdaptiveScoreConditionalLindeberg
          q p theta score n epsilon (histories k) i) = 0) atTop := by
  have hsmall : Filter.Eventually (fun n : Nat =>
      B / Real.sqrt (n : Real) < epsilon) atTop :=
    (constant_div_sqrt_nat_tendsto_zero B).eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hnsmall hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  apply Finset.sum_eq_zero
  intro k _
  exact finiteAdaptiveScoreConditionalLindeberg_eq_zero_of_bound
    q p theta score n hnpos epsilon B i hbound hnsmall.le (histories k)

end

end QubitOracle.Paper
