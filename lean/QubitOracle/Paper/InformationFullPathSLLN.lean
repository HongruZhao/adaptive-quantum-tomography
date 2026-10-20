import QubitOracle.Paper.AdaptiveInformationPath
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory

/-- Prepend one fixed observation to an infinite tail sequence. -/
def prependSequence {E : Type*} (first : E) (tail : ℕ → E) : ℕ → E
  | 0 => first
  | n + 1 => tail n

@[simp] theorem prependSequence_zero {E : Type*} (first : E) (tail : ℕ → E) :
    prependSequence first tail 0 = first := rfl

@[simp] theorem prependSequence_succ {E : Type*} (first : E) (tail : ℕ → E) (n : ℕ) :
    prependSequence first tail (n + 1) = tail n := rfl

/-- Sum of a prepended sequence over its first `n + 1` terms. -/
theorem sum_range_prependSequence
    {E : Type*} [AddCommMonoid E] (first : E) (tail : ℕ → E) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), prependSequence first tail k =
      first + ∑ k ∈ Finset.range n, tail k := by
  induction n with
  | zero => simp [prependSequence]
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1 + 1), prependSequence first tail k) =
            (∑ k ∈ Finset.range (n + 1), prependSequence first tail k) +
              prependSequence first tail (n + 1) := by
                rw [Finset.sum_range_succ]
        _ = (first + ∑ k ∈ Finset.range n, tail k) + tail n := by
              rw [ih, prependSequence_succ]
        _ = first + ∑ k ∈ Finset.range (n + 1), tail k := by
              rw [Finset.sum_range_succ]
              ac_rfl

/-- A fixed finite-prefix contribution vanishes after normalization. -/
theorem fixed_normalized_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • x) atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  simpa using hn.inv_tendsto_atTop.smul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (nhds x))

/-- Prepending one fixed term preserves a zero limit of normalized partial
sums.  This is the exact one-shot reconciliation needed for the path law. -/
theorem normalized_prependSequence_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (first : E) (tail : ℕ → E)
    (htail : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, tail k)
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, prependSequence first tail k)
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hscaled : Tendsto
      (fun n : ℕ =>
        ((n : ℝ) / ((n : ℝ) + 1)) •
          ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, tail k))
      atTop (nhds 0) := by
    simpa using hratio.smul htail
  have hscaleEq :
      (fun n : ℕ =>
        ((n : ℝ) / ((n : ℝ) + 1)) •
          ((n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, tail k)) =
      (fun n : ℕ =>
        ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range n, tail k) := by
    funext n
    cases n with
    | zero => simp
    | succ n =>
        rw [smul_smul]
        congr 1
        have hn : (Nat.succ n : ℝ) ≠ 0 := by positivity
        have hn1 : (Nat.succ n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hn, hn1]
  have htailShift : Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range n, tail k)
      atTop (nhds 0) := by
    rw [← hscaleEq]
    exact hscaled
  have hfirstShift : Tendsto
      (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • first) atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => (n : ℝ)⁻¹ • first) 1).2
      (fixed_normalized_tendsto_zero first)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hshifted : Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1)⁻¹ •
          ∑ k ∈ Finset.range (n + 1), prependSequence first tail k)
      atTop (nhds 0) := by
    simpa [sum_range_prependSequence, smul_add] using
      hfirstShift.add htailShift
  apply (Filter.tendsto_add_atTop_iff_nat
    (f := fun n : ℕ =>
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, prependSequence first tail k) 1).1
  simpa only [Nat.cast_add, Nat.cast_one] using hshifted

/-- Almost-sure form of normalized finite-prefix removal. -/
theorem ae_normalized_prependSequence_tendsto_zero
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) (first : Omega → E) (tail : Omega → ℕ → E)
    (htail : ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, tail omega k)
        atTop (nhds 0)) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ •
            ∑ k ∈ Finset.range n,
              prependSequence (first omega) (tail omega) k)
        atTop (nhds 0) := by
  filter_upwards [htail] with omega homega
  exact normalized_prependSequence_tendsto_zero
    (first omega) (tail omega) homega

/-- Information innovation contributed by the initial shot. -/
def mixedInitialInformationInnovation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) : OracleMatrix :=
  mixedInformationInnovation q r axis [] (omega 0).1

/-- Information-innovation tail beginning after the initial shot. -/
def mixedTailInformationInnovation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (k : ℕ) : OracleMatrix :=
  mixedInformationInnovation q r axis
    (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
    (omega (k + 1)).1

/-- Information innovation sequence including the initial shot. -/
def mixedPathInformationInnovationAllShots
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) : ℕ → OracleMatrix :=
  prependSequence
    (mixedInitialInformationInnovation q r axis omega)
    (mixedTailInformationInnovation q r axis omega)

/-- Named-tail form of the post-initial adaptive information SLLN. -/
theorem mixedTailInformationInnovation_strongLaw_adaptiveTrajectoryMeasure
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1) :
    ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ •
            ∑ k ∈ Finset.range n,
              mixedTailInformationInnovation q r axis omega k)
        atTop (nhds 0) := by
  simpa only [mixedTailInformationInnovation] using
    (mixedInformationInnovation_strongLaw_adaptiveTrajectoryMeasure
      (Theta := Theta) (M := M) (Y := Y)
      q p theta r axis hr haxis)

/-- Pointwise all-shot information-SLLN event.  Naming the event keeps the
finite-prefix argument separate from the adaptive path-measure layer. -/
def MixedInformationFullSLLNAt
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) : Prop :=
  Tendsto
    (fun n : ℕ =>
      (n : ℝ)⁻¹ •
        ∑ k ∈ Finset.range n,
          prependSequence
            (mixedInitialInformationInnovation q r axis omega)
            (mixedTailInformationInnovation q r axis omega) k)
    atTop (nhds 0)

/-- A post-initial information SLLN implies the exact all-shot event. -/
theorem mixedInformationFullSLLNAt_of_tail
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y)
    (htail : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            mixedTailInformationInnovation q r axis omega k)
      atTop (nhds 0)) :
    MixedInformationFullSLLNAt q r axis omega := by
  unfold MixedInformationFullSLLNAt
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have htail_i := tendsto_pi_nhds.1 htail i
  have htail_ij := tendsto_pi_nhds.1 htail_i j
  have htail_ij' : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            mixedTailInformationInnovation q r axis omega k i j)
      atTop (nhds 0) := by
    simpa only [Matrix.smul_apply, Matrix.sum_apply, Matrix.zero_apply] using htail_ij
  have hfull_ij := normalized_prependSequence_tendsto_zero
    (E := ℝ)
    (mixedInitialInformationInnovation q r axis omega i j)
    (fun k => mixedTailInformationInnovation q r axis omega k i j)
    htail_ij'
  have hseq (k : ℕ) :
      prependSequence
          (mixedInitialInformationInnovation q r axis omega)
          (mixedTailInformationInnovation q r axis omega) k i j =
        prependSequence
          (mixedInitialInformationInnovation q r axis omega i j)
          (fun t => mixedTailInformationInnovation q r axis omega t i j) k := by
    cases k <;> rfl
  simpa only [Matrix.smul_apply, Matrix.sum_apply, Matrix.zero_apply, hseq] using hfull_ij

/-- Exact all-shot almost-sure information-SLLN statement. -/
def MixedInformationFullSLLNStatement
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ) : Prop :=
  ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
    MixedInformationFullSLLNAt q r axis omega

/- Actual all-shot path-space information SLLN. -/
set_option maxHeartbeats 1000000 in
theorem mixedInformationInnovation_fullStrongLaw_adaptiveTrajectoryMeasure
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1) :
    MixedInformationFullSLLNStatement q p theta r axis := by
  unfold MixedInformationFullSLLNStatement
  exact
    (mixedTailInformationInnovation_strongLaw_adaptiveTrajectoryMeasure
      (Theta := Theta) (M := M) (Y := Y)
      q p theta r axis hr haxis).mono fun omega homega =>
        mixedInformationFullSLLNAt_of_tail q r axis omega homega

end QubitOracle.Paper
