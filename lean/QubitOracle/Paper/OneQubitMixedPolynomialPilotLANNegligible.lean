import Mathlib.Probability.Moments.Variance
import QubitOracle.Paper.OneQubitPauliPilotBornProductLaw
import QubitOracle.Paper.OneQubitLogTaylorBound
import QubitOracle.Paper.QubitFoundations

/-!
# Negligibility of the Pauli pilot in mixed-qubit LAN

This file treats only the deterministic Pauli pilot of the concrete mixed-qubit
polynomial schedule.  At row \`n\`, there are

* \`q(n) = (n + 1)^5\` complete three-Pauli blocks, and
* the LAN normalization is \`N(n) = 3 * (n + 1)^6\`.

All probabilities are taken under the explicit finite Born product measure on
\`Fin q(n) -> Fin 3 -> Bool\`.  There is no CLT and no asymptotic information
premise.  The strict interior assumption \`blochNormSq theta < 1\` supplies a
canonical positive denominator margin.

The main result is
\`mixedPolynomialPilotLogLikelihood_negligibleInProbability\`: the complete
pilot log-likelihood contribution converges to zero in the row-specific
finite-measure sense.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace QubitOracle.Paper

noncomputable section

local instance mixedPilotPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedPilotPathMeasurableSingletonClass (q : ℕ) :
    MeasurableSingletonClass (PauliPilotPath q) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

local instance mixedPilotBlockMeasurableSpace :
    MeasurableSpace PauliPilotBlock := ⊤

local instance mixedPilotBlockMeasurableSingletonClass :
    MeasurableSingletonClass PauliPilotBlock where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-! ## Strict interior geometry and the canonical score envelope -/

/-- Strict interior of the mixed one-qubit Bloch ball. -/
def MixedPilotStrictInterior (theta : RLSVector 3) : Prop :=
  QubitOracle.blochNormSq theta < 1

/-- Strict interior implies the physicality condition required by the explicit
Born product law. -/
theorem mixedPilotStrictInterior_physical
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    PauliPilotPhysicalBloch theta :=
  le_of_lt hInterior

/-- Every coordinate of a strictly interior Bloch vector has absolute value
strictly smaller than one. -/
theorem mixedPilotStrictInterior_coordinate_abs_lt_one
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (j : Fin 3) :
    |theta j| < 1 := by
  have hj : theta j ^ 2 ≤ QubitOracle.blochNormSq theta := by
    unfold QubitOracle.blochNormSq
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg (theta i)) (Finset.mem_univ j)
  have hsq : theta j ^ 2 < 1 := hj.trans_lt hInterior
  have habsSq : |theta j| ^ 2 < 1 := by
    simpa [sq_abs] using hsq
  nlinarith [abs_nonneg (theta j)]

/-- Largest absolute Bloch coordinate, written concretely for \`Fin 3\`. -/
def mixedPilotMaxAbsCoordinate (theta : RLSVector 3) : ℝ :=
  max |theta 0| (max |theta 1| |theta 2|)

/-- Every coordinate is bounded by the concrete maximum. -/
theorem mixedPilot_coordinate_abs_le_max
    (theta : RLSVector 3) (j : Fin 3) :
    |theta j| ≤ mixedPilotMaxAbsCoordinate theta := by
  fin_cases j <;> simp [mixedPilotMaxAbsCoordinate]

/-- The concrete maximum is strictly below one in the mixed interior. -/
theorem mixedPilot_maxAbsCoordinate_lt_one
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    mixedPilotMaxAbsCoordinate theta < 1 := by
  unfold mixedPilotMaxAbsCoordinate
  exact max_lt
    (mixedPilotStrictInterior_coordinate_abs_lt_one theta hInterior 0)
    (max_lt
      (mixedPilotStrictInterior_coordinate_abs_lt_one theta hInterior 1)
      (mixedPilotStrictInterior_coordinate_abs_lt_one theta hInterior 2))

/-- Canonical positive denominator margin \`1 - max_j |theta_j|\`. -/
def mixedPilotInteriorMargin (theta : RLSVector 3) : ℝ :=
  1 - mixedPilotMaxAbsCoordinate theta

theorem mixedPilotInteriorMargin_pos
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    0 < mixedPilotInteriorMargin theta := by
  unfold mixedPilotInteriorMargin
  linarith [mixedPilot_maxAbsCoordinate_lt_one theta hInterior]

theorem mixedPilot_coordinate_abs_le_one_sub_margin
    (theta : RLSVector 3) (j : Fin 3) :
    |theta j| ≤ 1 - mixedPilotInteriorMargin theta := by
  unfold mixedPilotInteriorMargin
  simpa only [sub_sub_cancel] using mixedPilot_coordinate_abs_le_max theta j

/-- Every Bernoulli score denominator is bounded below by the canonical
interior margin. -/
theorem mixedPilot_scoreDenominator_ge_margin
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (j : Fin 3) (outcome : Bool) :
    mixedPilotInteriorMargin theta ≤
      1 + pauliOutcomeSign outcome * theta j := by
  have habs := mixedPilot_coordinate_abs_le_one_sub_margin theta j
  cases outcome with
  | false =>
      have hupper : theta j ≤ 1 - mixedPilotInteriorMargin theta :=
        (le_abs_self (theta j)).trans habs
      simp only [pauliOutcomeSign, Bool.false_eq_true, if_false]
      linarith
  | true =>
      have hlower : -(1 - mixedPilotInteriorMargin theta) ≤ theta j :=
        (neg_le_neg habs).trans (neg_abs_le (theta j))
      simp only [pauliOutcomeSign, if_true, one_mul]
      linarith

/-- Unscaled one-observation directional score for Pauli coordinate \`j\`. -/
def mixedPilotOneShotDirectionalScore
    (theta h : RLSVector 3) (j : Fin 3) (outcome : Bool) : ℝ :=
  pauliOutcomeSign outcome * h j /
    (1 + pauliOutcomeSign outcome * theta j)

/-- One complete three-Pauli block score. -/
def mixedPilotBlockDirectionalScore
    (theta h : RLSVector 3) (block : PauliPilotBlock) : ℝ :=
  ∑ j : Fin 3, mixedPilotOneShotDirectionalScore theta h j (block j)

/-- Pilot directional score over all three axes and all \`q\` blocks. -/
def mixedPilotDirectionalScore
    {q : ℕ} (theta h : RLSVector 3) (path : PauliPilotPath q) : ℝ :=
  ∑ b : Fin q, mixedPilotBlockDirectionalScore theta h (path b)

/-- Uniform absolute envelope for one complete block. -/
def mixedPilotDirectionalEnvelope
    (theta h : RLSVector 3) : ℝ :=
  (∑ j : Fin 3, |h j|) / mixedPilotInteriorMargin theta

/-- The variance coefficient \`C(theta,h)\`. -/
def mixedPilotScoreVarianceConstant
    (theta h : RLSVector 3) : ℝ :=
  mixedPilotDirectionalEnvelope theta h ^ 2

theorem mixedPilotDirectionalEnvelope_nonneg
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    0 ≤ mixedPilotDirectionalEnvelope theta h := by
  unfold mixedPilotDirectionalEnvelope
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (le_of_lt (mixedPilotInteriorMargin_pos theta hInterior))

theorem mixedPilotScoreVarianceConstant_nonneg
    (theta h : RLSVector 3) :
    0 ≤ mixedPilotScoreVarianceConstant theta h :=
  sq_nonneg _

private theorem abs_pauliOutcomeSign (outcome : Bool) :
    |pauliOutcomeSign outcome| = 1 := by
  cases outcome <;> simp [pauliOutcomeSign]

/-- A single score contribution is bounded by its coordinate envelope. -/
theorem abs_mixedPilotOneShotDirectionalScore_le
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (j : Fin 3) (outcome : Bool) :
    |mixedPilotOneShotDirectionalScore theta h j outcome| ≤
      |h j| / mixedPilotInteriorMargin theta := by
  have hmargin := mixedPilotInteriorMargin_pos theta hInterior
  have hden := mixedPilot_scoreDenominator_ge_margin
    theta hInterior j outcome
  have hdenPos :
      0 < 1 + pauliOutcomeSign outcome * theta j :=
    hmargin.trans_le hden
  unfold mixedPilotOneShotDirectionalScore
  rw [abs_div, abs_mul, abs_pauliOutcomeSign, one_mul,
    abs_of_pos hdenPos]
  exact div_le_div_of_nonneg_left (abs_nonneg (h j)) hmargin hden

/-- A complete block score is bounded by
\`mixedPilotDirectionalEnvelope theta h\`. -/
theorem abs_mixedPilotBlockDirectionalScore_le
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (block : PauliPilotBlock) :
    |mixedPilotBlockDirectionalScore theta h block| ≤
      mixedPilotDirectionalEnvelope theta h := by
  calc
    |mixedPilotBlockDirectionalScore theta h block| ≤
        ∑ j : Fin 3,
          |mixedPilotOneShotDirectionalScore theta h j (block j)| := by
      unfold mixedPilotBlockDirectionalScore
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3,
          |h j| / mixedPilotInteriorMargin theta := by
      exact Finset.sum_le_sum fun j _ =>
        abs_mixedPilotOneShotDirectionalScore_le
          theta h hInterior j (block j)
    _ = mixedPilotDirectionalEnvelope theta h := by
      unfold mixedPilotDirectionalEnvelope
      rw [Finset.sum_div]

/-! ## Exact centering under the finite Born product mass -/

/-- A one-shot Pauli score has exact Born mean zero. -/
theorem mixedPilotOneShotDirectionalScore_bornMean_zero
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (j : Fin 3) :
    ∑ outcome : Bool,
      pauliBornProbability theta j outcome *
        mixedPilotOneShotDirectionalScore theta h j outcome = 0 := by
  have hplus :
      0 < 1 + theta j := by
    simpa [pauliOutcomeSign] using
      (mixedPilotInteriorMargin_pos theta hInterior).trans_le
        (mixedPilot_scoreDenominator_ge_margin theta hInterior j true)
  have hminus :
      0 < 1 - theta j := by
    simpa [pauliOutcomeSign] using
      (mixedPilotInteriorMargin_pos theta hInterior).trans_le
        (mixedPilot_scoreDenominator_ge_margin theta hInterior j false)
  have hplusNe : 1 + theta j ≠ 0 := ne_of_gt hplus
  have hminusNe : 1 - theta j ≠ 0 := ne_of_gt hminus
  simp [mixedPilotOneShotDirectionalScore, pauliBornProbability,
    pauliOutcomeSign, hplusNe, hminusNe]
  have hden : 1 + -theta j = 1 - theta j := by ring
  rw [hden]
  field_simp [hminusNe] <;> ring

private def mixedPilotMarkedAxisFactor
    (theta : RLSVector 3) (j k : Fin 3)
    (observable : Bool → ℝ) (outcome : Bool) : ℝ :=
  pauliBornProbability theta k outcome *
    (if k = j then observable outcome else 1)

private theorem mixedPilotMarkedAxisFactor_prod
    (theta : RLSVector 3) (j : Fin 3)
    (observable : Bool → ℝ) (block : PauliPilotBlock) :
    (∏ k : Fin 3,
      mixedPilotMarkedAxisFactor theta j k observable (block k)) =
      pauliPilotBlockMass theta block * observable (block j) := by
  unfold mixedPilotMarkedAxisFactor pauliPilotBlockMass
  rw [Finset.prod_mul_distrib]
  have hobservable :
      (∏ k : Fin 3, if k = j then observable (block k) else 1) =
        observable (block j) := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  rw [hobservable]

/-- Marginalization of an arbitrary one-coordinate observable inside one
three-Pauli block. -/
theorem mixedPilotBlock_singleCoordinate_mean
    (theta : RLSVector 3) (j : Fin 3)
    (observable : Bool → ℝ) :
    ∑ block : PauliPilotBlock,
      pauliPilotBlockMass theta block * observable (block j) =
      ∑ outcome : Bool,
        pauliBornProbability theta j outcome * observable outcome := by
  calc
    (∑ block : PauliPilotBlock,
      pauliPilotBlockMass theta block * observable (block j)) =
      ∑ block : PauliPilotBlock,
        ∏ k : Fin 3,
          mixedPilotMarkedAxisFactor theta j k observable (block k) := by
      apply Finset.sum_congr rfl
      intro block _
      exact (mixedPilotMarkedAxisFactor_prod
        theta j observable block).symm
    _ = ∏ k : Fin 3,
        ∑ outcome : Bool,
          mixedPilotMarkedAxisFactor theta j k observable outcome := by
      rw [← Fintype.prod_sum]
    _ = ∑ outcome : Bool,
        pauliBornProbability theta j outcome * observable outcome := by
      rw [Finset.prod_eq_single j]
      · simp [mixedPilotMarkedAxisFactor]
      · intro k _ hkj
        simpa [mixedPilotMarkedAxisFactor, hkj] using
          pauliBornProbability_sum_one theta k
      · simp

/-- One complete block has exact mass-weighted score mean zero. -/
theorem mixedPilotBlockDirectionalScore_massMean_zero
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    ∑ block : PauliPilotBlock,
      pauliPilotBlockMass theta block *
        mixedPilotBlockDirectionalScore theta h block = 0 := by
  unfold mixedPilotBlockDirectionalScore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc
    (∑ block : PauliPilotBlock,
      pauliPilotBlockMass theta block *
        mixedPilotOneShotDirectionalScore theta h j (block j)) =
      ∑ outcome : Bool,
        pauliBornProbability theta j outcome *
          mixedPilotOneShotDirectionalScore theta h j outcome :=
      mixedPilotBlock_singleCoordinate_mean theta j
        (mixedPilotOneShotDirectionalScore theta h j)
    _ = 0 :=
      mixedPilotOneShotDirectionalScore_bornMean_zero
        theta h hInterior j

/-- Every selected block score has exact integral zero under the full
\`q\`-block product measure. -/
theorem integral_mixedPilotBlockDirectionalScore_eq_zero
    {q : ℕ} (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) (b : Fin q) :
    (∫ path,
      mixedPilotBlockDirectionalScore theta h (path b)
      ∂pauliPilotBornProductMeasure theta) = 0 := by
  have hphysical := mixedPilotStrictInterior_physical theta hInterior
  calc
    (∫ path,
      mixedPilotBlockDirectionalScore theta h (path b)
      ∂pauliPilotBornProductMeasure theta) =
      ∑ path : PauliPilotPath q,
        pauliPilotPathMass theta path *
          mixedPilotBlockDirectionalScore theta h (path b) :=
      integral_pauliPilotBornProductMeasure theta hphysical _
    _ = ∑ block : PauliPilotBlock,
        pauliPilotBlockMass theta block *
          mixedPilotBlockDirectionalScore theta h block :=
      pauliPilotPath_singleBlock_mean theta b
        (mixedPilotBlockDirectionalScore theta h)
    _ = 0 :=
      mixedPilotBlockDirectionalScore_massMean_zero theta h hInterior

/-- The complete pilot directional score has exact mean zero. -/
theorem mixedPilotDirectionalScore_mean_zero
    {q : ℕ} (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    (∫ path : PauliPilotPath q, mixedPilotDirectionalScore theta h path
      ∂pauliPilotBornProductMeasure theta) = 0 := by
  letI : IsProbabilityMeasure
      (pauliPilotBornProductMeasure (q := q) theta) :=
    ⟨pauliPilotBornProductMeasure_univ (q := q) theta
      (mixedPilotStrictInterior_physical theta hInterior)⟩
  unfold mixedPilotDirectionalScore
  calc
    (∫ path,
      ∑ b : Fin q, mixedPilotBlockDirectionalScore theta h (path b)
      ∂pauliPilotBornProductMeasure theta) =
      ∑ b : Fin q,
        ∫ path, mixedPilotBlockDirectionalScore theta h (path b)
          ∂pauliPilotBornProductMeasure theta := by
      simpa using
        integral_finsetSum (μ := pauliPilotBornProductMeasure theta)
          Finset.univ (fun _ _ => Integrable.of_finite)
    _ = 0 := by
      simp [integral_mixedPilotBlockDirectionalScore_eq_zero
        theta h hInterior]

/-! ## Pairwise block independence and the O(q) variance bound -/

private theorem mixedPilot_fintype_prod_eq_two
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (f : ι → M) (a b : ι) (hab : a ≠ b)
    (hoff : ∀ i, i ≠ a → i ≠ b → f i = 1) :
    (∏ i : ι, f i) = f a * f b := by
  classical
  have hbmem : b ∈ (Finset.univ : Finset ι).erase a := by
    simp [hab.symm]
  calc
    (∏ i : ι, f i) =
        f a * ∏ i ∈ (Finset.univ : Finset ι).erase a, f i := by
      symm
      exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)
    _ = f a *
        (f b * ∏ i ∈ ((Finset.univ : Finset ι).erase a).erase b,
          f i) := by
      rw [Finset.mul_prod_erase
        ((Finset.univ : Finset ι).erase a) f hbmem]
    _ = f a * f b := by
      have hrest :
          (∏ i ∈ ((Finset.univ : Finset ι).erase a).erase b,
            f i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hib : i ≠ b := (Finset.mem_erase.mp hi).1
        have hia : i ≠ a :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        exact hoff i hia hib
      rw [hrest]
      simp

/-- Different complete Pauli blocks are pairwise independent under the
explicit finite Born product measure. -/
theorem mixedPilotBlockProjections_pairwiseIndep
    {q : ℕ} (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) :
    Set.Pairwise (Set.univ : Set (Fin q))
      (fun b c =>
        IndepFun
          (fun path : PauliPilotPath q => path b)
          (fun path : PauliPilotPath q => path c)
          (pauliPilotBornProductMeasure theta)) := by
  intro b _ c _ hbc
  apply indepFun_iff_measure_inter_preimage_eq_mul.2
  intro s t _hs _ht
  let events : Fin q → Set PauliPilotBlock := fun i =>
    if i = b then s else if i = c then t else univ
  have hrectangle :=
    pauliPilotBornProductMeasure_blockRectangle
      theta hphysical events
  have hset :
      (⋂ i, (fun path : PauliPilotPath q => path i) ⁻¹' events i) =
        (fun path : PauliPilotPath q => path b) ⁻¹' s ∩
          (fun path : PauliPilotPath q => path c) ⁻¹' t := by
    ext path
    constructor
    · intro hall
      have hb := Set.mem_iInter.mp hall b
      have hc := Set.mem_iInter.mp hall c
      constructor
      · simpa [events] using hb
      · simpa [events, hbc.symm] using hc
    · rintro ⟨hb, hc⟩
      apply Set.mem_iInter.mpr
      intro i
      by_cases hib : i = b
      · subst i
        simpa [events] using hb
      · by_cases hic : i = c
        · subst i
          simpa [events, hbc.symm] using hc
        · simp [events, hib, hic]
  have hprod :
      (∏ i : Fin q,
        ENNReal.ofReal (pauliPilotBlockEventMass theta (events i))) =
        ENNReal.ofReal (pauliPilotBlockEventMass theta s) *
          ENNReal.ofReal (pauliPilotBlockEventMass theta t) := by
    calc
      (∏ i : Fin q,
        ENNReal.ofReal (pauliPilotBlockEventMass theta (events i))) =
        ENNReal.ofReal (pauliPilotBlockEventMass theta (events b)) *
          ENNReal.ofReal (pauliPilotBlockEventMass theta (events c)) := by
        apply mixedPilot_fintype_prod_eq_two
        · exact hbc
        · intro i hib hic
          simp [events, hib, hic, pauliPilotBlockEventMass_univ]
      _ = ENNReal.ofReal (pauliPilotBlockEventMass theta s) *
          ENNReal.ofReal (pauliPilotBlockEventMass theta t) := by
        simp [events, hbc, hbc.symm]
  calc
    pauliPilotBornProductMeasure theta
        ((fun path : PauliPilotPath q => path b) ⁻¹' s ∩
          (fun path : PauliPilotPath q => path c) ⁻¹' t) =
      ∏ i : Fin q,
        ENNReal.ofReal (pauliPilotBlockEventMass theta (events i)) := by
      rw [← hset]
      exact hrectangle
    _ = ENNReal.ofReal (pauliPilotBlockEventMass theta s) *
          ENNReal.ofReal (pauliPilotBlockEventMass theta t) := hprod
    _ = pauliPilotBornProductMeasure theta
          ((fun path : PauliPilotPath q => path b) ⁻¹' s) *
        pauliPilotBornProductMeasure theta
          ((fun path : PauliPilotPath q => path c) ⁻¹' t) := by
      rw [pauliPilotBornProductMeasure_singleBlock
          theta hphysical b s,
        pauliPilotBornProductMeasure_singleBlock
          theta hphysical c t]

/-- Block scores inherit pairwise independence from the block projections. -/
theorem mixedPilotBlockScores_pairwiseIndep
    {q : ℕ} (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    Set.Pairwise (Set.univ : Set (Fin q))
      (fun b c =>
        IndepFun
          (fun path : PauliPilotPath q =>
            mixedPilotBlockDirectionalScore theta h (path b))
          (fun path : PauliPilotPath q =>
            mixedPilotBlockDirectionalScore theta h (path c))
          (pauliPilotBornProductMeasure theta)) := by
  intro b hb c hc hbc
  have hproj :=
    mixedPilotBlockProjections_pairwiseIndep
      (q := q) theta
      (mixedPilotStrictInterior_physical theta hInterior)
      hb hc hbc
  exact hproj.comp
    (measurable_of_finite (mixedPilotBlockDirectionalScore theta h))
    (measurable_of_finite (mixedPilotBlockDirectionalScore theta h))

/-- The variance of one selected block score is bounded by
\`C(theta,h)\`. -/
theorem mixedPilotBlockDirectionalScore_variance_le
    {q : ℕ} (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) (b : Fin q) :
    variance
      (fun path : PauliPilotPath q =>
        mixedPilotBlockDirectionalScore theta h (path b))
      (pauliPilotBornProductMeasure theta) ≤
      mixedPilotScoreVarianceConstant theta h := by
  let μ : Measure (PauliPilotPath q) :=
    pauliPilotBornProductMeasure theta
  letI : IsProbabilityMeasure μ :=
    ⟨by
      simpa [μ] using
        pauliPilotBornProductMeasure_univ theta
          (mixedPilotStrictInterior_physical theta hInterior)⟩
  have hinterval :
      ∀ᵐ path ∂μ,
        mixedPilotBlockDirectionalScore theta h (path b) ∈
          Set.Icc (-mixedPilotDirectionalEnvelope theta h)
            (mixedPilotDirectionalEnvelope theta h) := by
    exact Filter.Eventually.of_forall fun path =>
      (abs_le.mp
        (abs_mixedPilotBlockDirectionalScore_le
          theta h hInterior (path b)))
  have hvar :=
    variance_le_sq_of_bounded hinterval
      (measurable_of_finite
        (fun path : PauliPilotPath q =>
          mixedPilotBlockDirectionalScore theta h (path b))).aemeasurable
  change variance
      (fun path : PauliPilotPath q =>
        mixedPilotBlockDirectionalScore theta h (path b)) μ ≤
      mixedPilotScoreVarianceConstant theta h
  unfold mixedPilotScoreVarianceConstant
  convert hvar using 1 <;> ring

/-- Exact requested \`O(q)\` variance bound:
\`Var(score_q) <= q * C(theta,h)\`. -/
theorem mixedPilotDirectionalScore_variance_le
    {q : ℕ} (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    variance (mixedPilotDirectionalScore (q := q) theta h)
      (pauliPilotBornProductMeasure theta) ≤
      (q : ℝ) * mixedPilotScoreVarianceConstant theta h := by
  let μ : Measure (PauliPilotPath q) :=
    pauliPilotBornProductMeasure theta
  letI : IsProbabilityMeasure μ :=
    ⟨by
      simpa [μ] using
        pauliPilotBornProductMeasure_univ theta
          (mixedPilotStrictInterior_physical theta hInterior)⟩
  let X : Fin q → PauliPilotPath q → ℝ := fun b path =>
    mixedPilotBlockDirectionalScore theta h (path b)
  have hmem : ∀ b : Fin q, MemLp (X b) 2 μ := by
    intro b
    refine MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (mixedPilotDirectionalEnvelope theta h) ?_
    exact Filter.Eventually.of_forall fun path => by
      simpa [X, Real.norm_eq_abs] using
        abs_mixedPilotBlockDirectionalScore_le theta h hInterior (path b)
  have hindep :
      Set.Pairwise (↑(Finset.univ : Finset (Fin q)))
        (fun b c => IndepFun (X b) (X c) μ) := by
    simpa [X, μ] using
      mixedPilotBlockScores_pairwiseIndep
        (q := q) theta h hInterior
  have hvarianceSum :
      variance (mixedPilotDirectionalScore (q := q) theta h) μ =
        ∑ b : Fin q, variance (X b) μ := by
    have hfun :
        mixedPilotDirectionalScore (q := q) theta h =
          ∑ b : Fin q, X b := by
      funext path
      simp [mixedPilotDirectionalScore, X]
    rw [hfun]
    exact IndepFun.variance_sum
      (μ := μ) (X := X) (s := Finset.univ)
      (fun b _ => hmem b) hindep
  calc
    variance (mixedPilotDirectionalScore (q := q) theta h)
        (pauliPilotBornProductMeasure theta) =
      ∑ b : Fin q, variance (X b) μ := by
        simpa [μ] using hvarianceSum
    _ ≤ ∑ _b : Fin q, mixedPilotScoreVarianceConstant theta h := by
      apply Finset.sum_le_sum
      intro b _
      simpa [X, μ] using
        mixedPilotBlockDirectionalScore_variance_le
          (q := q) theta h hInterior b
    _ = (q : ℝ) * mixedPilotScoreVarianceConstant theta h := by
      simp

/-! ## Concrete polynomial row and score convergence -/

/-- Positive schedule parameter \`m=n+1\`. -/
def mixedPolynomialScheduleM (n : ℕ) : ℕ := Nat.succ n

/-- Number \`q(n)=m^5\` of complete three-Pauli pilot blocks. -/
def mixedPolynomialPilotBlocks (n : ℕ) : ℕ :=
  mixedPolynomialScheduleM n ^ 5

/-- LAN normalization \`N(n)=3*m^6\`. -/
def mixedPolynomialPilotLANScale (n : ℕ) : ℕ :=
  3 * mixedPolynomialScheduleM n ^ 6

theorem mixedPolynomialPilotBlocks_pos (n : ℕ) :
    0 < mixedPolynomialPilotBlocks n := by
  unfold mixedPolynomialPilotBlocks mixedPolynomialScheduleM
  positivity

theorem mixedPolynomialPilotLANScale_pos (n : ℕ) :
    0 < mixedPolynomialPilotLANScale n := by
  unfold mixedPolynomialPilotLANScale mixedPolynomialScheduleM
  positivity

/-- The exact pilot-to-LAN-scale ratio. -/
def mixedPolynomialPilotRatio (n : ℕ) : ℝ :=
  (mixedPolynomialPilotBlocks n : ℝ) /
    (mixedPolynomialPilotLANScale n : ℝ)

theorem mixedPolynomialPilotRatio_eq (n : ℕ) :
    mixedPolynomialPilotRatio n =
      1 / (3 * (mixedPolynomialScheduleM n : ℝ)) := by
  have hmne : (mixedPolynomialScheduleM n : ℝ) ≠ 0 := by
    have hmpos : 0 < mixedPolynomialScheduleM n := by
      unfold mixedPolynomialScheduleM
      positivity
    exact_mod_cast ne_of_gt hmpos
  unfold mixedPolynomialPilotRatio mixedPolynomialPilotBlocks
    mixedPolynomialPilotLANScale
  push_cast
  field_simp [hmne]

private theorem mixedPolynomialScheduleMReal_tendsto_atTop :
    Tendsto
      (fun n : ℕ => (mixedPolynomialScheduleM n : ℝ))
      atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) b] with n hn
  calc
    b ≤ (n : ℝ) := hn
    _ ≤ (mixedPolynomialScheduleM n : ℝ) := by
      simp [mixedPolynomialScheduleM]

private theorem mixedPolynomialScheduleMInv_tendsto_zero :
    Tendsto
      (fun n : ℕ => (mixedPolynomialScheduleM n : ℝ)⁻¹)
      atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    mixedPolynomialScheduleMReal_tendsto_atTop

theorem mixedPolynomialPilotRatio_tendsto_zero :
    Tendsto mixedPolynomialPilotRatio atTop (nhds 0) := by
  have hmul :
      Tendsto
        (fun n : ℕ =>
          (1 / 3 : ℝ) *
            (mixedPolynomialScheduleM n : ℝ)⁻¹)
        atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop
            (nhds (1 / 3 : ℝ))).mul
          mixedPolynomialScheduleMInv_tendsto_zero)
  have hfun :
      mixedPolynomialPilotRatio =
        fun n : ℕ =>
          (1 / 3 : ℝ) *
            (mixedPolynomialScheduleM n : ℝ)⁻¹ := by
    funext n
    rw [mixedPolynomialPilotRatio_eq]
    ring
  rw [hfun]
  exact hmul

/-- \`m^3 <= sqrt(N)\`, used to control all local ratios. -/
theorem mixedPolynomial_m_cube_le_sqrtLANScale (n : ℕ) :
    (mixedPolynomialScheduleM n : ℝ) ^ 3 ≤
      Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) := by
  have hm3nonneg :
      0 ≤ (mixedPolynomialScheduleM n : ℝ) ^ 3 := by positivity
  have hm6nonneg :
      0 ≤ (mixedPolynomialScheduleM n : ℝ) ^ 6 := by positivity
  have hsquare :
      ((mixedPolynomialScheduleM n : ℝ) ^ 3) ^ 2 ≤
        (mixedPolynomialPilotLANScale n : ℝ) := by
    calc
      ((mixedPolynomialScheduleM n : ℝ) ^ 3) ^ 2 =
          (mixedPolynomialScheduleM n : ℝ) ^ 6 := by ring
      _ ≤ 3 * (mixedPolynomialScheduleM n : ℝ) ^ 6 := by
        nlinarith
      _ = (mixedPolynomialPilotLANScale n : ℝ) := by
        unfold mixedPolynomialPilotLANScale
        push_cast
        rfl
  calc
    (mixedPolynomialScheduleM n : ℝ) ^ 3 =
        Real.sqrt (((mixedPolynomialScheduleM n : ℝ) ^ 3) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hm3nonneg]
    _ ≤ Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) :=
      Real.sqrt_le_sqrt hsquare

/-- The reciprocal LAN square-root scale tends to zero. -/
theorem mixedPolynomial_invSqrtLANScale_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹)
      atTop (nhds 0) := by
  have hupper :
      ∀ n : ℕ,
        (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹ ≤
          (mixedPolynomialScheduleM n : ℝ)⁻¹ ^ 3 := by
    intro n
    have hm3pos :
        0 < (mixedPolynomialScheduleM n : ℝ) ^ 3 := by
      apply pow_pos
      exact_mod_cast Nat.succ_pos n
    calc
      (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹ ≤
          ((mixedPolynomialScheduleM n : ℝ) ^ 3)⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le hm3pos
            (mixedPolynomial_m_cube_le_sqrtLANScale n)
      _ = (mixedPolynomialScheduleM n : ℝ)⁻¹ ^ 3 := by
        rw [inv_pow]
  have hpow :
      Tendsto
        (fun n : ℕ =>
          (mixedPolynomialScheduleM n : ℝ)⁻¹ ^ 3)
        atTop (nhds 0) := by
    simpa using mixedPolynomialScheduleMInv_tendsto_zero.pow 3
  exact Tendsto.squeeze tendsto_const_nhds hpow
    (fun _ => by positivity) hupper

/-- Directional score divided by \`sqrt(N(n))\`. -/
def mixedPolynomialPilotNormalizedScore
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) : ℝ :=
  mixedPilotDirectionalScore theta h path /
    Real.sqrt (mixedPolynomialPilotLANScale n : ℝ)

/-- Row-specific convergence in probability to zero.  The sample type and
finite Born measure are allowed to vary with \`n\`. -/
def MixedPilotRowConvergesInProbability
    (theta : RLSVector 3)
    (X : (n : ℕ) →
      PauliPilotPath (mixedPolynomialPilotBlocks n) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ =>
        pauliPilotBornProductMeasure theta
          {path | ε ≤ |X n path|})
      atTop (nhds 0)

/-- Explicit real Chebyshev envelope. -/
def mixedPolynomialPilotScoreTailRealEnvelope
    (theta h : RLSVector 3) (ε : ℝ) (n : ℕ) : ℝ :=
  mixedPilotScoreVarianceConstant theta h *
      mixedPolynomialPilotRatio n / ε ^ 2

/-- Explicit Chebyshev bound under the row-specific finite Born measure. -/
theorem mixedPolynomialPilotNormalizedScore_tail_bound
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    pauliPilotBornProductMeasure theta
        {path : PauliPilotPath (mixedPolynomialPilotBlocks n) |
          ε ≤ |mixedPolynomialPilotNormalizedScore theta h n path|} ≤
      ENNReal.ofReal
        (mixedPolynomialPilotScoreTailRealEnvelope theta h ε n) := by
  let q := mixedPolynomialPilotBlocks n
  let N := mixedPolynomialPilotLANScale n
  let μ : Measure (PauliPilotPath q) :=
    pauliPilotBornProductMeasure theta
  let X : PauliPilotPath q → ℝ :=
    mixedPilotDirectionalScore theta h
  have hphysical := mixedPilotStrictInterior_physical theta hInterior
  letI : IsProbabilityMeasure μ :=
    ⟨by
      simpa [μ] using
        pauliPilotBornProductMeasure_univ theta hphysical⟩
  have hN : 0 < N := by
    simpa [N] using mixedPolynomialPilotLANScale_pos n
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hA : 0 ≤ mixedPilotDirectionalEnvelope theta h :=
    mixedPilotDirectionalEnvelope_nonneg theta h hInterior
  have hmem : MemLp X 2 μ := by
    refine MemLp.of_bound (measurable_of_finite X).aestronglyMeasurable
      ((q : ℝ) * mixedPilotDirectionalEnvelope theta h) ?_
    exact Filter.Eventually.of_forall fun path => by
      rw [Real.norm_eq_abs]
      change
        |∑ b : Fin q, mixedPilotBlockDirectionalScore theta h (path b)| ≤
          (q : ℝ) * mixedPilotDirectionalEnvelope theta h
      calc
        |∑ b : Fin q, mixedPilotBlockDirectionalScore theta h (path b)| ≤
            ∑ b : Fin q,
              |mixedPilotBlockDirectionalScore theta h (path b)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin q, mixedPilotDirectionalEnvelope theta h := by
          exact Finset.sum_le_sum fun b _ =>
            abs_mixedPilotBlockDirectionalScore_le theta h hInterior (path b)
        _ = (q : ℝ) * mixedPilotDirectionalEnvelope theta h := by simp
  have hmean : μ[X] = 0 := by
    simpa [μ, X] using
      mixedPilotDirectionalScore_mean_zero
        (q := q) theta h hInterior
  have hevent :
      {path : PauliPilotPath q |
        ε ≤ |X path / Real.sqrt (N : ℝ)|} =
      {path : PauliPilotPath q |
        ε * Real.sqrt (N : ℝ) ≤ |X path - μ[X]|} := by
    ext path
    change
      ε ≤ |X path / Real.sqrt (N : ℝ)| ↔
        ε * Real.sqrt (N : ℝ) ≤ |X path - μ[X]|
    rw [hmean, sub_zero, abs_div, abs_of_pos hsqrt]
    exact (le_div_iff₀ hsqrt)
  have hchebyshev :=
    meas_ge_le_variance_div_sq hmem (mul_pos hε hsqrt)
  have hvariance :
      variance X μ ≤
        (q : ℝ) * mixedPilotScoreVarianceConstant theta h := by
    simpa [X, μ] using
      mixedPilotDirectionalScore_variance_le
        (q := q) theta h hInterior
  have hthresholdSquare :
      (ε * Real.sqrt (N : ℝ)) ^ 2 =
        ε ^ 2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ))]
  have hreal :
      variance X μ / (ε * Real.sqrt (N : ℝ)) ^ 2 ≤
        mixedPolynomialPilotScoreTailRealEnvelope theta h ε n := by
    rw [hthresholdSquare]
    calc
      variance X μ / (ε ^ 2 * (N : ℝ)) ≤
          ((q : ℝ) * mixedPilotScoreVarianceConstant theta h) /
            (ε ^ 2 * (N : ℝ)) :=
        div_le_div_of_nonneg_right hvariance (by positivity)
      _ = mixedPilotScoreVarianceConstant theta h *
          ((q : ℝ) / (N : ℝ)) / ε ^ 2 := by ring
      _ = mixedPolynomialPilotScoreTailRealEnvelope theta h ε n := by
        simp only [mixedPolynomialPilotScoreTailRealEnvelope,
          mixedPolynomialPilotRatio, q, N]
  change μ
      {path : PauliPilotPath q |
        ε ≤ |X path / Real.sqrt (N : ℝ)|} ≤
    ENNReal.ofReal
      (mixedPolynomialPilotScoreTailRealEnvelope theta h ε n)
  rw [hevent]
  exact hchebyshev.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The normalized pilot score converges to zero in the concrete row-specific
finite-measure sense. -/
theorem mixedPolynomialPilotNormalizedScore_convergesInProbability
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    MixedPilotRowConvergesInProbability theta
      (mixedPolynomialPilotNormalizedScore theta h) := by
  intro ε hε
  have hreal :
      Tendsto
        (fun n : ℕ =>
          mixedPolynomialPilotScoreTailRealEnvelope theta h ε n)
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun n : ℕ =>
            mixedPilotScoreVarianceConstant theta h *
              mixedPolynomialPilotRatio n)
          atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ => mixedPilotScoreVarianceConstant theta h)
            atTop (nhds (mixedPilotScoreVarianceConstant theta h))).mul
          mixedPolynomialPilotRatio_tendsto_zero)
    have hmulInv :
        Tendsto
          (fun n : ℕ =>
            (mixedPilotScoreVarianceConstant theta h *
              mixedPolynomialPilotRatio n) * (ε ^ 2)⁻¹)
          atTop (nhds 0) := by
      simpa using
        hmul.mul
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (ε ^ 2)⁻¹) atTop
              (nhds ((ε ^ 2)⁻¹)))
    simpa [mixedPolynomialPilotScoreTailRealEnvelope, div_eq_mul_inv] using
      hmulInv
  have hENN :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal
            (mixedPolynomialPilotScoreTailRealEnvelope theta h ε n))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact Tendsto.squeeze tendsto_const_nhds hENN
    (fun _ => bot_le)
    (fun n =>
      mixedPolynomialPilotNormalizedScore_tail_bound
        theta h hInterior ε hε n)

/-! ## Quadratic and cubic pilot likelihood terms -/

/-- One local pilot likelihood ratio increment. -/
def mixedPolynomialPilotLocalRatio
    (theta h : RLSVector 3) (n : ℕ) (j : Fin 3)
    (outcome : Bool) : ℝ :=
  mixedPilotOneShotDirectionalScore theta h j outcome /
    Real.sqrt (mixedPolynomialPilotLANScale n : ℝ)

/-- The normalized score is exactly the sum of local ratio increments. -/
theorem mixedPolynomialPilotNormalizedScore_eq_sumLocalRatios
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    mixedPolynomialPilotNormalizedScore theta h n path =
      ∑ b : Fin (mixedPolynomialPilotBlocks n),
        ∑ j : Fin 3,
          mixedPolynomialPilotLocalRatio theta h n j (path b j) := by
  unfold mixedPolynomialPilotNormalizedScore mixedPilotDirectionalScore
    mixedPilotBlockDirectionalScore mixedPolynomialPilotLocalRatio
  simp_rw [Finset.sum_div]

/-- Observed quadratic term from all pilot outcomes. -/
def mixedPolynomialPilotObservedQuadratic
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) : ℝ :=
  ∑ b : Fin (mixedPolynomialPilotBlocks n),
    ∑ j : Fin 3,
      mixedPolynomialPilotLocalRatio theta h n j (path b j) ^ 2

/-- Sum of scalar third-order Taylor remainders over the pilot. -/
def mixedPolynomialPilotTaylorRemainder
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) : ℝ :=
  ∑ b : Fin (mixedPolynomialPilotBlocks n),
    ∑ j : Fin 3,
      logThirdOrderRemainder
        (mixedPolynomialPilotLocalRatio theta h n j (path b j))

/-- Exact pilot Bernoulli log-likelihood contribution. -/
def mixedPolynomialPilotLogLikelihood
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) : ℝ :=
  ∑ b : Fin (mixedPolynomialPilotBlocks n),
    ∑ j : Fin 3,
      Real.log
        (1 + mixedPolynomialPilotLocalRatio theta h n j (path b j))

theorem mixedPolynomialPilotObservedQuadratic_nonneg
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    0 ≤ mixedPolynomialPilotObservedQuadratic theta h n path := by
  unfold mixedPolynomialPilotObservedQuadratic
  positivity

/-- Uniform local-ratio envelope. -/
theorem abs_mixedPolynomialPilotLocalRatio_le
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ) (j : Fin 3) (outcome : Bool) :
    |mixedPolynomialPilotLocalRatio theta h n j outcome| ≤
      mixedPilotDirectionalEnvelope theta h /
        Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) := by
  have hN := mixedPolynomialPilotLANScale_pos n
  have hsqrt :
      0 < Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hcoordinate :
      |h j| / mixedPilotInteriorMargin theta ≤
        mixedPilotDirectionalEnvelope theta h := by
    unfold mixedPilotDirectionalEnvelope
    have hterm :
        |h j| ≤ ∑ k : Fin 3, |h k| :=
      Finset.single_le_sum
        (fun k _ => abs_nonneg (h k)) (Finset.mem_univ j)
    exact div_le_div_of_nonneg_right hterm
      (le_of_lt (mixedPilotInteriorMargin_pos theta hInterior))
  unfold mixedPolynomialPilotLocalRatio
  rw [abs_div, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right
    ((abs_mixedPilotOneShotDirectionalScore_le
      theta h hInterior j outcome).trans hcoordinate)
    hsqrt.le

/-- Explicit \`O(q/N)\` quadratic envelope. -/
def mixedPolynomialPilotQuadraticEnvelope
    (theta h : RLSVector 3) (n : ℕ) : ℝ :=
  3 * mixedPilotDirectionalEnvelope theta h ^ 2 *
    mixedPolynomialPilotRatio n

/-- Explicit \`O(q/N^(3/2))\` cubic envelope. -/
def mixedPolynomialPilotRemainderEnvelope
    (theta h : RLSVector 3) (n : ℕ) : ℝ :=
  8 * mixedPilotDirectionalEnvelope theta h ^ 3 *
    mixedPolynomialPilotRatio n *
      (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹

theorem mixedPolynomialPilotQuadraticEnvelope_nonneg
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ) :
    0 ≤ mixedPolynomialPilotQuadraticEnvelope theta h n := by
  unfold mixedPolynomialPilotQuadraticEnvelope
    mixedPolynomialPilotRatio
  positivity

theorem mixedPolynomialPilotRemainderEnvelope_nonneg
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ) :
    0 ≤ mixedPolynomialPilotRemainderEnvelope theta h n := by
  have hA : 0 ≤ mixedPilotDirectionalEnvelope theta h :=
    mixedPilotDirectionalEnvelope_nonneg theta h hInterior
  have hratio : 0 ≤ mixedPolynomialPilotRatio n := by
    unfold mixedPolynomialPilotRatio
    positivity
  have hinv :
      0 ≤ (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹ :=
    inv_nonneg.2 (Real.sqrt_nonneg _)
  unfold mixedPolynomialPilotRemainderEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA 3)) hratio)
    hinv

/-- Pathwise quadratic bound by the explicit \`q/N\` envelope. -/
theorem mixedPolynomialPilotObservedQuadratic_le
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    mixedPolynomialPilotObservedQuadratic theta h n path ≤
      mixedPolynomialPilotQuadraticEnvelope theta h n := by
  let q := mixedPolynomialPilotBlocks n
  let N := mixedPolynomialPilotLANScale n
  let A := mixedPilotDirectionalEnvelope theta h
  have hN : 0 < N := by
    simpa [N] using mixedPolynomialPilotLANScale_pos n
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hlocalSquare :
      (A / Real.sqrt (N : ℝ)) ^ 2 = A ^ 2 / (N : ℝ) := by
    rw [div_pow, Real.sq_sqrt hNnonneg]
  calc
    mixedPolynomialPilotObservedQuadratic theta h n path ≤
        ∑ _b : Fin q, ∑ _j : Fin 3,
          (A / Real.sqrt (N : ℝ)) ^ 2 := by
      unfold mixedPolynomialPilotObservedQuadratic
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro j _
      calc
        mixedPolynomialPilotLocalRatio theta h n j (path b j) ^ 2 =
            |mixedPolynomialPilotLocalRatio theta h n j (path b j)| ^ 2 := by
          rw [sq_abs]
        _ ≤ (A / Real.sqrt (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _)
            (by
              simpa [A, N] using
                abs_mixedPolynomialPilotLocalRatio_le
                  theta h hInterior n j (path b j))
            2
    _ = (q : ℝ) * 3 * (A / Real.sqrt (N : ℝ)) ^ 2 := by
      simp
      ring
    _ = 3 * A ^ 2 * ((q : ℝ) / (N : ℝ)) := by
      rw [hlocalSquare]
      ring
    _ = mixedPolynomialPilotQuadraticEnvelope theta h n := by
      simp only [mixedPolynomialPilotQuadraticEnvelope,
        mixedPolynomialPilotRatio, q, N, A]

/-- The quadratic \`q/N\` envelope vanishes. -/
theorem mixedPolynomialPilotQuadraticEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto
      (mixedPolynomialPilotQuadraticEnvelope theta h)
      atTop (nhds 0) := by
  have hprod :=
    ((tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ =>
          3 * mixedPilotDirectionalEnvelope theta h ^ 2)
        atTop
        (nhds (3 * mixedPilotDirectionalEnvelope theta h ^ 2))).mul
      mixedPolynomialPilotRatio_tendsto_zero)
  have hprod0 :
      Tendsto
        (fun n : ℕ =>
          3 * mixedPilotDirectionalEnvelope theta h ^ 2 *
            mixedPolynomialPilotRatio n)
        atTop (nhds 0) := by
    simpa using hprod
  refine hprod0.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp only [mixedPolynomialPilotQuadraticEnvelope]

/-- The local Taylor condition holds eventually without any additional
premise. -/
theorem mixedPolynomialPilotTaylorCondition_eventually
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    ∀ᶠ n : ℕ in atTop,
      mixedPilotDirectionalEnvelope theta h /
          Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) ≤ 1 / 2 := by
  have hzero :
      Tendsto
        (fun n : ℕ =>
          mixedPilotDirectionalEnvelope theta h *
            (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹)
        atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ => mixedPilotDirectionalEnvelope theta h)
          atTop (nhds (mixedPilotDirectionalEnvelope theta h))).mul
        mixedPolynomial_invSqrtLANScale_tendsto_zero)
  filter_upwards [(tendsto_order.1 hzero).2 (1 / 2 : ℝ) (by norm_num)]
    with n hn
  simpa [div_eq_mul_inv] using le_of_lt hn

/-- Pathwise cubic Taylor bound by the explicit \`q/N^(3/2)\` envelope. -/
theorem abs_mixedPolynomialPilotTaylorRemainder_le
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ)
    (hsmall :
      mixedPilotDirectionalEnvelope theta h /
          Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) ≤ 1 / 2)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    |mixedPolynomialPilotTaylorRemainder theta h n path| ≤
      mixedPolynomialPilotRemainderEnvelope theta h n := by
  let q := mixedPolynomialPilotBlocks n
  let N := mixedPolynomialPilotLANScale n
  let A := mixedPilotDirectionalEnvelope theta h
  have hN : 0 < N := by
    simpa [N] using mixedPolynomialPilotLANScale_pos n
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hlocalCube :
      (A / Real.sqrt (N : ℝ)) ^ 3 =
        A ^ 3 / ((N : ℝ) * Real.sqrt (N : ℝ)) := by
    rw [div_pow]
    congr 1
    calc
      Real.sqrt (N : ℝ) ^ 3 =
          Real.sqrt (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) := by ring
      _ = (N : ℝ) * Real.sqrt (N : ℝ) := by
        rw [Real.sq_sqrt hNnonneg]
  calc
    |mixedPolynomialPilotTaylorRemainder theta h n path| ≤
        ∑ b : Fin q,
          |∑ j : Fin 3,
            logThirdOrderRemainder
              (mixedPolynomialPilotLocalRatio theta h n j (path b j))| := by
      unfold mixedPolynomialPilotTaylorRemainder
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin q, ∑ j : Fin 3,
          |logThirdOrderRemainder
            (mixedPolynomialPilotLocalRatio theta h n j (path _b j))| := by
      apply Finset.sum_le_sum
      intro b _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin q, ∑ _j : Fin 3,
          (8 / 3 : ℝ) * (A / Real.sqrt (N : ℝ)) ^ 3 := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro j _
      have hratio :=
        abs_mixedPolynomialPilotLocalRatio_le
          theta h hInterior n j (path b j)
      have hratioA :
          |mixedPolynomialPilotLocalRatio theta h n j (path b j)| ≤
            A / Real.sqrt (N : ℝ) := by
        simpa [A, N] using hratio
      calc
        |logThirdOrderRemainder
            (mixedPolynomialPilotLocalRatio theta h n j (path b j))| ≤
            (8 / 3 : ℝ) *
              |mixedPolynomialPilotLocalRatio theta h n j (path b j)| ^ 3 :=
          logThirdOrderRemainder_contract _
            (hratioA.trans (by simpa [A, N] using hsmall))
        _ ≤ (8 / 3 : ℝ) * (A / Real.sqrt (N : ℝ)) ^ 3 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) hratioA 3) (by norm_num)
    _ = 8 * (q : ℝ) * (A / Real.sqrt (N : ℝ)) ^ 3 := by
      simp
      ring
    _ = 8 * A ^ 3 * ((q : ℝ) / (N : ℝ)) *
          (Real.sqrt (N : ℝ))⁻¹ := by
      rw [hlocalCube]
      field_simp [show (N : ℝ) ≠ 0 by positivity,
        show Real.sqrt (N : ℝ) ≠ 0 by positivity]
    _ = mixedPolynomialPilotRemainderEnvelope theta h n := by
      simp only [mixedPolynomialPilotRemainderEnvelope,
        mixedPolynomialPilotRatio, q, N, A]

/-- The cubic \`q/N^(3/2)\` envelope vanishes. -/
theorem mixedPolynomialPilotRemainderEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto
      (mixedPolynomialPilotRemainderEnvelope theta h)
      atTop (nhds 0) := by
  have hfirst :
      Tendsto
        (fun n : ℕ =>
          (8 * mixedPilotDirectionalEnvelope theta h ^ 3) *
            mixedPolynomialPilotRatio n)
        atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ => 8 * mixedPilotDirectionalEnvelope theta h ^ 3)
          atTop
          (nhds (8 * mixedPilotDirectionalEnvelope theta h ^ 3))).mul
        mixedPolynomialPilotRatio_tendsto_zero)
  have hfull :=
    hfirst.mul mixedPolynomial_invSqrtLANScale_tendsto_zero
  have hfull0 :
      Tendsto
        (fun n : ℕ =>
          8 * mixedPilotDirectionalEnvelope theta h ^ 3 *
            mixedPolynomialPilotRatio n *
              (Real.sqrt (mixedPolynomialPilotLANScale n : ℝ))⁻¹)
        atTop (nhds 0) := by
    simpa using hfull
  refine hfull0.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp only [mixedPolynomialPilotRemainderEnvelope]

/-- Exact finite-path pilot likelihood decomposition. -/
theorem mixedPolynomialPilotLogLikelihood_exact_decomposition
    (theta h : RLSVector 3) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    mixedPolynomialPilotLogLikelihood theta h n path =
      mixedPolynomialPilotNormalizedScore theta h n path -
        mixedPolynomialPilotObservedQuadratic theta h n path / 2 +
          mixedPolynomialPilotTaylorRemainder theta h n path := by
  have hscalar (x : ℝ) :
      Real.log (1 + x) =
        x - x ^ 2 / 2 + logThirdOrderRemainder x := by
    unfold logThirdOrderRemainder
    ring
  unfold mixedPolynomialPilotLogLikelihood
  simp_rw [hscalar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [mixedPolynomialPilotNormalizedScore_eq_sumLocalRatios]
  unfold mixedPolynomialPilotObservedQuadratic
    mixedPolynomialPilotTaylorRemainder
  simp only [Finset.sum_div]

/-- Deterministic envelope for the non-score part of the pilot likelihood. -/
def mixedPolynomialPilotLikelihoodErrorEnvelope
    (theta h : RLSVector 3) (n : ℕ) : ℝ :=
  mixedPolynomialPilotQuadraticEnvelope theta h n / 2 +
    mixedPolynomialPilotRemainderEnvelope theta h n

theorem mixedPolynomialPilotLikelihoodErrorEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto
      (mixedPolynomialPilotLikelihoodErrorEnvelope theta h)
      atTop (nhds 0) := by
  have hquad :
      Tendsto
        (fun n : ℕ =>
          mixedPolynomialPilotQuadraticEnvelope theta h n / 2)
        atTop (nhds 0) := by
    have hmul :=
      (mixedPolynomialPilotQuadraticEnvelope_tendsto_zero theta h).mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)⁻¹) atTop (nhds (2 : ℝ)⁻¹))
    simpa [div_eq_mul_inv] using hmul
  change Tendsto
    (fun n : ℕ =>
      mixedPolynomialPilotQuadraticEnvelope theta h n / 2 +
        mixedPolynomialPilotRemainderEnvelope theta h n)
    atTop (nhds 0)
  simpa using hquad.add
    (mixedPolynomialPilotRemainderEnvelope_tendsto_zero theta h)

/-- Once the scalar Taylor condition holds, the non-score part is uniformly
bounded by the deterministic error envelope. -/
theorem abs_mixedPolynomialPilotLogLikelihood_sub_score_le
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ)
    (hsmall :
      mixedPilotDirectionalEnvelope theta h /
          Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) ≤ 1 / 2)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    |mixedPolynomialPilotLogLikelihood theta h n path -
        mixedPolynomialPilotNormalizedScore theta h n path| ≤
      mixedPolynomialPilotLikelihoodErrorEnvelope theta h n := by
  have hdecomp :=
    mixedPolynomialPilotLogLikelihood_exact_decomposition theta h n path
  have hquadNonneg :=
    mixedPolynomialPilotObservedQuadratic_nonneg theta h n path
  have hquadBound :=
    mixedPolynomialPilotObservedQuadratic_le
      theta h hInterior n path
  have hremBound :=
    abs_mixedPolynomialPilotTaylorRemainder_le
      theta h hInterior n hsmall path
  calc
    |mixedPolynomialPilotLogLikelihood theta h n path -
        mixedPolynomialPilotNormalizedScore theta h n path| =
      |-mixedPolynomialPilotObservedQuadratic theta h n path / 2 +
        mixedPolynomialPilotTaylorRemainder theta h n path| := by
      rw [hdecomp]
      congr 1
      ring
    _ ≤ |-mixedPolynomialPilotObservedQuadratic theta h n path / 2| +
        |mixedPolynomialPilotTaylorRemainder theta h n path| :=
      abs_add_le _ _
    _ = mixedPolynomialPilotObservedQuadratic theta h n path / 2 +
        |mixedPolynomialPilotTaylorRemainder theta h n path| := by
      rw [abs_div, abs_neg, abs_of_nonneg hquadNonneg]
      norm_num
    _ ≤ mixedPolynomialPilotQuadraticEnvelope theta h n / 2 +
        mixedPolynomialPilotRemainderEnvelope theta h n := by
      exact add_le_add
        (div_le_div_of_nonneg_right hquadBound (by norm_num))
        hremBound
    _ = mixedPolynomialPilotLikelihoodErrorEnvelope theta h n := rfl

/-- Final pilot-stage LAN result: the complete pilot log-likelihood
contribution is negligible in probability under the row-specific explicit
finite Born measures. -/
theorem mixedPolynomialPilotLogLikelihood_negligibleInProbability
    (theta h : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    MixedPilotRowConvergesInProbability theta
      (mixedPolynomialPilotLogLikelihood theta h) := by
  intro ε hε
  have hscore :
      Tendsto
        (fun n : ℕ =>
          pauliPilotBornProductMeasure theta
            {path : PauliPilotPath (mixedPolynomialPilotBlocks n) |
              ε / 2 ≤
                |mixedPolynomialPilotNormalizedScore theta h n path|})
        atTop (nhds 0) :=
    mixedPolynomialPilotNormalizedScore_convergesInProbability
      theta h hInterior (ε / 2) (by linarith)
  have hsmall :=
    mixedPolynomialPilotTaylorCondition_eventually
      theta h hInterior
  have herrorSmall :
      ∀ᶠ n : ℕ in atTop,
        mixedPolynomialPilotLikelihoodErrorEnvelope theta h n < ε / 2 :=
    (tendsto_order.1
      (mixedPolynomialPilotLikelihoodErrorEnvelope_tendsto_zero theta h)).2
      (ε / 2) (by linarith)
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        pauliPilotBornProductMeasure theta
            {path : PauliPilotPath (mixedPolynomialPilotBlocks n) |
              ε ≤ |mixedPolynomialPilotLogLikelihood theta h n path|} ≤
          pauliPilotBornProductMeasure theta
            {path : PauliPilotPath (mixedPolynomialPilotBlocks n) |
              ε / 2 ≤
                |mixedPolynomialPilotNormalizedScore theta h n path|} := by
    filter_upwards [hsmall, herrorSmall] with n hnSmall hnError
    apply measure_mono
    intro path hpath
    change ε ≤
      |mixedPolynomialPilotLogLikelihood theta h n path| at hpath
    change ε / 2 ≤
      |mixedPolynomialPilotNormalizedScore theta h n path|
    by_contra hnot
    have hscoreLt :
        |mixedPolynomialPilotNormalizedScore theta h n path| < ε / 2 :=
      lt_of_not_ge hnot
    have herrorBound :=
      abs_mixedPolynomialPilotLogLikelihood_sub_score_le
        theta h hInterior n hnSmall path
    have hlogBound :
        |mixedPolynomialPilotLogLikelihood theta h n path| ≤
          |mixedPolynomialPilotNormalizedScore theta h n path| +
            |mixedPolynomialPilotLogLikelihood theta h n path -
              mixedPolynomialPilotNormalizedScore theta h n path| := by
      calc
        |mixedPolynomialPilotLogLikelihood theta h n path| =
            |mixedPolynomialPilotNormalizedScore theta h n path +
              (mixedPolynomialPilotLogLikelihood theta h n path -
                mixedPolynomialPilotNormalizedScore theta h n path)| := by
              congr 1
              ring
        _ ≤ _ := abs_add_le _ _
    have hstrict :
        |mixedPolynomialPilotLogLikelihood theta h n path| < ε := by
      calc
        |mixedPolynomialPilotLogLikelihood theta h n path| ≤
            |mixedPolynomialPilotNormalizedScore theta h n path| +
              |mixedPolynomialPilotLogLikelihood theta h n path -
                mixedPolynomialPilotNormalizedScore theta h n path| :=
          hlogBound
        _ ≤ |mixedPolynomialPilotNormalizedScore theta h n path| +
              mixedPolynomialPilotLikelihoodErrorEnvelope theta h n :=
          add_le_add le_rfl herrorBound
        _ < ε := by linarith
    exact (not_lt_of_ge hpath) hstrict
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscore
    (Filter.Eventually.of_forall fun _ => bot_le)
    hupper

end

end QubitOracle.Paper
