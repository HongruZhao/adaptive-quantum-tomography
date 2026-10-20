import QubitOracle.Paper.OneQubitPureLinearEstimatorRisk
import Mathlib.Probability.CentralLimitTheorem

/-!
# Pure one-qubit cyclic tangent-Pauli score CLT

At a pure qubit truth, a radial Pauli measurement is nonregular.  The regular
cyclic design therefore uses the two tangent Pauli axes in a local chart.  One
block consists of one outcome from each tangent axis.  This file constructs an
infinite i.i.d. sequence of such blocks and proves its scalar score CLT from
Mathlib's kernel-proved i.i.d. central limit theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace QubitOracle.Paper

open OneQubitPureLinearEstimatorRisk

noncomputable section

/-- One complete pure-state tangent cycle: one shot on each tangent axis. -/
abbrev PureCyclicPauliBlock := PureLinearSampleSpace 1

/-- The exact fair Born law at the north-pole representative of a pure state. -/
noncomputable abbrev pureCyclicPauliBlockMeasure :
    Measure PureCyclicPauliBlock :=
  pureLinearSampleMeasure 1

/-- Common sample space carrying infinitely many independent complete cycles. -/
abbrev PureCyclicPauliOmega := ℕ -> PureCyclicPauliBlock

/-- Infinite product of the exact one-cycle Born law. -/
noncomputable abbrev pureCyclicPauliMeasure :
    Measure PureCyclicPauliOmega :=
  Measure.infinitePi (fun _ : ℕ => pureCyclicPauliBlockMeasure)

/-- Coordinate outcome in a complete two-axis cycle. -/
def pureCyclicPauliBlockCoordinate
    (axis : Fin 2) (block : PureCyclicPauliBlock) : ℝ :=
  pureLinearCoordinateEstimator 1 axis block

/-- Scalar score contributed by one complete two-axis cycle. -/
def pureCyclicPauliBlockScore
    (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) : ℝ :=
  Real.sqrt 2 *
    (h 0 * pureCyclicPauliBlockCoordinate 0 block +
      h 1 * pureCyclicPauliBlockCoordinate 1 block)

/-- Tangent Fisher quadratic form per complete two-shot cycle. -/
def pureCyclicPauliFisherQuadratic (h : Fin 2 -> ℝ) : ℝ :=
  2 * ∑ axis : Fin 2, h axis ^ 2

theorem pureCyclicPauliFisherQuadratic_nonnegative
    (h : Fin 2 -> ℝ) :
    0 <= pureCyclicPauliFisherQuadratic h := by
  unfold pureCyclicPauliFisherQuadratic
  positivity

/-- Every one-cycle coordinate is bounded by one. -/
theorem pureCyclicPauliBlockCoordinate_abs_le_one
    (axis : Fin 2) (block : PureCyclicPauliBlock) :
    |pureCyclicPauliBlockCoordinate axis block| <= 1 := by
  exact pureLinearCoordinateEstimator_abs_le_one (by norm_num) axis block

/-- Products of two one-cycle coordinates are integrable. -/
theorem pureCyclicPauliBlockCoordinate_mul_integrable
    (first second : Fin 2) :
    Integrable
      (fun block : PureCyclicPauliBlock =>
        pureCyclicPauliBlockCoordinate first block *
          pureCyclicPauliBlockCoordinate second block)
      pureCyclicPauliBlockMeasure := by
  have hLp : MemLp
      (fun block : PureCyclicPauliBlock =>
        pureCyclicPauliBlockCoordinate first block *
          pureCyclicPauliBlockCoordinate second block)
      1 pureCyclicPauliBlockMeasure := by
    refine MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1 ?_
    filter_upwards with block
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |pureCyclicPauliBlockCoordinate first block| *
          |pureCyclicPauliBlockCoordinate second block| <=
          1 * |pureCyclicPauliBlockCoordinate second block| :=
        mul_le_mul_of_nonneg_right
          (pureCyclicPauliBlockCoordinate_abs_le_one first block)
          (abs_nonneg _)
      _ <= 1 * 1 := mul_le_mul_of_nonneg_left
        (pureCyclicPauliBlockCoordinate_abs_le_one second block) zero_le_one
      _ = 1 := by ring
  exact hLp.integrable le_rfl

/-- Each one-cycle coordinate is integrable. -/
theorem pureCyclicPauliBlockCoordinate_integrable
    (axis : Fin 2) :
    Integrable (pureCyclicPauliBlockCoordinate axis)
      pureCyclicPauliBlockMeasure := by
  have hLp : MemLp (pureCyclicPauliBlockCoordinate axis) 1
      pureCyclicPauliBlockMeasure := by
    refine MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1 ?_
    filter_upwards with block
    simpa [Real.norm_eq_abs] using
      pureCyclicPauliBlockCoordinate_abs_le_one axis block
  exact hLp.integrable le_rfl

/-- A deterministic envelope for one block score. -/
def pureCyclicPauliBlockScoreEnvelope (h : Fin 2 -> ℝ) : ℝ :=
  Real.sqrt 2 * (|h 0| + |h 1|)

theorem pureCyclicPauliBlockScore_abs_le
    (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) :
    |pureCyclicPauliBlockScore h block| <=
      pureCyclicPauliBlockScoreEnvelope h := by
  rw [pureCyclicPauliBlockScore, pureCyclicPauliBlockScoreEnvelope,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
  calc
    |h 0 * pureCyclicPauliBlockCoordinate 0 block +
        h 1 * pureCyclicPauliBlockCoordinate 1 block| <=
        |h 0 * pureCyclicPauliBlockCoordinate 0 block| +
          |h 1 * pureCyclicPauliBlockCoordinate 1 block| := abs_add_le _ _
    _ = |h 0| * |pureCyclicPauliBlockCoordinate 0 block| +
          |h 1| * |pureCyclicPauliBlockCoordinate 1 block| := by
          rw [abs_mul, abs_mul]
    _ <= |h 0| * 1 + |h 1| * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (pureCyclicPauliBlockCoordinate_abs_le_one 0 block)
              (abs_nonneg _))
            (mul_le_mul_of_nonneg_left
              (pureCyclicPauliBlockCoordinate_abs_le_one 1 block)
              (abs_nonneg _))
    _ = |h 0| + |h 1| := by ring

theorem pureCyclicPauliBlockScore_memLp_two
    (h : Fin 2 -> ℝ) :
    MemLp (pureCyclicPauliBlockScore h) 2
      pureCyclicPauliBlockMeasure := by
  refine MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
    (pureCyclicPauliBlockScoreEnvelope h) ?_
  filter_upwards with block
  simpa [Real.norm_eq_abs] using pureCyclicPauliBlockScore_abs_le h block

theorem pureCyclicPauliBlockCoordinate_mean_zero
    (axis : Fin 2) :
    (∫ block, pureCyclicPauliBlockCoordinate axis block
      ∂pureCyclicPauliBlockMeasure) = 0 := by
  exact pureLinearCoordinateEstimator_mean_zero 1 axis

theorem pureCyclicPauliBlockCoordinate_secondMoment_one
    (axis : Fin 2) :
    (∫ block : PureCyclicPauliBlock,
      pureCyclicPauliBlockCoordinate axis block ^ 2
      ∂pureCyclicPauliBlockMeasure) = 1 := by
  simpa [pureCyclicPauliBlockCoordinate] using
    (pureLinearCoordinateEstimator_secondMoment (q := 1) (by norm_num) axis)

theorem pureCyclicPauliBlockCoordinate_crossMoment_zero :
    (∫ block : PureCyclicPauliBlock,
      pureCyclicPauliBlockCoordinate 0 block *
        pureCyclicPauliBlockCoordinate 1 block
      ∂pureCyclicPauliBlockMeasure) = 0 := by
  exact pureLinearCoordinateEstimator_crossMoment_zero
    (q := 1) (by norm_num) (by decide)

theorem pureCyclicPauliBlockScore_mean_zero
    (h : Fin 2 -> ℝ) :
    (∫ block, pureCyclicPauliBlockScore h block
      ∂pureCyclicPauliBlockMeasure) = 0 := by
  simp only [pureCyclicPauliBlockScore]
  rw [integral_const_mul]
  rw [integral_add
    ((pureCyclicPauliBlockCoordinate_integrable 0).const_mul (h 0))
    ((pureCyclicPauliBlockCoordinate_integrable 1).const_mul (h 1)),
    integral_const_mul, integral_const_mul,
    pureCyclicPauliBlockCoordinate_mean_zero,
    pureCyclicPauliBlockCoordinate_mean_zero]
  ring

theorem pureCyclicPauliBlockScore_secondMoment
    (h : Fin 2 -> ℝ) :
    (∫ block : PureCyclicPauliBlock,
        pureCyclicPauliBlockScore h block ^ 2
      ∂pureCyclicPauliBlockMeasure) =
      pureCyclicPauliFisherQuadratic h := by
  have h00 := pureCyclicPauliBlockCoordinate_secondMoment_one 0
  have h11 := pureCyclicPauliBlockCoordinate_secondMoment_one 1
  have h01 := pureCyclicPauliBlockCoordinate_crossMoment_zero
  have h10 :
      (∫ block : PureCyclicPauliBlock,
        pureCyclicPauliBlockCoordinate 1 block *
          pureCyclicPauliBlockCoordinate 0 block
        ∂pureCyclicPauliBlockMeasure) = 0 := by
    simpa [mul_comm] using h01
  have hsquare :
      (fun block : PureCyclicPauliBlock =>
        pureCyclicPauliBlockScore h block ^ 2) =
      (fun block : PureCyclicPauliBlock =>
        2 * (h 0 ^ 2 * pureCyclicPauliBlockCoordinate 0 block ^ 2 +
          h 1 ^ 2 * pureCyclicPauliBlockCoordinate 1 block ^ 2 +
          h 0 * h 1 *
            (pureCyclicPauliBlockCoordinate 0 block *
              pureCyclicPauliBlockCoordinate 1 block) +
          h 1 * h 0 *
            (pureCyclicPauliBlockCoordinate 1 block *
              pureCyclicPauliBlockCoordinate 0 block))) := by
    funext block
    rw [pureCyclicPauliBlockScore, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) <= 2)]
    ring
  rw [hsquare, integral_const_mul]
  have h00i : Integrable
      (fun block : PureCyclicPauliBlock =>
        h 0 ^ 2 * pureCyclicPauliBlockCoordinate 0 block ^ 2)
      pureCyclicPauliBlockMeasure := by
    simpa [pow_two] using
      (pureCyclicPauliBlockCoordinate_mul_integrable 0 0).const_mul (h 0 ^ 2)
  have h11i : Integrable
      (fun block : PureCyclicPauliBlock =>
        h 1 ^ 2 * pureCyclicPauliBlockCoordinate 1 block ^ 2)
      pureCyclicPauliBlockMeasure := by
    simpa [pow_two] using
      (pureCyclicPauliBlockCoordinate_mul_integrable 1 1).const_mul (h 1 ^ 2)
  have h01i : Integrable
      (fun block : PureCyclicPauliBlock =>
        h 0 * h 1 *
          (pureCyclicPauliBlockCoordinate 0 block *
            pureCyclicPauliBlockCoordinate 1 block))
      pureCyclicPauliBlockMeasure :=
    (pureCyclicPauliBlockCoordinate_mul_integrable 0 1).const_mul (h 0 * h 1)
  have h10i : Integrable
      (fun block : PureCyclicPauliBlock =>
        h 1 * h 0 *
          (pureCyclicPauliBlockCoordinate 1 block *
            pureCyclicPauliBlockCoordinate 0 block))
      pureCyclicPauliBlockMeasure :=
    (pureCyclicPauliBlockCoordinate_mul_integrable 1 0).const_mul (h 1 * h 0)
  change 2 * (∫ block : PureCyclicPauliBlock,
      ((fun b => h 0 ^ 2 * pureCyclicPauliBlockCoordinate 0 b ^ 2) +
        (fun b => h 1 ^ 2 * pureCyclicPauliBlockCoordinate 1 b ^ 2) +
        (fun b => h 0 * h 1 *
          (pureCyclicPauliBlockCoordinate 0 b *
            pureCyclicPauliBlockCoordinate 1 b)) +
        (fun b => h 1 * h 0 *
          (pureCyclicPauliBlockCoordinate 1 b *
            pureCyclicPauliBlockCoordinate 0 b))) block
      ∂pureCyclicPauliBlockMeasure) = pureCyclicPauliFisherQuadratic h
  have hsplit4 := integral_add (h00i.add h11i |>.add h01i) h10i
  have hsplit3 := integral_add (h00i.add h11i) h01i
  have hsplit2 := integral_add h00i h11i
  simp only [Pi.add_apply] at hsplit4 hsplit3 hsplit2 ⊢
  rw [hsplit4, hsplit3, hsplit2]
  simp only [integral_const_mul]
  rw [h00, h11, h01, h10]
  simp [pureCyclicPauliFisherQuadratic, Fin.sum_univ_two]

theorem pureCyclicPauliBlockScore_variance
    (h : Fin 2 -> ℝ) :
    Var[pureCyclicPauliBlockScore h; pureCyclicPauliBlockMeasure] =
      pureCyclicPauliFisherQuadratic h := by
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable,
    pureCyclicPauliBlockScore_mean_zero]
  simpa using pureCyclicPauliBlockScore_secondMoment h

/-- The score of block `k` on the common infinite product space. -/
def pureCyclicPauliScoreIncrement
    (h : Fin 2 -> ℝ) (k : ℕ) (omega : PureCyclicPauliOmega) : ℝ :=
  pureCyclicPauliBlockScore h (omega k)

theorem pureCyclicPauliScoreIncrement_iIndepFun
    (h : Fin 2 -> ℝ) :
    iIndepFun (pureCyclicPauliScoreIncrement h)
      pureCyclicPauliMeasure := by
  exact iIndepFun_infinitePi
    (X := fun _ : ℕ => pureCyclicPauliBlockScore h)
    (fun _ => measurable_of_finite _)

theorem pureCyclicPauliScoreIncrement_hasLaw
    (h : Fin 2 -> ℝ) (k : ℕ) :
    HasLaw (pureCyclicPauliScoreIncrement h k)
      (pureCyclicPauliBlockMeasure.map (pureCyclicPauliBlockScore h))
      pureCyclicPauliMeasure := by
  refine HasLaw.mk
    (((measurable_of_finite _).comp (measurable_pi_apply k)).aemeasurable) ?_
  change Measure.map
      ((pureCyclicPauliBlockScore h) ∘ fun omega : PureCyclicPauliOmega => omega k)
      pureCyclicPauliMeasure = _
  rw [← Measure.map_map]
  · change Measure.map (pureCyclicPauliBlockScore h)
      (Measure.map (fun omega : PureCyclicPauliOmega => omega k)
        (Measure.infinitePi (fun _ : ℕ => pureCyclicPauliBlockMeasure))) = _
    rw [Measure.infinitePi_map_eval]
  · fun_prop
  · fun_prop

theorem pureCyclicPauliScoreIncrement_identDistrib
    (h : Fin 2 -> ℝ) (k : ℕ) :
    IdentDistrib (pureCyclicPauliScoreIncrement h k)
      (pureCyclicPauliScoreIncrement h 0)
      pureCyclicPauliMeasure pureCyclicPauliMeasure :=
  (pureCyclicPauliScoreIncrement_hasLaw h k).identDistrib
    (pureCyclicPauliScoreIncrement_hasLaw h 0)

theorem pureCyclicPauliScoreIncrement_memLp_two
    (h : Fin 2 -> ℝ) :
    MemLp (pureCyclicPauliScoreIncrement h 0) 2
      pureCyclicPauliMeasure := by
  change MemLp (fun omega : PureCyclicPauliOmega =>
      pureCyclicPauliBlockScore h (omega 0)) 2
    (Measure.infinitePi (fun _ : ℕ => pureCyclicPauliBlockMeasure))
  simpa [Function.comp_def] using
    (pureCyclicPauliBlockScore_memLp_two h).comp_measurePreserving
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ => pureCyclicPauliBlockMeasure) 0)

theorem pureCyclicPauliScoreIncrement_mean_zero
    (h : Fin 2 -> ℝ) :
    (∫ omega, pureCyclicPauliScoreIncrement h 0 omega
      ∂pureCyclicPauliMeasure) = 0 := by
  have hSelf : HasLaw (pureCyclicPauliBlockScore h)
      (pureCyclicPauliBlockMeasure.map (pureCyclicPauliBlockScore h))
      pureCyclicPauliBlockMeasure :=
    HasLaw.mk (measurable_of_finite _).aemeasurable rfl
  have hIdent :=
    (pureCyclicPauliScoreIncrement_hasLaw h 0).identDistrib hSelf
  rw [hIdent.integral_eq]
  exact pureCyclicPauliBlockScore_mean_zero h

theorem pureCyclicPauliScoreIncrement_variance
    (h : Fin 2 -> ℝ) :
    Var[pureCyclicPauliScoreIncrement h 0; pureCyclicPauliMeasure] =
      pureCyclicPauliFisherQuadratic h := by
  have hSelf : HasLaw (pureCyclicPauliBlockScore h)
      (pureCyclicPauliBlockMeasure.map (pureCyclicPauliBlockScore h))
      pureCyclicPauliBlockMeasure :=
    HasLaw.mk (measurable_of_finite _).aemeasurable rfl
  have hIdent :=
    (pureCyclicPauliScoreIncrement_hasLaw h 0).identDistrib hSelf
  rw [hIdent.variance_eq]
  exact pureCyclicPauliBlockScore_variance h

/-- Normalized score accumulated over the first `q` complete cycles. -/
def pureCyclicPauliNormalizedScore
    (h : Fin 2 -> ℝ) (q : ℕ) (omega : PureCyclicPauliOmega) : ℝ :=
  (Real.sqrt q)⁻¹ *
    ∑ k ∈ Finset.range q, pureCyclicPauliScoreIncrement h k omega

/-- Kernel-proved scalar score CLT for the pure two-tangent-axis cycle. -/
theorem pureCyclicPauliNormalizedScore_CLT
    (h : Fin 2 -> ℝ) :
    TendstoInDistribution
      (pureCyclicPauliNormalizedScore h) atTop id
      (fun _ => pureCyclicPauliMeasure)
      (gaussianReal 0 (pureCyclicPauliFisherQuadratic h).toNNReal) := by
  change TendstoInDistribution
    (fun (q : ℕ) (omega : PureCyclicPauliOmega) => (Real.sqrt q)⁻¹ *
      ∑ k ∈ Finset.range q, pureCyclicPauliScoreIncrement h k omega)
    atTop id (fun _ => pureCyclicPauliMeasure)
    (gaussianReal 0 (pureCyclicPauliFisherQuadratic h).toNNReal)
  let gaussian := gaussianReal 0
    (Var[pureCyclicPauliScoreIncrement h 0;
      pureCyclicPauliMeasure]).toNNReal
  have hGaussian : HasLaw id gaussian gaussian := by
    exact HasLaw.mk measurable_id.aemeasurable Measure.map_id
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := pureCyclicPauliMeasure) (P' := gaussian)
    (X := pureCyclicPauliScoreIncrement h) (Y := id)
    hGaussian (pureCyclicPauliScoreIncrement_memLp_two h)
    (pureCyclicPauliScoreIncrement_iIndepFun h)
    (pureCyclicPauliScoreIncrement_identDistrib h)
  simpa [pureCyclicPauliScoreIncrement_mean_zero,
    pureCyclicPauliScoreIncrement_variance, gaussian] using hCLT

end

end QubitOracle.Paper
