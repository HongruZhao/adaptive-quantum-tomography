import QubitOracle.AdaptiveDesign.P1PositiveBatches
import QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments
import QubitOracle.AdaptiveDesign.AdaptiveExplorationRate

/-! The exact six-outcome Born experiment for a weighted orthonormal triad.
The weights are classical setting probabilities; each observed sign remains
attached to its chosen axis. This includes both P1 design rules. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

structure Action where
  frame : P1.UniformFrame
  weight : Fin 3 → ℝ
  nonneg : ∀ k, 0 ≤ weight k
  total : ∑ k, weight k = 1

instance : MeasurableSpace Action := ⊤
abbrev Path := AdaptiveInfinitePath LabeledBinaryOutcome
abbrev Policy := ℕ → AdaptiveTrajectory LabeledBinaryOutcome → Action
abbrev Vector := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def probability (θ : OneQubitPhysicalParameter) (a : Action)
    (z : LabeledBinaryOutcome) : ℝ :=
  a.weight z.1 * binaryBornProbability (generalAxisBornProjection θ (a.frame.axis z.1)) z.2

theorem probability_nonneg (θ : OneQubitPhysicalParameter) (a : Action) (z : LabeledBinaryOutcome) :
    0 ≤ probability θ a z :=
  mul_nonneg (a.nonneg z.1) (generalAxisBornProbability_nonnegative θ _ _)

theorem probability_sum (θ : OneQubitPhysicalParameter) (a : Action) :
    ∑ z, probability θ a z = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ k, a.weight k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sum_binaryOutcome]
      simp only [probability]
      rw [← mul_add, binaryBornProbability_plus_add_minus, mul_one]
    _ = 1 := a.total

def bornMeasure (θ : OneQubitPhysicalParameter) (a : Action) : Measure LabeledBinaryOutcome :=
  ∑ z, ENNReal.ofReal (probability θ a z) • Measure.dirac z

instance bornMeasure_probability (θ : OneQubitPhysicalParameter) (a : Action) :
    IsProbabilityMeasure (bornMeasure θ a) where
  measure_univ := by
    simp only [bornMeasure, Measure.finset_sum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => probability_nonneg θ a z),
      probability_sum, ENNReal.ofReal_one]

def kernel (θ : OneQubitPhysicalParameter) : Kernel Action LabeledBinaryOutcome where
  toFun := bornMeasure θ
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    intro t ht
    trivial

instance kernel_markov (θ : OneQubitPhysicalParameter) : IsMarkovKernel (kernel θ) :=
  ⟨fun a => bornMeasure_probability θ a⟩

theorem kernel_singleton (θ : OneQubitPhysicalParameter) (a : Action) (z : LabeledBinaryOutcome) :
    kernel θ a {z} = ENNReal.ofReal (probability θ a z) := by
  classical
  change bornMeasure θ a {z} = _
  rw [bornMeasure, Measure.finset_sum_apply, Finset.sum_eq_single z]
  · simp [Measure.smul_apply]
  · intro w _ hw
    simp [Measure.smul_apply, hw]
  · simp

theorem integral_eq_sum (θ : OneQubitPhysicalParameter) (a : Action)
    (f : LabeledBinaryOutcome → ℝ) :
    ∫ z, f z ∂kernel θ a = ∑ z, probability θ a z * f z := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul, Measure.real_def, kernel_singleton]
  simp_rw [ENNReal.toReal_ofReal (probability_nonneg θ a _)]

theorem integral_label (θ : OneQubitPhysicalParameter) (a : Action) (f : Fin 3 → ℝ) :
    ∫ z, f z.1 ∂kernel θ a = ∑ k, a.weight k * f k := by
  rw [integral_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_binaryOutcome]
  simp only [probability, binaryBornProbability, BinaryOutcome.sign]
  ring

def protocol (policy : Policy) :
    PredictableAdaptiveProtocol OneQubitPhysicalParameter Action LabeledBinaryOutcome where
  response := kernel
  response_isMarkov := kernel_markov
  design := policy
  design_measurable _ := measurable_of_countable _

def actualAction (policy : Policy) (n : ℕ) (path : Path) : Action :=
  policy n (adaptiveInfinitePathPrefix n path)

def axis (a : Action) (k : Fin 3) : Fin 3 → ℝ := (a.frame.axis k).1
def gram (a : Action) : Mat := ∑ k, a.weight k • blochOuter (axis a k)
def fisher (θ : Fin 3 → ℝ) (a : Action) : Mat :=
  ∑ k, a.weight k • mixedAxisFisher θ (axis a k)
def residual (θ : Fin 3 → ℝ) (a : Action) (z : LabeledBinaryOutcome) : Vector :=
  WithLp.toLp 2 (fun i => axis a z.1 i * (z.2.sign - blochDot θ (axis a z.1)))
def noiseCovariance (θ : Fin 3 → ℝ) (a : Action) : Mat :=
  ∑ k, (a.weight k * (1 - blochDot θ (axis a k)^2)) • blochOuter (axis a k)

theorem residual_coordinate_mean (θ : OneQubitPhysicalParameter) (a : Action) (i : Fin 3) :
    ∫ z, residual θ.1 a z i ∂kernel θ a = 0 := by
  rw [integral_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro k _
  rw [sum_binaryOutcome]
  simp only [probability, residual, PiLp.toLp_apply, binaryBornProbability,
    BinaryOutcome.sign, generalAxisBornProjection, axis, blochDot, Fin.sum_univ_succ]
  ring

theorem residual_mean (θ : OneQubitPhysicalParameter) (a : Action) :
    ∫ z, residual θ.1 a z ∂kernel θ a = 0 := by
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp (fun _ => Integrable.of_finite)]
  exact residual_coordinate_mean θ a i

theorem residual_second_moment (θ : OneQubitPhysicalParameter) (a : Action) (i j : Fin 3) :
    ∫ z, residual θ.1 a z i * residual θ.1 a z j ∂kernel θ a =
      noiseCovariance θ.1 a i j := by
  rw [integral_eq_sum, Fintype.sum_prod_type]
  simp only [noiseCovariance, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, blochOuter]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_binaryOutcome]
  simp only [probability, residual, PiLp.toLp_apply, binaryBornProbability,
    BinaryOutcome.sign, generalAxisBornProjection, axis, blochDot, Fin.sum_univ_succ]
  ring

theorem gram_coordinate_mean (θ : OneQubitPhysicalParameter) (a : Action) (i j : Fin 3) :
    ∫ z, axis a z.1 i * axis a z.1 j ∂kernel θ a = gram a i j := by
  rw [integral_label θ a (fun k => axis a k i * axis a k j)]
  simp [gram, blochOuter, Matrix.sum_apply, Matrix.smul_apply]

theorem gram_centered_mean (θ : OneQubitPhysicalParameter) (a : Action) (i j : Fin 3) :
    ∫ z, (axis a z.1 i * axis a z.1 j - gram a i j) ∂kernel θ a = 0 := by
  rw [integral_sub Integrable.of_finite (integrable_const _), gram_coordinate_mean]
  simp

end
end QubitOracle.AdaptiveDesign.P1Weighted
