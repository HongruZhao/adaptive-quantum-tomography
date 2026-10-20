import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.BoundedMartingaleAzumaStrongLaw
import QubitOracle.Paper.ConcreteProtocolA1A3
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveBornProtocol
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveScoreCondExp
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
/-!
# P1: a uniform orthonormal frame is persistently exciting

This file deliberately allows every frame to depend on the entire observed
past.  The exact labeled Born law implies a constant conditional Gram matrix
`I / 3`, independent of that frame and of the unknown state.  Thus the Bures
protocol needs no added exploration and no external RLS theorem.
-/
namespace QubitOracle.AdaptiveDesign.P1

open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
noncomputable section

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

/-- Physical orthonormal frame, specified by its resolution of the identity. -/
structure UniformFrame extends QubitThreeAxisFrame where
  unit_axes : ∀ k, QubitOracle.blochNormSq (axis k).1 = 1
  resolution : ∀ i j : Fin 3,
    (∑ k : Fin 3, (axis k).1 i * (axis k).1 j) = if i = j then 1 else 0

abbrev FramePolicy := Nat → AdaptiveTrajectory LabeledBinaryOutcome → UniformFrame
abbrev Path := AdaptiveInfinitePath LabeledBinaryOutcome
abbrev Prefix (k : Nat) :=
  (i : ↥(Finset.Iic k)) → AdaptiveOutcomeProcess LabeledBinaryOutcome i.1

/-- Every observation records the uniformly chosen axis label and Born outcome. -/
def protocol (policy : FramePolicy) :
    PredictableAdaptiveProtocol OneQubitPhysicalParameter
      QubitLabeledMeasurementAction LabeledBinaryOutcome where
  response := qubitLabeledBornResponseKernel
  response_isMarkov := qubitLabeledBornResponseKernel_isMarkov
  design n history := .frame (policy n history).toQubitThreeAxisFrame
  design_measurable n := measurable_of_countable _

def pathMeasure (policy : FramePolicy) (theta : OneQubitPhysicalParameter) : Measure Path :=
  adaptiveInfiniteTrajectoryMeasure (protocol policy) theta

instance (policy : FramePolicy) (theta : OneQubitPhysicalParameter) :
    IsProbabilityMeasure (pathMeasure policy theta) := by
  unfold pathMeasure
  infer_instance

def actualFrame (policy : FramePolicy) (n : Nat) (path : Path) : UniformFrame :=
  policy n (adaptiveInfinitePathPrefix n path)

def actualAxis (policy : FramePolicy) (n : Nat) (path : Path) : Fin 3 → Real :=
  ((actualFrame policy n path).axis (path n).1).1

def rewardValue (policy : FramePolicy)
    (reward : UniformFrame → LabeledBinaryOutcome → Real) (n : Nat) (path : Path) : Real :=
  reward (actualFrame policy n path) (path n)

private def prefixReward (policy : FramePolicy)
    (reward : UniformFrame → LabeledBinaryOutcome → Real) (k : Nat)
    (pref : Prefix (k+1)) : Real :=
  reward (policy (k+1) (iicToAdaptiveTrajectory
    (fun i : Finset.Iic k => pref ⟨i.1, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ k))⟩)))
    (pref ⟨k+1, Finset.mem_Iic.mpr le_rfl⟩)

theorem rewardValue_stronglyMeasurable_succ (policy : FramePolicy)
    (reward : UniformFrame → LabeledBinaryOutcome → Real) (k : Nat) :
    StronglyMeasurable[Filtration.piLE (k+1)] (rewardValue policy reward (k+1)) := by
  have heq : rewardValue policy reward (k+1) =
      prefixReward policy reward k ∘ Preorder.frestrictLe (k+1) := by
    funext path
    rfl
  rw [heq, Filtration.piLE_eq_comap_frestrictLe]
  have hg : Measurable (prefixReward policy reward k) := measurable_of_countable _
  exact (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- A finite-kernel mean-zero calculation transfers to the literal adaptive law. -/
theorem rewardValue_condExp_zero (policy : FramePolicy)
    (theta : OneQubitPhysicalParameter)
    (reward : UniformFrame → LabeledBinaryOutcome → Real)
    (C : Real) (hbound : ∀ f z, ‖reward f z‖ ≤ C)
    (hmean : ∀ f, ∫ z, reward f z
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame) = 0)
    (k : Nat) :
    (pathMeasure policy theta)[rewardValue policy reward (k+1) | Filtration.piLE k]
      =ᵐ[pathMeasure policy theta] 0 := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let mu := pathMeasure policy theta
  let X : Path → Prefix k := Preorder.frestrictLe k
  let Ynext : Path → LabeledBinaryOutcome := fun path => path (k+1)
  let f := fun z : Prefix k × LabeledBinaryOutcome =>
    reward (policy (k+1) (iicToAdaptiveTrajectory z.1)) z.2
  have hX : Measurable X := Preorder.measurable_frestrictLe k
  have hY : Measurable Ynext := measurable_pi_apply (k+1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun path => f (X path, Ynext path)) mu := by
    refine Integrable.of_bound
      (hf.comp_measurable (hX.prodMk hY)).aestronglyMeasurable C ?_
    exact ae_of_all _ fun path => hbound _ _
  have hcond := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    hX hY.aemeasurable hf hfInt
  have hkernel : ProbabilityTheory.condDistrib Ynext X mu =ᵐ[mu.map X]
      adaptiveIonescuStepKernel (protocol policy) theta k := by
    simpa [mu, X, Ynext, pathMeasure] using
      adaptiveInfiniteTrajectory_conditionalStep (protocol policy) theta k
  have hkernelPath := (MeasureTheory.ae_map_iff hX.aemeasurable
    (Set.Finite.measurableSet (Set.toFinite {pref |
      (ProbabilityTheory.condDistrib Ynext X mu) pref =
        adaptiveIonescuStepKernel (protocol policy) theta k pref}))).mp hkernel
  have hzero : (fun path => ∫ z, f (X path, z)
      ∂(ProbabilityTheory.condDistrib Ynext X mu) (X path)) =ᵐ[mu] 0 := by
    filter_upwards [hkernelPath] with path hp
    rw [hp]
    exact hmean _
  exact hcond.trans hzero

private def shiftedReward (policy : FramePolicy)
    (reward : UniformFrame → LabeledBinaryOutcome → Real) : Nat → Path → Real
  | 0 => fun _ => 0
  | n+1 => rewardValue policy reward (n+1)

/-- Source-free strong law for any bounded, centered frame reward. The average
includes every actual observation from time zero through time `N`. -/
theorem centeredReward_average_ae (policy : FramePolicy)
    (theta : OneQubitPhysicalParameter)
    (reward : UniformFrame → LabeledBinaryOutcome → Real)
    (C : Real) (hC : 0 ≤ C) (hbound : ∀ f z, ‖reward f z‖ ≤ C)
    (hmean : ∀ f, ∫ z, reward f z
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame) = 0) :
    ∀ᵐ path ∂pathMeasure policy theta,
      Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range (N+1), rewardValue policy reward k path)
        atTop (nhds 0) := by
  have hadapt : StronglyAdapted Filtration.piLE (shiftedReward policy reward) := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ k => exact rewardValue_stronglyMeasurable_succ policy reward k
  have hs := boundedMartingaleDifference_average_ae_tendsto_zero
    (pathMeasure policy theta) Filtration.piLE (shiftedReward policy reward)
    hadapt rfl
    (fun k => rewardValue_condExp_zero policy theta reward C hbound hmean k)
    C hC (by
      intro n path
      cases n with
      | zero => simpa [shiftedReward] using hC
      | succ k => exact hbound _ _)
  filter_upwards [hs] with path hp
  have hsum (N : Nat) :
      (∑ k ∈ Finset.range (N+1), rewardValue policy reward k path) =
        (∑ k ∈ Finset.range (N+1), shiftedReward policy reward k path) +
          rewardValue policy reward 0 path := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [shiftedReward]
    ring
  have hinit : Tendsto (fun N : Nat => (N : Real)⁻¹ *
      rewardValue policy reward 0 path) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (rewardValue policy reward 0 path)
  convert hp.add hinit using 1
  · ext N
    rw [hsum, mul_add]
  · simp

/-- Each physical axis coordinate has absolute value at most one. -/
theorem axis_coordinate_bound (f : UniformFrame) (k i : Fin 3) :
    |(f.axis k).1 i| ≤ 1 := by
  have hs : (f.axis k).1 i ^ 2 ≤ 1 :=
    (Finset.single_le_sum (fun j _ => sq_nonneg ((f.axis k).1 j))
      (Finset.mem_univ i)).trans (f.axis k).2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((f.axis k).1 i + 1),
    sq_nonneg ((f.axis k).1 i - 1)]

def gramReward (i j : Fin 3) (f : UniformFrame) (z : LabeledBinaryOutcome) : Real :=
  (f.axis z.1).1 i * (f.axis z.1).1 j - (if i = j then 1 else 0) / 3

def responseReward (theta : OneQubitPhysicalParameter)
    (i : Fin 3) (f : UniformFrame) (z : LabeledBinaryOutcome) : Real :=
  (f.axis z.1).1 i * z.2.sign - theta.1 i / 3

private theorem integral_reward_eq_sum (theta : OneQubitPhysicalParameter)
    (f : UniformFrame) (r : LabeledBinaryOutcome → Real) :
    (∫ z, r z ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame)) =
      ∑ z : LabeledBinaryOutcome,
        qubitLabeledBornProbability theta (.frame f.toQubitThreeAxisFrame) z * r z := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul, Measure.real_def,
    qubitLabeledBornResponseKernel_singleton]
  simp_rw [ENNReal.toReal_ofReal
    (qubitLabeledBornProbability_nonnegative theta (.frame f.toQubitThreeAxisFrame) _)]

theorem gramReward_mean (theta : OneQubitPhysicalParameter)
    (i j : Fin 3) (f : UniformFrame) :
    (∫ z, gramReward i j f z
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame)) = 0 := by
  rw [integral_reward_eq_sum, Fintype.sum_prod_type]
  have hterm (k : Fin 3) :
      (∑ y : BinaryOutcome,
        qubitLabeledBornProbability theta (.frame f.toQubitThreeAxisFrame) (k,y) *
          gramReward i j f (k,y)) =
      ((f.axis k).1 i * (f.axis k).1 j - (if i = j then 1 else 0) / 3) / 3 := by
    rw [sum_binaryOutcome]
    simp [qubitLabeledBornProbability, qubitLabeledActionWeight,
      qubitLabeledActionAxis, gramReward, binaryBornProbability, BinaryOutcome.sign]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, f.resolution]
  simp
  ring

theorem gramReward_bound (i j : Fin 3) (f : UniformFrame)
    (z : LabeledBinaryOutcome) : ‖gramReward i j f z‖ ≤ 2 := by
  have hab : |(f.axis z.1).1 i * (f.axis z.1).1 j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (axis_coordinate_bound f z.1 i)
      (axis_coordinate_bound f z.1 j) (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hc : |(if i = j then (1 : Real) else 0) / 3| ≤ 1 := by
    split_ifs <;> norm_num
  exact (abs_sub _ _).trans (by
    have h := add_le_add hab hc
    norm_num at h ⊢
    exact h)

theorem responseReward_mean (theta : OneQubitPhysicalParameter)
    (i : Fin 3) (f : UniformFrame) :
    (∫ z, responseReward theta i f z
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame)) = 0 := by
  rw [integral_reward_eq_sum, Fintype.sum_prod_type]
  have hterm (k : Fin 3) :
      (∑ y : BinaryOutcome,
        qubitLabeledBornProbability theta (.frame f.toQubitThreeAxisFrame) (k,y) *
          responseReward theta i f (k,y)) =
      ((f.axis k).1 i * generalAxisBornProjection theta (f.axis k) - theta.1 i / 3) / 3 := by
    rw [sum_binaryOutcome]
    simp [qubitLabeledBornProbability, qubitLabeledActionWeight,
      qubitLabeledActionAxis, responseReward, binaryBornProbability, BinaryOutcome.sign]
    ring
  have hsum : (∑ k : Fin 3,
      (f.axis k).1 i * generalAxisBornProjection theta (f.axis k)) = theta.1 i := by
    simp only [generalAxisBornProjection, QubitOracle.blochDot, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, f.resolution]
    simp
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hsum]
  simp
  ring

theorem responseReward_bound (theta : OneQubitPhysicalParameter)
    (i : Fin 3) (f : UniformFrame) (z : LabeledBinaryOutcome) :
    ‖responseReward theta i f z‖ ≤ 2 := by
  have ht : |theta.1 i| ≤ 1 := by
    have hs : theta.1 i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (theta.1 j))
        (Finset.mem_univ i)).trans theta.2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (theta.1 i + 1), sq_nonneg (theta.1 i - 1)]
  have hy : |z.2.sign| = 1 := by cases z.2 <;> norm_num [BinaryOutcome.sign]
  have hab : |(f.axis z.1).1 i * z.2.sign| ≤ 1 := by
    rw [abs_mul, hy, mul_one]
    exact axis_coordinate_bound f z.1 i
  have hc : |theta.1 i / 3| ≤ 1 := by rw [abs_div]; norm_num; linarith
  change |(f.axis z.1).1 i * z.2.sign - theta.1 i / 3| ≤ 2
  exact (abs_sub _ _).trans (by linarith)

/-- Both centered sufficient statistics obey a strong law on the actual Born
trajectory, for every history-dependent orthonormal frame policy. -/
theorem sufficientStatistics_centered_ae (policy : FramePolicy)
    (theta : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂pathMeasure policy theta,
      (∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range (N+1),
          (actualAxis policy k path i * actualAxis policy k path j -
            (if i = j then 1 else 0) / 3)) atTop (nhds 0)) ∧
      (∀ i : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range (N+1),
          (actualAxis policy k path i * (path k).2.sign - theta.1 i / 3))
        atTop (nhds 0)) := by
  have hg : ∀ᵐ path ∂pathMeasure policy theta, ∀ i j : Fin 3,
      Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range (N+1), rewardValue policy (gramReward i j) k path)
        atTop (nhds 0) := by
    exact ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      centeredReward_average_ae policy theta (gramReward i j) 2 (by norm_num)
        (gramReward_bound i j) (gramReward_mean theta i j)
  have hr : ∀ᵐ path ∂pathMeasure policy theta, ∀ i : Fin 3,
      Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range (N+1), rewardValue policy (responseReward theta i) k path)
        atTop (nhds 0) := by
    exact ae_all_iff.2 fun i => centeredReward_average_ae policy theta
      (responseReward theta i) 2 (by norm_num)
      (responseReward_bound theta i) (responseReward_mean theta i)
  filter_upwards [hg, hr] with path hp hq
  exact ⟨hp, hq⟩

end
end QubitOracle.AdaptiveDesign.P1
