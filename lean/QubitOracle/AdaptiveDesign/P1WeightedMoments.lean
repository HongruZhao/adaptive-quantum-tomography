import QubitOracle.AdaptiveDesign.AdaptiveExplorationRate
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveBornProtocol
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1UniformFrameBorn
/-! All stochastic inputs are derived from the exact adaptive Born law.
In particular, the realized Gram innovations and regression residuals obey
quantitative martingale laws before any estimator limit is assumed. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

theorem axis_abs_le_one (a : Action) (k i : Fin 3) : |axis a k i| ≤ 1 :=
  P1.axis_coordinate_bound a.frame k i

theorem gram_entry_bound (a : Action) (i j : Fin 3) : |gram a i j| ≤ 1 := by
  simp only [gram,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,blochOuter]
  calc
    _ ≤ ∑ k, |a.weight k * (axis a k i * axis a k j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, a.weight k := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg (a.nonneg k)]
      have h : |axis a k i * axis a k j| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (axis_abs_le_one a k i) (axis_abs_le_one a k j)
          (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      simpa using mul_le_mul_of_nonneg_left h (a.nonneg k)
    _ = 1 := a.total

theorem gram_innovation_bound (a : Action) (z : LabeledBinaryOutcome) (i j : Fin 3) :
    ‖axis a z.1 i * axis a z.1 j - gram a i j‖ ≤ 2 := by
  rw [Real.norm_eq_abs]
  have h : |axis a z.1 i * axis a z.1 j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (axis_abs_le_one a z.1 i) (axis_abs_le_one a z.1 j)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (abs_sub _ _).trans (by linarith [gram_entry_bound a i j])

theorem residual_coordinate_bound (θ : OneQubitPhysicalParameter) (a : Action)
    (z : LabeledBinaryOutcome) (i : Fin 3) : |residual θ.1 a z i| ≤ 2 := by
  have ht : |blochDot θ.1 (axis a z.1)| ≤ 1 := by
    simpa only [generalAxisBornProjection,axis,blochDot,mul_comm] using
      generalAxisBornProjection_abs_le_one θ (a.frame.axis z.1)
  have hs : |z.2.sign| = 1 := by cases z.2 <;> norm_num [BinaryOutcome.sign]
  change |axis a z.1 i * (z.2.sign - blochDot θ.1 (axis a z.1))| ≤ 2
  rw [abs_mul]
  have hres : |z.2.sign - blochDot θ.1 (axis a z.1)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  nlinarith [axis_abs_le_one a z.1 i,abs_nonneg (axis a z.1 i),abs_nonneg (z.2.sign - blochDot θ.1 (axis a z.1))]

theorem residual_bound (θ : OneQubitPhysicalParameter) (a : Action) (z : LabeledBinaryOutcome) :
    ‖residual θ.1 a z‖ ≤ 6 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ i : Fin 3, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := residual_coordinate_bound θ a z i
      have hs := (sq_le_sq₀ (abs_nonneg (residual θ.1 a z i)) (by norm_num : (0:ℝ)≤2)).mpr hh
      simpa only [sq_abs, show (2:ℝ)^2=4 by norm_num] using hs
    _ ≤ (6:ℝ)^2 := by norm_num

/-- The realized design matrix differs from its predictable mean by o(n^(3/4)). -/
theorem gram_innovation_rate (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ, ∀ i j : Fin 3,
      Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) *
        ∑ t ∈ Finset.range n, (actualAxis p t path i * actualAxis p t path j -
          gram (actualAction p t path) i j)) atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  exact ExplorationRate.actualResponse_threeQuarter_ae_tendsto_zero (protocol p) θ
    (fun a z => axis a z.1 i * axis a z.1 j - gram a i j)
    (fun a => gram_centered_mean θ a i j) 2 (by norm_num)
    (fun a z => gram_innovation_bound a z i j)

/-- The regression residual sum is o(n^(3/4)) under the actual adaptive law. -/
theorem residual_rate (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) •
        ∑ t ∈ Finset.range n, residual θ.1 (actualAction p t path) (path t)) atTop (𝓝 0) :=
  ExplorationRate.actualVectorResponse_threeQuarter_ae_tendsto_zero (protocol p) θ
    (residual θ.1) (residual_mean θ) 6 (by norm_num) (residual_bound θ)

end
end QubitOracle.AdaptiveDesign.P1Weighted
