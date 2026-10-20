-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralAdaptiveTheorem
import QubitOracle.AdaptiveDesign.TangentGLSActualRates

/-! The preliminary quarter rate follows from the accumulated exploration
budget and bounded martingale innovations, not from an estimator premise. -/
namespace QubitOracle.AdaptiveDesign.PVMGeneralAdaptive
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open PVMExplorationSchedule CoerciveLeastSquares AdaptiveRidgeConsistency
open BoundedResponseQuarterRate ProbabilityCalculus FiniteDimensionalResponseRates
open GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController P2Adaptive
open scoped BigOperators Topology InnerProductSpace
noncomputable section
variable [PVMExplorationSchedule.Schedule]
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

lemma quarterScale_mul_sqrt (n : ℕ) :
    quarterScale n * Real.sqrt ((n+1 : ℕ) : ℝ) = ((n:ℝ)+1)^(3/4:ℝ) := by
  simp only [quarterScale, Real.sqrt_eq_rpow, Nat.cast_add, Nat.cast_one]
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
  norm_num

lemma quarter_budget_rate : Tendsto (fun n : ℕ =>
    quarterScale n * Real.sqrt ((n+1 : ℕ):ℝ) / (1 + budget (n+1))) atTop (𝓝 0) := by
  simp_rw [quarterScale_mul_sqrt]
  have hs := budget_rate.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero (fun n => div_nonneg (by positivity) (budget_add_one_pos (n+1)).le) _ hs
  intro n
  apply div_le_div_of_nonneg_right _ (budget_add_one_pos (n+1)).le
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

variable {Theta Action Outcome E : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem scheduled_estimate_quarterRate
    (kernel : Theta → Kernel (ℕ × Action) Outcome)
    (hk : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : ℕ → Action → E →ₗ[ℝ] E)
    (response : ℕ → Action → Outcome → E)
    (truth : E) (controller : E → Action) (refresh : ℕ → Bool)
    (κ : ℝ) (hκ : 0 < κ) (hf0 : ∀ n a, Coercive (frame n a) 0)
    (hf : ∀ n a, Coercive (frame n a) (κ * epsilon n))
    (hmean : ∀ n a, ∫ y, response n a y ∂kernel theta (n,a) = frame n a truth)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n a y, ‖response n a y - frame n a truth‖ ≤ C) :
    let p := ScheduledRidgeController.protocol kernel hk frame response controller refresh
      1 0 zero_lt_one le_rfl hf0
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n path => quarterScale n •
        ((ScheduledRidgeController.pathState frame response controller refresh
          1 0 zero_lt_one le_rfl hf0 path (n+1)).estimate zero_lt_one - truth))
      atTop (fun _ => (0:E)) := by
  intro p
  letI : IsMarkovKernel (kernel theta) := hk theta
  let centered : (ℕ × Action) → Outcome → E :=
    fun a y => response a.1 a.2 y - frame a.1 a.2 truth
  have hc : ∀ a, ∫ y, centered a y ∂p.response theta a = 0 := by
    intro a
    change (∫ y, response a.1 a.2 y - frame a.1 a.2 truth ∂kernel theta a) = 0
    rw [integral_sub Integrable.of_finite (integrable_const _), hmean]
    simp
  let noise := fun n path => ∑ k ∈ Finset.range (n+1), actualVectorResponse p centered k path
  have ht := actualResponse_rootTight_normed p theta centered hc C hC
    (fun a y => hbound a.1 a.2 y)
  have hconst : TightNorm (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n (_ : AdaptiveInfinitePath Outcome) =>
        (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (-truth)) atTop := by
    apply tight_uniform_bound ‖truth‖
    intro n path
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    apply inv_le_one_of_one_le₀
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using Real.sqrt_le_sqrt hn
  have hbiased : TightNorm (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (noise n path-truth)) atTop := by
    simpa only [noise, sub_eq_add_neg, smul_add, smul_neg] using tight_add ht hconst
  let c : ℝ := min 1 κ
  have hcp : 0 < c := lt_min (by norm_num) hκ
  have hsmall : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n (_ : AdaptiveInfinitePath Outcome) =>
        quarterScale n * Real.sqrt ((n+1:ℕ):ℝ) / (1 + budget (n+1)) / c)
      atTop (fun _ => (0:ℝ)) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound _ (by simpa using (quarter_budget_rate.div_const c).norm)
    intro n path
    simp [norm_div, norm_mul, Nat.cast_add, Nat.cast_one]
  apply product_bound_zero hsmall hbiased
  intro n path
  let fr := fun k => frame k (ScheduledRidgeController.pathState frame response controller refresh
      1 0 zero_lt_one le_rfl hf0 path k).action
  let re := fun k => response k (ScheduledRidgeController.pathState frame response controller refresh
      1 0 zero_lt_one le_rfl hf0 path k).action (path k)
  have hg := PVMExplorationSchedule.gram_coercive
    (fun k => frame k (ScheduledRidgeController.pathState frame response controller refresh
      1 0 zero_lt_one le_rfl hf0 path k).action) κ hκ (fun k => hf k _) (n+1)
  have hb := norm_le_residual_div _ _
    (mul_pos hcp (budget_add_one_pos (n+1))) hg _ _
    (ridgeEstimate_errorEquation fr re truth 1 0 zero_lt_one le_rfl
      (fun k => hf0 k _) (n+1))
  simp only [one_smul] at hb
  rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (quarterScale_pos n)]
  calc
    _ ≤ quarterScale n * (‖noise n path-truth‖ / (c * (1+budget (n+1)))) :=
      mul_le_mul_of_nonneg_left hb (quarterScale_pos n).le
    _ = _ := by
      have hscalar : 0 ≤ quarterScale n * Real.sqrt ((n+1:ℕ):ℝ) / (1+budget (n+1)) / c :=
        div_nonneg (div_nonneg (mul_nonneg (quarterScale_pos n).le
          (Real.sqrt_nonneg _)) (budget_add_one_pos (n+1)).le) hcp.le
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscalar,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg ((n+1:ℕ):ℝ)))]
      have hs : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hm := (budget_add_one_pos (n+1)).ne'
      field_simp

variable (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d]

theorem rawEstimator_quarterRate (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)
      (fun n path => quarterScale n • (rawEstimator d batchSize path (n+1)-theta.1))
      atTop (fun _ => (0 : HermitianSpace (d+1))) := by
  exact scheduled_estimate_quarterRate PVMGeneralExploration.bornKernel
    PVMGeneralExploration.bornKernel_isMarkov theta
    PVMGeneralExploration.regressionFrame (fun _ => PVMGeneralExploration.responseVector)
    theta.1 (physicalController d) (SequentialRidgeController.batchRefresh batchSize)
    (PVMGeneralExploration.coercivityConstant d) (PVMGeneralExploration.coercivityConstant_pos d)
    PVMGeneralExploration.regressionFrame_nonnegative PVMGeneralExploration.regressionFrame_coercive
    (fun n a => PVMGeneralExploration.responseVector_mean theta (n,a))
    (2 * PVMGeometry.basisBound d) (mul_nonneg (by norm_num) (PVMGeometry.basisBound_nonnegative d))
    (fun n a y => PVMGeneralExploration.responseInnovation_bound theta (n,a) y)

end
end QubitOracle.AdaptiveDesign.PVMGeneralAdaptive

-/
