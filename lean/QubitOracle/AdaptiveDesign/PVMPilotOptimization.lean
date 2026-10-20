-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotAdaptiveTheorem

/-! The exploration pilot is the unique minimizer of the displayed
design-averaged quadratic objective, for every finite recorded path. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotAdaptive
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian CoerciveLeastSquares
open FiniteFrameCoercivity PVMPilotSchedule
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def pilotObjective (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d))
    (A : HermitianSpace (d+1)) : ℝ :=
  ‖A‖^2/2+(∑ t ∈ Finset.range n, epsilon t)/2*
    ⟪A,PVMGeneralGeometry.explorationFrame d A⟫_ℝ-
    ∑ t ∈ Finset.range n, ⟪A,PVMPilotRegression.response
      (actualState d batchSize path t).action (path t)⟫_ℝ

theorem frame_inner_symmetric (x y : HermitianSpace (d+1)) :
    ⟪PVMGeneralGeometry.explorationFrame d x,y⟫_ℝ=
      ⟪x,PVMGeneralGeometry.explorationFrame d y⟫_ℝ := by
  simp only [PVMGeneralGeometry.explorationFrame,LinearMap.smul_apply,frameOperator_apply,
    inner_smul_left,inner_smul_right,inner_sum,sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm x]
  simp only [starRingEnd_apply,star_trivial]
  ring

theorem pilotObjective_expansion (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (A : HermitianSpace (d+1)) :
    pilotObjective batchSize n path A-pilotObjective batchSize n path (rawEstimator d batchSize path n)=
      ‖A-rawEstimator d batchSize path n‖^2/2+
      (∑ t ∈ Finset.range n, epsilon t)/2*
        ⟪A-rawEstimator d batchSize path n,
          PVMGeneralGeometry.explorationFrame d (A-rawEstimator d batchSize path n)⟫_ℝ := by
  let fr := fun k => PVMPilotRegression.frame k (actualState d batchSize path k).action
  let re := fun k => PVMPilotRegression.response (actualState d batchSize path k).action (path k)
  let a := rawEstimator d batchSize path n
  have hnormal : a+(∑ t ∈ Finset.range n, epsilon t) • PVMGeneralGeometry.explorationFrame d a=
      ∑ t ∈ Finset.range n, re t := by
    have he : a=ridgeEstimate fr re 1 0 zero_lt_one le_rfl
        (fun k => PVMPilotRegression.frame_nonnegative k _) n := by
      dsimp [a,rawEstimator,actualState]
      exact ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate _ _ _ _ _ _ _ _ _ _ _
    have hh := ridgeEstimate_normalEquation fr re 1 0 zero_lt_one le_rfl
      (fun k => PVMPilotRegression.frame_nonnegative k _) n
    rw [← he,ridgeGram_apply] at hh
    simpa only [one_smul,fr,PVMPilotRegression.frame,LinearMap.smul_apply,← Finset.sum_smul] using hh
  have hi := congrArg (fun z => ⟪A-a,z⟫_ℝ) hnormal
  simp only [inner_add_right,inner_smul_right,inner_sum,inner_sub_left] at hi
  have hcross : ⟪a,PVMGeneralGeometry.explorationFrame d A⟫_ℝ=
      ⟪A,PVMGeneralGeometry.explorationFrame d a⟫_ℝ :=
    (real_inner_comm _ _).trans (frame_inner_symmetric A a)
  change pilotObjective batchSize n path A-pilotObjective batchSize n path a=
    ‖A-a‖^2/2+(∑ t ∈ Finset.range n, epsilon t)/2*
      ⟪A-a,PVMGeneralGeometry.explorationFrame d (A-a)⟫_ℝ
  simp only [pilotObjective,norm_sub_sq_real,map_sub,inner_sub_left,inner_sub_right]
  change ‖A‖^2/2+_ - (∑ t ∈ Finset.range n, ⟪A,re t⟫_ℝ)-
    (‖a‖^2/2+_ -(∑ t ∈ Finset.range n, ⟪a,re t⟫_ℝ))=_
  rw [hcross]
  simp only [Finset.sum_sub_distrib,real_inner_self_eq_norm_sq] at hi
  nlinarith

theorem pilot_unique_minimizer (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) :
    (∀ A, pilotObjective batchSize n path (rawEstimator d batchSize path n) ≤
      pilotObjective batchSize n path A) ∧
    (∀ A, pilotObjective batchSize n path A=
      pilotObjective batchSize n path (rawEstimator d batchSize path n) →
      A=rawEstimator d batchSize path n) := by
  have hquad (A : HermitianSpace (d+1)) :
      0 ≤ ⟪A,PVMGeneralGeometry.explorationFrame d A⟫_ℝ := by
    simp only [PVMGeneralGeometry.explorationFrame,LinearMap.smul_apply,inner_smul_right,
      frameOperator_quadratic]
    positivity
  have hE : 0 ≤ ∑ t ∈ Finset.range n, epsilon t :=
    Finset.sum_nonneg (fun t _ => epsilon_nonnegative t)
  constructor
  · intro A
    have he := pilotObjective_expansion batchSize n path A
    have hp := mul_nonneg (div_nonneg hE (by norm_num : (0:ℝ) ≤ 2))
      (hquad (A-rawEstimator d batchSize path n))
    linarith [sq_nonneg ‖A-rawEstimator d batchSize path n‖]
  · intro A hA
    have he := pilotObjective_expansion batchSize n path A
    have hp := mul_nonneg (div_nonneg hE (by norm_num : (0:ℝ) ≤ 2))
      (hquad (A-rawEstimator d batchSize path n))
    have hz : ‖A-rawEstimator d batchSize path n‖=0 := by
      rw [hA,sub_self] at he
      nlinarith [norm_nonneg (A-rawEstimator d batchSize path n)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end
end QubitOracle.AdaptiveDesign.PVMPilotAdaptive

-/
