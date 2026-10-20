-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotBorn
import QubitOracle.AdaptiveDesign.AdaptiveBudgetResponses

/-! The exploration-only linear fit. Its design operator is deterministic,
and its noise variance is proportional to the exploration probability. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotRegression
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry PVMGeneralGeometry PVMPilotBorn PVMPilotSchedule
open FiniteFrameCoercivity CoerciveLeastSquares MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

def response (U : Action d) (o : Outcome d) : HermitianSpace (d+1) :=
  match o.1 with
  | .inl _ => 0
  | .inr l => basisEffect (PVMGeneralGeometry.explorationBasis l) o.2

def frame (n : ℕ) (_U : Action d) : HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  epsilon n • PVMGeneralGeometry.explorationFrame d

lemma response_bound (U : Action d) (o : Outcome d) : ‖response U o‖ ≤ basisBound d := by
  cases h : o.1 with
  | inl b => simpa [response, h] using basisBound_nonnegative d
  | inr l => simpa [response, h] using basisEffect_bound (PVMGeneralGeometry.explorationBasis l) o.2

lemma response_mean (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, response a.2 o ∂PVMPilotBorn.bornKernel theta a = frame a.1 a.2 theta.1 := by
  change (∫ o, response a.2 o ∂finiteMassMeasure (PVMPilotBorn.bornProbability theta a)
    (PVMPilotBorn.bornProbability_nonnegative theta a) (PVMPilotBorn.bornProbability_sum theta a)) = _
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [PVMPilotBorn.bornProbability, settingWeight, response, settingBasis,
    smul_zero, Finset.sum_const_zero, zero_add, frame, LinearMap.smul_apply,
    PVMGeneralGeometry.explorationFrame, frameOperator_apply, Fintype.sum_prod_type,
    Finset.smul_sum, smul_smul, basisProbability]

lemma frame_coercive (n : ℕ) (U : Action d) :
    Coercive (frame n U) (PVMPilotBorn.coercivityConstant d * epsilon n) := by
  intro A
  have h := (Classical.choose_spec (PVMGeneralGeometry.explorationFrame_coercive d)).2 A
  have hs := mul_le_mul_of_nonneg_left h (epsilon_nonnegative n)
  rw [frame, LinearMap.smul_apply, inner_smul_right]
  simpa [PVMPilotBorn.coercivityConstant, mul_comm, mul_left_comm, mul_assoc] using hs

lemma frame_nonnegative (n : ℕ) (U : Action d) : Coercive (frame n U) 0 := by
  intro A
  have h := frame_coercive n U A
  have hk := PVMPilotBorn.coercivityConstant_pos d
  have he := epsilon_nonnegative n
  simp only [zero_mul]
  exact (mul_nonneg (mul_nonneg hk.le he) (sq_nonneg _)).trans h

lemma frame_truth_bound (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ‖frame a.1 a.2 theta.1‖ ≤ basisBound d := by
  rw [← response_mean]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : Outcome d, basisBound d ∂PVMPilotBorn.bornKernel theta a := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro o
      exact response_bound _ _
    _ = _ := by simp

def noise (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) (o : Outcome d) :
    HermitianSpace (d+1) := response a.2 o-frame a.1 a.2 theta.1

lemma noise_mean (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, noise theta a o ∂PVMPilotBorn.bornKernel theta a = 0 := by
  simp only [noise]
  rw [integral_sub Integrable.of_finite (integrable_const _), response_mean]
  simp

lemma noise_bound (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) (o : Outcome d) :
    ‖noise theta a o‖ ≤ 2*basisBound d :=
  (norm_sub_le _ _).trans (by linarith [response_bound a.2 o, frame_truth_bound theta a])

lemma finite_variance_bound {O : Type*} [Fintype O] (p f : O → ℝ)
    (hp : ∑ o, p o = 1) :
    ∑ o, p o*(f o-∑ y, p y*f y)^2 ≤ ∑ o, p o*f o^2 := by
  let m := ∑ y, p y*f y
  have he : (∑ o, p o*(f o-m)^2) = (∑ o, p o*f o^2)-m^2 := by
    calc
      _ = ∑ o, (p o*f o^2-2*m*(p o*f o)+m^2*p o) := by
        apply Finset.sum_congr rfl
        intro o _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp, mul_one]
        dsimp [m]
        ring
  change (∑ o, p o*(f o-m)^2) ≤ _
  rw [he]
  linarith [sq_nonneg m]

lemma response_secondMoment (theta : PhysicalParameter (d+1)) (a : ℕ × Action d)
    (u : HermitianSpace (d+1)) :
    ∫ o, ⟪u,response a.2 o⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a ≤
      (‖u‖*basisBound d)^2*epsilon a.1 := by
  change (∫ o, ⟪u,response a.2 o⟫_ℝ^2 ∂finiteMassMeasure (PVMPilotBorn.bornProbability theta a)
    (PVMPilotBorn.bornProbability_nonnegative theta a) (PVMPilotBorn.bornProbability_sum theta a)) ≤ _
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [response, inner_zero_right, zero_pow (by norm_num : 2≠0), smul_eq_mul,
    mul_zero, Finset.sum_const_zero, zero_add, PVMPilotBorn.bornProbability, settingWeight, settingBasis]
  have hinner (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1)) :
      ⟪u,basisEffect (PVMGeneralGeometry.explorationBasis l) k⟫_ℝ^2 ≤ (‖u‖*basisBound d)^2 := by
    have h := (norm_inner_le_norm (𝕜:=ℝ) u (basisEffect (PVMGeneralGeometry.explorationBasis l) k)).trans
      (mul_le_mul_of_nonneg_left (basisEffect_bound _ _) (norm_nonneg u))
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg ⟪u,basisEffect (PVMGeneralGeometry.explorationBasis l) k⟫_ℝ,
      sq_abs ⟪u,basisEffect (PVMGeneralGeometry.explorationBasis l) k⟫_ℝ]
  calc
    _ ≤ ∑ l : PVMGeneralGeometry.ExplorationIndex d, ∑ k : Fin (d+1),
        (epsilon a.1*(Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ *
          basisProbability theta (PVMGeneralGeometry.explorationBasis l) k) * (‖u‖*basisBound d)^2 := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hinner l k) (by
        have he := epsilon_nonnegative a.1
        have hp := basisProbability_nonnegative theta (PVMGeneralGeometry.explorationBasis l) k
        positivity)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, basisProbability_sum, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hk := (PVMGeneralGeometry.exploration_card_pos d).ne'
      field_simp [hk]

lemma noise_secondMoment (theta : PhysicalParameter (d+1)) (a : ℕ × Action d)
    (u : HermitianSpace (d+1)) :
    ∫ o, ⟪u,noise theta a o⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a ≤
      (‖u‖*basisBound d)^2*epsilon a.1 := by
  have hm : ⟪u,frame a.1 a.2 theta.1⟫_ℝ =
      ∑ o, PVMPilotBorn.bornProbability theta a o * ⟪u,response a.2 o⟫_ℝ := by
    rw [← response_mean, ← integral_inner Integrable.of_finite]
    exact integral_finiteMassMeasure _ (PVMPilotBorn.bornProbability_nonnegative theta a)
      (PVMPilotBorn.bornProbability_sum theta a) _
  have hv := finite_variance_bound (PVMPilotBorn.bornProbability theta a)
    (fun o => ⟪u,response a.2 o⟫_ℝ) (PVMPilotBorn.bornProbability_sum theta a)
  have he : (∫ o, ⟪u,noise theta a o⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a) ≤
      ∫ o, ⟪u,response a.2 o⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a := by
    change (∫ o, ⟪u,noise theta a o⟫_ℝ^2 ∂finiteMassMeasure (PVMPilotBorn.bornProbability theta a)
      (PVMPilotBorn.bornProbability_nonnegative theta a) (PVMPilotBorn.bornProbability_sum theta a)) ≤ _
    rw [integral_finiteMassMeasure]
    change _ ≤ ∫ o, ⟪u,response a.2 o⟫_ℝ^2 ∂finiteMassMeasure (PVMPilotBorn.bornProbability theta a)
      (PVMPilotBorn.bornProbability_nonnegative theta a) (PVMPilotBorn.bornProbability_sum theta a)
    rw [integral_finiteMassMeasure]
    simpa only [noise, inner_sub_right, hm, smul_eq_mul] using hv
  exact he.trans (response_secondMoment theta a u)

end
end QubitOracle.AdaptiveDesign.PVMPilotRegression

-/
