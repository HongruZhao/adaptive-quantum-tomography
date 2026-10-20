-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeometry

/-! At the aligned balanced pair all outcome probabilities are 1/D.
Consequently ordinary tangent least squares has the efficient sandwich
covariance. These are polynomial moment identities, with no division by
small observed probabilities. -/
namespace QubitOracle.AdaptiveDesign.PVMUniformMoments
open QubitOracle QubitOracle.Paper PVMGeometry Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
variable {d : ℕ}

def basisGram (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ k, fixedChartBasisGradient B k x*fixedChartBasisGradient B k y

def basisMoment (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ := fun x y =>
  ∑ k, fixedChartBasisProbability B k *
    (fixedChartBasisGradient B k x-∑ l, fixedChartBasisProbability B l*fixedChartBasisGradient B l x) *
    (fixedChartBasisGradient B k y-∑ l, fixedChartBasisProbability B l*fixedChartBasisGradient B l y)

lemma gradient_sum (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (x : TangentIndex d) :
    ∑ k, fixedChartBasisGradient B k x=0 := by
  have hrow (r : Fin d) : ∑ k, star (B 0 k)*B r.succ k = 0 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hB) r.succ) 0
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using h
  cases x with
  | inl r => simpa only [fixedChartBasisGradient, ← Complex.re_sum, hrow r, Complex.zero_re]
  | inr r => simpa only [fixedChartBasisGradient, ← Complex.im_sum, hrow r, Complex.zero_im]

lemma basisGram_eq_fisher (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (p : ℝ) (hp : p ≠ 0) (huniform : ∀ k, fixedChartBasisProbability B k=p) :
    basisGram B = p • fixedChartBasisFisher B := by
  ext x y
  simp only [basisGram, fixedChartBasisFisher, classicalFisher, huniform,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

lemma basisMoment_eq_gram (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (p : ℝ)
    (huniform : ∀ k, fixedChartBasisProbability B k=p) :
    basisMoment B = p • basisGram B := by
  ext x y
  simp only [basisMoment, huniform, ← Finset.mul_sum, gradient_sum B hB,
    mul_zero, sub_zero, basisGram, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

def stageGram (F : OracleFrame d) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  (1/2:ℝ) • basisGram (controllerChiBasis F U)+(1/2:ℝ) • basisGram (controllerTauBasis F U)

def stageMoment (F : OracleFrame d) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  (1/2:ℝ) • basisMoment (controllerChiBasis F U)+(1/2:ℝ) • basisMoment (controllerTauBasis F U)

lemma basisGram_continuous : Continuous (basisGram (d:=d)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  apply continuous_finset_sum
  intro k _
  exact (continuous_fixedChartBasisGradient k x).mul (continuous_fixedChartBasisGradient k y)

lemma basisMoment_continuous : Continuous (basisMoment (d:=d)) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  unfold basisMoment
  apply continuous_finset_sum
  intro k _
  apply ((continuous_fixedChartBasisProbability k).mul
    ((continuous_fixedChartBasisGradient k x).sub ?_)).mul
    ((continuous_fixedChartBasisGradient k y).sub ?_)
  all_goals
    apply continuous_finset_sum
    intro l _
    exact (continuous_fixedChartBasisProbability l).mul (continuous_fixedChartBasisGradient l _)

lemma stageGram_continuous (F : OracleFrame d) : Continuous (stageGram F) :=
  ((basisGram_continuous.comp (continuous_controllerChiBasis F)).const_smul (1/2:ℝ)).add
    ((basisGram_continuous.comp (continuous_controllerTauBasis F)).const_smul (1/2:ℝ))

lemma stageMoment_continuous (F : OracleFrame d) : Continuous (stageMoment F) :=
  ((basisMoment_continuous.comp (continuous_controllerChiBasis F)).const_smul (1/2:ℝ)).add
    ((basisMoment_continuous.comp (continuous_controllerTauBasis F)).const_smul (1/2:ℝ))

lemma stageGram_aligned (F : OracleFrame d) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (hoverlap : controllerTrueOverlapSq U=1) :
    stageGram F U = (1/(2*(d+1:ℝ))) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  have hc k : fixedChartBasisProbability (controllerChiBasis F U) k=1/(d+1:ℝ) := by
    rw [controllerChiProbability_eq_baseProbability_of_overlap_one F U hU hoverlap,
      baseProbability_eq_inv_dimension]
  have ht k : fixedChartBasisProbability (controllerTauBasis F U) k=1/(d+1:ℝ) := by
    rw [controllerTauProbability_eq_baseProbability_of_overlap_one F U hU hoverlap,
      baseProbability_eq_inv_dimension]
  rw [stageGram, basisGram_eq_fisher _ _ (by positivity) hc,
    basisGram_eq_fisher _ _ (by positivity) ht]
  have he : (1/2:ℝ) • ((1/(d+1:ℝ)) • fixedChartBasisFisher (controllerChiBasis F U))+
      (1/2:ℝ) • ((1/(d+1:ℝ)) • fixedChartBasisFisher (controllerTauBasis F U)) =
      (1/(d+1:ℝ)) • rankOneStageInformation F U := by
    simp only [rankOneStageInformation, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [he, rankOneStageInformation_eq_half_identity_of_overlap_one F U hU hoverlap, smul_smul]
  congr 1
  field_simp
  <;> ring

lemma stageMoment_aligned (F : OracleFrame d) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (hoverlap : controllerTrueOverlapSq U=1) :
    stageMoment F U = (1/(2*(d+1:ℝ)^2)) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  have hc k : fixedChartBasisProbability (controllerChiBasis F U) k=1/(d+1:ℝ) := by
    rw [controllerChiProbability_eq_baseProbability_of_overlap_one F U hU hoverlap,
      baseProbability_eq_inv_dimension]
  have ht k : fixedChartBasisProbability (controllerTauBasis F U) k=1/(d+1:ℝ) := by
    rw [controllerTauProbability_eq_baseProbability_of_overlap_one F U hU hoverlap,
      baseProbability_eq_inv_dimension]
  have hchi : controllerChiBasis F U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hU (chiBasis_mem_unitary F)
  have htau : controllerTauBasis F U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hU (tauBasis_mem_unitary F)
  rw [stageMoment, basisMoment_eq_gram _ hchi _ hc, basisMoment_eq_gram _ htau _ ht]
  have he : (1/2:ℝ) • ((1/(d+1:ℝ)) • basisGram (controllerChiBasis F U))+
      (1/2:ℝ) • ((1/(d+1:ℝ)) • basisGram (controllerTauBasis F U)) =
      (1/(d+1:ℝ)) • stageGram F U := by
    simp only [stageGram, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  rw [he, stageGram_aligned F U hU hoverlap, smul_smul]
  congr 1
  field_simp
  <;> ring

/-- Both moments converge using only the controller ray; the complement
need not converge. -/
theorem stage_moments_tendsto (F : OracleFrame d)
    (U : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hoverlap : Tendsto (fun n => controllerTrueOverlapSq (U n)) atTop (𝓝 1)) :
    Tendsto (fun n => stageGram F (U n)) atTop
      (𝓝 ((1/(2*(d+1:ℝ))) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
    Tendsto (fun n => stageMoment F (U n)) atTop
      (𝓝 ((1/(2*(d+1:ℝ)^2)) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  constructor
  · exact tendsto_of_compact_identified_fiber _ isCompact_unitaryMatrices U hU
      controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 hoverlap
      (stageGram F) _ (fun A hA ho => ⟨(stageGram_continuous F).continuousAt,stageGram_aligned F A hA ho⟩)
  · exact tendsto_of_compact_identified_fiber _ isCompact_unitaryMatrices U hU
      controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 hoverlap
      (stageMoment F) _ (fun A hA ho => ⟨(stageMoment_continuous F).continuousAt,stageMoment_aligned F A hA ho⟩)

end
end QubitOracle.AdaptiveDesign.PVMUniformMoments

-/
