import QubitOracle.AdaptiveDesign.P1WeightedLimits
import QubitOracle.Paper.P1BuresOptimality

/-! Exact inverse-information and least-squares sandwich identities. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

def affine (r : Fin 3 → ℝ) (a b : ℝ) : Mat := a • 1 + b • blochOuter r

theorem outer_sq (r : Fin 3 → ℝ) : blochOuter r * blochOuter r = blochNormSq r • blochOuter r := by
  ext i j
  simp [blochOuter,Matrix.mul_apply,Matrix.smul_apply,blochNormSq,Fin.sum_univ_succ]
  ring

theorem affine_mul (r : Fin 3 → ℝ) (a b c d : ℝ) :
    affine r a b * affine r c d = affine r (a*c) (a*d+b*c+b*d*blochNormSq r) := by
  simp only [affine,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,outer_sq,smul_smul]
  module

theorem affine_transpose (r : Fin 3 → ℝ) (a b : ℝ) : (affine r a b).transpose = affine r a b := by
  ext i j
  simp [affine,Matrix.one_apply,blochOuter,mul_comm,eq_comm]

theorem affine_posDef (r : Fin 3 → ℝ) (a b : ℝ) (hb : b ≤ 0)
    (hab : 0 < a+b*blochNormSq r) : (affine r a b).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using affine_transpose r a b
  · intro x hx
    have hx0 : 0 < blochNormSq x := lt_of_le_of_ne (normSq_nonneg x)
      (Ne.symm (fun hz => hx (normSq_eq_zero x hz)))
    have hq : star x ⬝ᵥ (affine r a b).mulVec x =
        a*blochNormSq x+b*(blochDot r x)^2 := by
      change quadratic (affine r a b) x = _
      rw [affine,quadratic_add,quadratic_smul,quadratic_one,quadratic_smul,quadratic_outer]
    rw [hq]
    have hc := mul_le_mul_of_nonpos_left (bloch_cauchy_schwarz r x) hb
    nlinarith [mul_pos hab hx0]

theorem meanGram_affine (loss : Loss) (r : Fin 3 → ℝ) :
    meanGramTarget loss r = match loss with
    | .bures => affine r (1/3) 0
    | .frobenius => affine r (2+mixedRadialGap r)⁻¹ (-((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹) := by
  cases loss <;> simp [meanGramTarget,affine,sub_eq_add_neg,neg_smul]

theorem covariance_affine (loss : Loss) (r : Fin 3 → ℝ) :
    covarianceTarget loss r = match loss with
    | .bures => affine r 3 (-3)
    | .frobenius => affine r (2+mixedRadialGap r) (-(2+mixedRadialGap r)/(1+mixedRadialGap r)) := by
  cases loss <;> simp [covarianceTarget,affine,smul_sub,smul_smul,div_eq_mul_inv,sub_eq_add_neg,neg_smul]
  module

theorem meanGram_posDef (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (meanGramTarget loss r).PosDef := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  cases loss <;> rw [meanGram_affine]
  · exact affine_posDef r (1/3) 0 (by norm_num) (by norm_num)
  · apply affine_posDef r _ _
    · exact neg_nonpos.mpr (by positivity)
    · have he : (2+mixedRadialGap r)⁻¹ +
          -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*blochNormSq r =
          mixedRadialGap r/(2+mixedRadialGap r) := by
        rw [hn]
        field_simp
        ring
      rw [he]
      positivity

theorem covariance_posDef (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (covarianceTarget loss r).PosDef := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  cases loss <;> rw [covariance_affine]
  · apply affine_posDef r 3 (-3) (by norm_num)
    linarith
  · apply affine_posDef r _ _
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have he : (2+mixedRadialGap r)+(-(2+mixedRadialGap r)/(1+mixedRadialGap r))*blochNormSq r =
          (2+mixedRadialGap r)*mixedRadialGap r := by
        rw [hn]
        field_simp
        ring
      rw [he]
      positivity

theorem information_mul_covariance (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    informationTarget loss r * covarianceTarget loss r = 1 := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  have h1 : 1+mixedRadialGap r ≠ 0 := by positivity
  have h2 : 2+mixedRadialGap r ≠ 0 := by positivity
  have hg : 1-blochNormSq r ≠ 0 := (sub_pos.mpr hr).ne'
  cases loss with
  | bures =>
    change affine r (1/3) (3*(1-blochNormSq r))⁻¹ * covarianceTarget .bures r = 1
    rw [covariance_affine,affine_mul]
    have hb : (1/3:ℝ)*(-3)+(3*(1-blochNormSq r))⁻¹*3+
        (3*(1-blochNormSq r))⁻¹*(-3)*blochNormSq r = 0 := by field_simp; ring
    rw [hb]
    norm_num [affine]
  | frobenius =>
    change affine r (2+mixedRadialGap r)⁻¹ (mixedRadialGap r*(2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ *
      covarianceTarget .frobenius r = 1
    rw [covariance_affine,affine_mul,inv_mul_cancel₀ h2]
    have hb : (2+mixedRadialGap r)⁻¹*(-(2+mixedRadialGap r)/(1+mixedRadialGap r))+
        (mixedRadialGap r*(2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*(2+mixedRadialGap r)+
        (mixedRadialGap r*(2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*
          (-(2+mixedRadialGap r)/(1+mixedRadialGap r))*blochNormSq r = 0 := by
      rw [hn]
      field_simp
      ring
    rw [hb]
    simp [affine]

theorem covariance_eq_information_inv (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    covarianceTarget loss r = (informationTarget loss r)⁻¹ :=
  (Matrix.inv_eq_right_inv (information_mul_covariance loss r hr)).symm

theorem sandwich_identity (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    meanGramTarget loss r * covarianceTarget loss r * meanGramTarget loss r = noiseTarget loss r := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  have h1 : 1+mixedRadialGap r ≠ 0 := by positivity
  have h2 : 2+mixedRadialGap r ≠ 0 := by positivity
  rw [noiseTarget]
  cases loss with
  | bures =>
    rw [meanGram_affine,covariance_affine,affine_mul,affine_mul]
    norm_num [affine,radialWeight]
    module
  | frobenius =>
    rw [meanGram_affine,covariance_affine,affine_mul,affine_mul]
    have ha : ((2+mixedRadialGap r)⁻¹*(2+mixedRadialGap r))*(2+mixedRadialGap r)⁻¹ =
        (2+mixedRadialGap r)⁻¹ := by field_simp
    rw [ha]
    unfold affine radialWeight mixedRadialAllocation
    suffices hc :
        ((2+mixedRadialGap r)⁻¹*(2+mixedRadialGap r)) * -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ +
        ((2+mixedRadialGap r)⁻¹*(-(2+mixedRadialGap r)/(1+mixedRadialGap r))+
          -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*(2+mixedRadialGap r)+
          -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*(-(2+mixedRadialGap r)/(1+mixedRadialGap r))*blochNormSq r) *
            (2+mixedRadialGap r)⁻¹ +
        ((2+mixedRadialGap r)⁻¹*(-(2+mixedRadialGap r)/(1+mixedRadialGap r))+
          -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*(2+mixedRadialGap r)+
          -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹*(-(2+mixedRadialGap r)/(1+mixedRadialGap r))*blochNormSq r) *
            -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ * blochNormSq r =
        -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹-mixedRadialGap r/(2+mixedRadialGap r) by
      rw [hc]
      module
    rw [hn]
    field_simp
    ring

theorem inverse_sandwich (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (meanGramTarget loss r)⁻¹ * noiseTarget loss r * (meanGramTarget loss r)⁻¹ = covarianceTarget loss r := by
  have hd := isUnit_iff_ne_zero.mpr (meanGram_posDef loss r hr).det_pos.ne'
  rw [← sandwich_identity loss r hr]
  calc
    _ = ((meanGramTarget loss r)⁻¹ * meanGramTarget loss r) * covarianceTarget loss r *
      (meanGramTarget loss r * (meanGramTarget loss r)⁻¹) := by noncomm_ring
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hd,Matrix.mul_nonsing_inv _ hd,one_mul,mul_one]

end
end QubitOracle.AdaptiveDesign.P1Weighted
