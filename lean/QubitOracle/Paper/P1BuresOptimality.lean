import Mathlib.Analysis.Matrix.Order
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedOracleFeasible
import QubitOracle.Paper.MixedOracleGeometry
import QubitOracle.Paper.MixedOracleMatrix
import QubitOracle.Paper.MixedRotationalTarget
namespace QubitOracle.AdaptiveDesign.P1
open scoped BigOperators MatrixOrder
open QubitOracle.Paper
noncomputable section

private theorem sqrt_facts (P : OracleMatrix) (hP : P.PosDef) :
    let S := CFC.sqrt P
    S.transpose = S ∧ S*S=P ∧ S*S⁻¹=1 ∧ S⁻¹*S=1 ∧
      S⁻¹.transpose=S⁻¹ ∧ S⁻¹*S⁻¹=P⁻¹ := by
  dsimp only
  have hs := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hsq : CFC.sqrt P * CFC.sqrt P = P := by
    simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hd : IsUnit (CFC.sqrt P).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hsq
    simp only [Matrix.det_mul, hz, zero_mul] at hh
    exact hP.det_pos.ne' hh.symm
  refine ⟨?_,hsq,Matrix.mul_nonsing_inv _ hd,Matrix.nonsing_inv_mul _ hd,?_,?_⟩
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hs.isHermitian
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hs.inv.isHermitian
  · rw [hP.posSemidef.inv_sqrt]
    simpa only [pow_two] using CFC.sq_sqrt P⁻¹ hP.inv.posSemidef.nonneg

/-- A coordinate-free inverse-information lower bound. All square roots are
constructed internally from positive definiteness. -/
theorem inverse_information_lower_bound (P Q : OracleMatrix)
    (hP : P.PosDef) (hQ : Q.PosDef) (hbudget : (P*Q).trace ≤ 1) :
    (9 : ℝ) ≤ (P⁻¹*Q⁻¹).trace := by
  obtain ⟨hRsym,hR2,hRinv,hRinv',hRinvsym,hRinv2⟩ := sqrt_facts P hP
  obtain ⟨hSsym,hS2,hSinv,hSinv',hSinvsym,hSinv2⟩ := sqrt_facts Q hQ
  let R := CFC.sqrt P
  let S := CFC.sqrt Q
  let X := R*S
  let Y := R⁻¹*S⁻¹
  have hxy : (X.transpose * Y).trace = 3 := by
    dsimp [X,Y,R,S]
    rw [Matrix.transpose_mul,hRsym,hSsym]
    have hh : (CFC.sqrt Q * CFC.sqrt P) * ((CFC.sqrt P)⁻¹*(CFC.sqrt Q)⁻¹) = 1 := by
      calc
        _ = CFC.sqrt Q * (CFC.sqrt P * (CFC.sqrt P)⁻¹) * (CFC.sqrt Q)⁻¹ := by noncomm_ring
        _ = 1 := by rw [hRinv]; simpa using hSinv
    rw [hh]
    norm_num
  have hxx : (X.transpose * X).trace = (P*Q).trace := by
    dsimp [X,R,S]
    rw [Matrix.transpose_mul,hRsym,hSsym]
    have hh : (CFC.sqrt Q*CFC.sqrt P)*(CFC.sqrt P*CFC.sqrt Q) = CFC.sqrt Q*P*CFC.sqrt Q := by
      calc
        _ = CFC.sqrt Q*(CFC.sqrt P*CFC.sqrt P)*CFC.sqrt Q := by noncomm_ring
        _ = _ := by rw [hR2]
    rw [hh,Matrix.trace_mul_cycle,hS2,Matrix.trace_mul_comm]
  have hyy : (Y.transpose * Y).trace = (P⁻¹*Q⁻¹).trace := by
    dsimp [Y,R,S]
    rw [Matrix.transpose_mul,hRinvsym,hSinvsym]
    have hh : ((CFC.sqrt Q)⁻¹*(CFC.sqrt P)⁻¹)*((CFC.sqrt P)⁻¹*(CFC.sqrt Q)⁻¹) =
        (CFC.sqrt Q)⁻¹*P⁻¹*(CFC.sqrt Q)⁻¹ := by
      calc
        _ = (CFC.sqrt Q)⁻¹*((CFC.sqrt P)⁻¹*(CFC.sqrt P)⁻¹)*(CFC.sqrt Q)⁻¹ := by noncomm_ring
        _ = _ := by rw [hRinv2]
    rw [hh,Matrix.trace_mul_cycle,hSinv2,Matrix.trace_mul_comm]
  have hcs := frobeniusInner_sq_le X Y
  have hrisk := frobeniusSq_nonneg Y
  rw [← trace_transpose_mul_eq_frobeniusInner, hxy] at hcs
  change 3^2 ≤ frobeniusInner X X * frobeniusInner Y Y at hcs
  rw [← trace_transpose_mul_eq_frobeniusInner, ← trace_transpose_mul_eq_frobeniusInner,
    hxx,hyy] at hcs
  change 0 ≤ frobeniusInner Y Y at hrisk
  rw [← trace_transpose_mul_eq_frobeniusInner,hyy] at hrisk
  nlinarith [mul_le_mul_of_nonneg_right hbudget hrisk]

/-- The inverse SLD matrix is positive definite throughout the open Bloch ball,
including the maximally mixed state. -/
theorem qubitSLDFisherInv_posDef (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (qubitSLDFisherInv r).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · unfold Matrix.IsHermitian
    ext i j
    simp [qubitSLDFisherInv, Matrix.conjTranspose_apply, eq_comm, mul_comm]
  · intro x hx
    have hnorm : 0 < blochNormSq x := lt_of_le_of_ne (blochNormSq_nonneg x)
      (Ne.symm (fun hz => hx ((blochNormSq_eq_zero_iff x).mp hz)))
    have hcs := bloch_cauchy_schwarz r x
    have hquad : star x ⬝ᵥ ((qubitSLDFisherInv r).mulVec x) =
        blochNormSq x - (blochDot r x)^2 := by
      simp [Matrix.mulVec, dotProduct, qubitSLDFisherInv,
        blochNormSq,blochDot,Fin.sum_univ_succ]
      ring
    rw [hquad]
    nlinarith [mul_pos (sub_pos.mpr hr) hnorm]

private theorem blochOuter_mul_self (r : Fin 3 → ℝ) :
    blochOuter r * blochOuter r = blochNormSq r • blochOuter r := by
  ext i j
  simp [blochOuter,Matrix.mul_apply,Matrix.smul_apply,blochNormSq,Fin.sum_univ_succ]
  ring

/-- Exact inverse SLD Fisher formula, proved by multiplying the rank-one
update. -/
theorem qubitSLDFisherInv_inv (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (qubitSLDFisherInv r)⁻¹ = 1 + (1-blochNormSq r)⁻¹ • blochOuter r := by
  apply Matrix.inv_eq_right_inv
  have hform : qubitSLDFisherInv r = 1-blochOuter r := by
    ext i j
    simp [qubitSLDFisherInv,blochOuter,Matrix.one_apply]
  have hcoef : (1-blochNormSq r)⁻¹ - 1 -
      (1-blochNormSq r)⁻¹ * blochNormSq r = 0 := by
    field_simp [ne_of_gt (sub_pos.mpr hr)]
    ring
  rw [hform]
  calc
    (1-blochOuter r)*(1+(1-blochNormSq r)⁻¹ • blochOuter r) =
        1 + ((1-blochNormSq r)⁻¹-1-(1-blochNormSq r)⁻¹*blochNormSq r) • blochOuter r := by
      simp only [sub_mul,mul_add,one_mul,mul_one,Matrix.mul_smul,
        blochOuter_mul_self,smul_smul]
      module
    _ = 1 := by rw [hcoef]; simp

/-- The limit proved for the implemented adaptive controller is exactly one
third of the SLD Fisher matrix. -/
theorem mixedBuresTarget_eq_third_sld (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    mixedBuresTarget r = (1/3 : ℝ) • (qubitSLDFisherInv r)⁻¹ := by
  rw [qubitSLDFisherInv_inv r hr]
  simp only [mixedBuresTarget,smul_add,smul_smul]
  congr 1
  congr 1
  field_simp

/-- The local Bures inverse-information design criterion. The inverse SLD
formula immediately above identifies its weight with `H(r)/4`. -/
def buresDesignCriterion (r : Fin 3 → ℝ) (M : OracleMatrix) : ℝ :=
  (1/4 : ℝ) * ((qubitSLDFisherInv r)⁻¹*M⁻¹).trace

/-- Actual finite qubit POVMs satisfy the Bures lower bound: positivity,
completeness, and nonsingular Fisher information are the only competitor
conditions. No trace-budget or optimizer certificate is assumed. -/
theorem finite_qubitPOVM_bures_lower_bound
    (r : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    {O : Type} [Fintype O] (P : QubitBlochPOVM O)
    (hP : (qubitClassicalFisher r P).PosDef) :
    (9/4 : ℝ) ≤ buresDesignCriterion r (qubitClassicalFisher r P) := by
  have h := inverse_information_lower_bound (qubitSLDFisherInv r)
    (qubitClassicalFisher r P) (qubitSLDFisherInv_posDef r hr) hP
    (qubit_interior_gillMassar r P hr)
  unfold buresDesignCriterion
  linarith

/-- The actual Bures information limit attains the sharp bound. -/
theorem mixedBuresTarget_bures_value (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    buresDesignCriterion r (mixedBuresTarget r) = 9/4 := by
  have hpd := qubitSLDFisherInv_posDef r hr
  have hinv : (mixedBuresTarget r)⁻¹ = (3 : ℝ) • qubitSLDFisherInv r := by
    apply Matrix.inv_eq_right_inv
    rw [mixedBuresTarget_eq_third_sld r hr]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    norm_num
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
  unfold buresDesignCriterion
  rw [hinv,Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')]
  norm_num

/-- Global Bures design optimality of the limit reached by the implemented
P1 controller, against all regular finite qubit POVMs in Bloch coordinates. -/
theorem mixedBuresTarget_optimal_over_finite_qubitPOVM
    (r : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    {O : Type} [Fintype O] (P : QubitBlochPOVM O)
    (hP : (qubitClassicalFisher r P).PosDef) :
    buresDesignCriterion r (mixedBuresTarget r) ≤
      buresDesignCriterion r (qubitClassicalFisher r P) := by
  rw [mixedBuresTarget_bures_value r hr]
  exact finite_qubitPOVM_bures_lower_bound r hr P hP

end
end QubitOracle.AdaptiveDesign.P1
