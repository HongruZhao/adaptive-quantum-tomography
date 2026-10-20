import QubitOracle.AdaptiveDesign.FiniteAdaptiveOracle
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Arbitrary positive-semidefinite loss matrices

The canonical positive square root is Mathlib's continuous functional
calculus. B is an invertible information-whitening matrix and U its inverse.
Taking B = H^(-1/2) gives the paper's coordinate-invariant Gill--Massar
constant. No restriction to isotropic, Bures, or Frobenius weights is made.
-/

namespace QubitOracle.AdaptiveDesign.FiniteRegularOracle

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

namespace RegularModel

def information (P : RegularModel ι Ω) : Matrix ι ι ℝ :=
  ∑ w, P.mass P.theta w • Matrix.vecMulVec (P.score w) (P.score w)

def quadraticRisk (P : RegularModel ι Ω) (W : Matrix ι ι ℝ) (T : Ω → ι → ℝ) : ℝ :=
  P.expectation (fun w => (T w - P.theta) ⬝ᵥ (W *ᵥ (T w - P.theta)))

theorem factorRisk_eq_quadraticRisk (P : RegularModel ι Ω)
    (R : Matrix ι ι ℝ) (T : Ω → ι → ℝ) :
    P.factorRisk R T = P.quadraticRisk (R.transpose * R) T := by
  unfold factorRisk quadraticRisk expectation
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  dsimp only
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, pow_two]

theorem scoreEnergy_eq_information_trace (P : RegularModel ι Ω)
    (B : Matrix ι ι ℝ) :
    P.scoreEnergy B = Matrix.trace ((B.transpose * B) * P.information) := by
  simp only [information, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    scoreEnergy, expectation]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  simp only [dotProduct, Matrix.mulVec, pow_two]

/-- Sharp general weighted lower bound, with all probabilities, derivatives,
unbiasedness conditions, and the information budget explicitly exposed. -/
theorem general_weighted_oracle (P : RegularModel ι Ω)
    (W B U : Matrix ι ι ℝ) (hW : W.PosSemidef)
    (hBU : B * U = 1) (hUB : U * B = 1)
    (T : Ω → ι → ℝ) (hT : P.LocallyUnbiased T)
    (n budget : ℝ) (hbudget : 0 < budget)
    (hInfo : Matrix.trace ((B.transpose * B) * P.information) ≤ n * budget) :
    (Matrix.trace (CFC.sqrt (B * W * B.transpose)))^2 / budget ≤
      n * P.quadraticRisk W T := by
  let A := B * W * B.transpose
  let C := CFC.sqrt A
  have hA : A.PosSemidef := by
    simpa only [A, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hW.mul_mul_conjTranspose_same B
  have hC : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hCsym : C.transpose = C := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  have hCsq : C * C = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  let R := C * U.transpose
  have hR : R.transpose * R = W := by
    dsimp only [R]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hCsym]
    calc
      _ = U * (C * C) * U.transpose := by noncomm_ring
      _ = U * (B * W * B.transpose) * U.transpose := by rw [hCsq]
      _ = (U * B) * W * (U * B).transpose := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = W := by rw [hUB]; simp
  have hcross : R * B.transpose = C := by
    dsimp only [R]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hBU]
    simp
  have h := P.oracle_bound_of_information_budget R B T hT n budget hbudget
    (by rwa [P.scoreEnergy_eq_information_trace])
  rw [hcross, P.factorRisk_eq_quadraticRisk, hR] at h
  exact h

end RegularModel

/-- The general oracle theorem for the full adaptive record. The one-copy
budget is summed by the proved chain rule, not postulated for the joint law. -/
theorem general_adaptive_oracle {Y : Type} [Fintype Y]
    (theta : ι → ℝ) (step : List Y → AtTruth theta Y)
    (W B U : Matrix ι ι ℝ) (hW : W.PosSemidef)
    (hBU : B * U = 1) (hUB : U * B = 1)
    (budget : ℝ) (hbudget : 0 < budget)
    (hstep : ∀ history, Matrix.trace ((B.transpose * B) *
      (step history).val.information) ≤ budget)
    (n : ℕ) (T : Record Y n → ι → ℝ)
    (hT : (adaptiveExperiment theta step n []).val.LocallyUnbiased T) :
    (Matrix.trace (CFC.sqrt (B * W * B.transpose)))^2 / budget ≤
      (n : ℝ) * (adaptiveExperiment theta step n []).val.quadraticRisk W T := by
  apply RegularModel.general_weighted_oracle _ W B U hW hBU hUB T hT n budget hbudget
  rw [← RegularModel.scoreEnergy_eq_information_trace]
  apply adaptive_scoreEnergy_le
  intro history
  rw [RegularModel.scoreEnergy_eq_information_trace]
  exact hstep history

/-- The exact coordinate form of the benchmark in Theorem 5.5. -/
def oracleConstant (W H : Matrix ι ι ℝ) (budget : ℝ) : ℝ :=
  (Matrix.trace (CFC.sqrt (CFC.sqrt (H⁻¹) * W * CFC.sqrt (H⁻¹))))^2 / budget

/-- Theorem 5.5 with canonical quantum-information whitening. Positivity
of H supplies both inverse square roots and their inverse identities;
there are no extra whitening-factor assumptions in this endpoint. -/
theorem general_adaptive_oracle_qfi {Y : Type} [Fintype Y]
    (theta : ι → ℝ) (step : List Y → AtTruth theta Y)
    (W H : Matrix ι ι ℝ) (hW : W.PosSemidef) (hH : H.PosDef)
    (budget : ℝ) (hbudget : 0 < budget)
    (hstep : ∀ history, Matrix.trace (H⁻¹ * (step history).val.information) ≤ budget)
    (n : ℕ) (T : Record Y n → ι → ℝ)
    (hT : (adaptiveExperiment theta step n []).val.LocallyUnbiased T) :
    oracleConstant W H budget ≤
      (n : ℝ) * (adaptiveExperiment theta step n []).val.quadraticRisk W T := by
  let B := CFC.sqrt (H⁻¹)
  have hBpos : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (H⁻¹))
  have hBsym : B.transpose = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hBpos.isHermitian.eq
  have hBB : B * B = H⁻¹ := CFC.sqrt_mul_sqrt_self (H⁻¹) hH.inv.posSemidef.nonneg
  have hd : B.det * B.det = (H⁻¹).det := by rw [← Matrix.det_mul, hBB]
  have hu : IsUnit B.det := by
    have hh : IsUnit (B.det * B.det) := hd.symm ▸
      (Matrix.isUnit_iff_isUnit_det (H⁻¹)).mp hH.inv.isUnit
    exact isUnit_iff_ne_zero.mpr (fun hz => hh.ne_zero (by simp [hz]))
  have h := general_adaptive_oracle theta step W B B⁻¹ hW
    (Matrix.mul_nonsing_inv B hu) (Matrix.nonsing_inv_mul B hu)
    budget hbudget (by intro history; simpa only [hBsym, hBB] using hstep history)
    n T hT
  simpa only [hBsym, B, oracleConstant] using h

end
end QubitOracle.AdaptiveDesign.FiniteRegularOracle
