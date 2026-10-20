import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
/-!
# Same-record fitted-weight expansion

These are exact finite-sample identities. They apply after computing the
preliminary estimate from those same records. No predictability of the fitted
weights is assumed. The remainder separates clipping, nonlinear geometry,
and the quadratic reciprocal-weight term; its stochastic rate is a separate
obligation, not a hidden hypothesis of these identities.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open scoped BigOperators InnerProductSpace
noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype R]

theorem reciprocal_exact_expansion (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    q⁻¹ = p⁻¹ - (q-p) / p^2 + (q-p)^2 / (p^2*q) := by
  field_simp
  ring

def noiseDerivative (feature : R → E) (p observed : R → ℝ) (floor : ℝ) : E →ₗ[ℝ] E :=
  -gram feature (fun r => (observed r - p r) / denominator floor (p r)^2)

def fittedWeightRemainder (feature : R → E) (p q observed : R → ℝ)
    (floor : ℝ) (preliminaryError : E) : E :=
  ∑ r,
    ((observed r - p r) *
      (⟪feature r, preliminaryError⟫_ℝ -
        (denominator floor (q r) - denominator floor (p r))) /
          denominator floor (p r)^2 +
      (observed r - p r) *
        (denominator floor (q r) - denominator floor (p r))^2 /
          (denominator floor (p r)^2 * denominator floor (q r)) -
      (q r - p r - ⟪feature r, preliminaryError⟫_ℝ) / denominator floor (q r)) • feature r

/-- Exact score expansion with the all-data fitted weights. Curvature and
clipping errors are explicitly displayed in `fittedWeightRemainder`. -/
theorem fittedScore_exact_expansion (feature : R → E) (p q observed : R → ℝ)
    (floor : ℝ) (hf : 0 < floor) (preliminaryError : E) :
    score feature (fun r => (denominator floor (q r))⁻¹) (fun r => observed r - q r) =
      score feature (fun r => (denominator floor (p r))⁻¹) (fun r => observed r - p r) -
      gram feature (fun r => (denominator floor (q r))⁻¹) preliminaryError +
      noiseDerivative feature p observed floor preliminaryError +
      fittedWeightRemainder feature p q observed floor preliminaryError := by
  simp only [score, gram_apply, noiseDerivative, LinearMap.neg_apply,
    fittedWeightRemainder, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← sub_smul, ← neg_smul, ← add_smul, ← add_smul]
  congr 1
  have hp := (denominator_pos hf (p r)).ne'
  have hq := (denominator_pos hf (q r)).ne'
  field_simp
  ring

theorem fittedCorrection_exact_cancellation
    (feature : R → E) (p q observed : R → ℝ)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) (preliminaryError : E) :
    fittedCorrection feature q (fun r => observed r - q r) floor ridge hf hr =
      -preliminaryError +
      (normalEquiv feature (fun r => (denominator floor (q r))⁻¹)
        (fun r => (inv_pos.mpr (denominator_pos hf (q r))).le) ridge hr).symm
        (score feature (fun r => (denominator floor (p r))⁻¹) (fun r => observed r - p r)) +
      (normalEquiv feature (fun r => (denominator floor (q r))⁻¹)
        (fun r => (inv_pos.mpr (denominator_pos hf (q r))).le) ridge hr).symm
        (noiseDerivative feature p observed floor preliminaryError +
          fittedWeightRemainder feature p q observed floor preliminaryError + ridge • preliminaryError) := by
  apply correction_error_cancellation
  rw [fittedScore_exact_expansion feature p q observed floor hf preliminaryError, normalMap_apply]
  abel

open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController

def preliminaryTangentError {d : ℕ} (h truth : PureVector d) : tangentSpace h :=
  (tangentSpace h).orthogonalProjectionOnto
    ((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val)

theorem recordCorrection_exact_cancellation {d n : ℕ} {O : Type} [Fintype O]
    (h truth : PureVector d) (data : Fin n → Record d O)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    recordCorrection h data floor ridge hf hr =
      -preliminaryTangentError h truth +
      (normalEquiv (tangentFeature h data)
        (fun r => (denominator floor (fittedProbability h data r))⁻¹)
        (fun r => (inv_pos.mpr (denominator_pos hf (fittedProbability h data r))).le) ridge hr).symm
        (score (tangentFeature h data)
          (fun r => (denominator floor (fittedProbability truth data r))⁻¹)
          (fun r => observedIndicator data r - fittedProbability truth data r)) +
      (normalEquiv (tangentFeature h data)
        (fun r => (denominator floor (fittedProbability h data r))⁻¹)
        (fun r => (inv_pos.mpr (denominator_pos hf (fittedProbability h data r))).le) ridge hr).symm
        (noiseDerivative (tangentFeature h data) (fittedProbability truth data) (observedIndicator data) floor
            (preliminaryTangentError h truth) +
          fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
            (fittedProbability h data) (observedIndicator data) floor (preliminaryTangentError h truth) +
          ridge • preliminaryTangentError h truth) := by
  exact fittedCorrection_exact_cancellation (tangentFeature h data)
    (fittedProbability truth data) (fittedProbability h data) (observedIndicator data)
    floor ridge hf hr (preliminaryTangentError h truth)

end
end QubitOracle.AdaptiveDesign.TangentGLS
