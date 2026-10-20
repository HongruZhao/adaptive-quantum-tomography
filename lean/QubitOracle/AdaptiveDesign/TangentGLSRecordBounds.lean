import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProtectedGLSWeightBounds
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.PureStateFoundations
/-! The analytic bounds specialized to the Born records of the implemented
estimator. In particular, fitting on the same records is allowed throughout. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {d n : ℕ} {O : Type} [Fintype O]

theorem fittedProbability_nonneg (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : 0 ≤ fittedProbability h data r := by
  rw [fittedProbability_eq_Born]
  have hb := ((data r.1).measurement.positive r.2).dotProduct_mulVec_nonneg h.val
  simpa [GlobalPFSIC.quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using (Complex.nonneg_iff.mp hb).1

theorem fittedProbability_sum (h : PureVector d) (data : Fin n → Record d O)
    (t : Fin n) : ∑ y, fittedProbability h data (t,y) = 1 := by
  simp only [fittedProbability, inner_eq_trace]
  change (∑ y, (Matrix.trace (rankOneDensity h.val * (data t).measurement.effect y)).re) = 1
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
    (data t).measurement.complete, Matrix.mul_one, rankOneDensity_trace_eq_one _ h.property]
  rfl

theorem fittedProbability_le_one (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : fittedProbability h data r ≤ 1 := by
  have hb := Finset.single_le_sum (fun y _ => fittedProbability_nonneg h data (r.1,y))
    (Finset.mem_univ r.2)
  simpa only [fittedProbability_sum] using hb

theorem observedIndicator_mem (data : Fin n → Record d O) (r : Fin n × O) :
    0 ≤ observedIndicator data r ∧ observedIndicator data r ≤ 1 := by
  classical
  unfold observedIndicator
  split_ifs <;> norm_num

theorem record_noise_abs_le (truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : |observedIndicator data r - fittedProbability truth data r| ≤ 1 := by
  have ho := observedIndicator_mem data r
  have hp := fittedProbability_nonneg truth data r
  have hq := fittedProbability_le_one truth data r
  rw [abs_le]
  constructor <;> linarith

theorem record_increment_abs_le_one (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : |fittedProbability h data r - fittedProbability truth data r| ≤ 1 := by
  have hp := fittedProbability_nonneg truth data r
  have hq := fittedProbability_le_one truth data r
  have hr := fittedProbability_nonneg h data r
  have hs := fittedProbability_le_one h data r
  rw [abs_le]
  constructor <;> linarith

theorem record_increment_eq (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) :
    fittedProbability h data r - fittedProbability truth data r =
      ⟪recordFeature data r,
        (P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val⟫_ℝ := by
  rw [inner_sub_right]
  rfl

theorem record_increment_bound (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) (C : ℝ) (hC : ‖recordFeature data r‖ ≤ C) :
    |fittedProbability h data r - fittedProbability truth data r| ≤
      C * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ := by
  rw [record_increment_eq]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

theorem record_curvature_eq (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) :
    fittedProbability h data r - fittedProbability truth data r -
        ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ =
      ⟪recordFeature data r,
        ((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val) -
          (preliminaryTangentError h truth).val⟫_ℝ := by
  rw [inner_sub_right, record_increment_eq, tangentFeature,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

theorem record_curvature_bound (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) (C : ℝ) (hC : ‖recordFeature data r‖ ≤ C) :
    |fittedProbability h data r - fittedProbability truth data r -
        ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ| ≤
      3*C * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2 := by
  rw [record_curvature_eq]
  calc
    _ ≤ ‖recordFeature data r‖ * ‖((P2Adaptive.pureParameter d h).val -
        (P2Adaptive.pureParameter d truth).val) - (preliminaryTangentError h truth).val‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ C * (3 * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2) :=
      mul_le_mul hC (preliminaryError_normal_bound h truth) (norm_nonneg _)
        ((norm_nonneg _).trans hC)
    _ = _ := by ring

theorem tangentFeature_norm_le (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : ‖tangentFeature h data r‖ ≤ ‖recordFeature data r‖ :=
  (tangentSpace h).norm_orthogonalProjectionOnto_apply_le _

theorem record_tangent_error_inner_bound (h truth : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) (C : ℝ) (hC : ‖recordFeature data r‖ ≤ C) :
    |⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ| ≤ 2*C := by
  have he := (preliminaryTangentError_norm_le h truth).trans (preliminaryError_norm_le_two h truth)
  have hf := (tangentFeature_norm_le h data r).trans hC
  exact (abs_real_inner_le_norm _ _).trans (by
    simpa only [mul_comm] using mul_le_mul hf he (norm_nonneg _) ((norm_nonneg _).trans hC))

def regularRemainderConstant (floor C : ℝ) : ℝ :=
  C * (3*C/floor^2 + C^2/floor^3 + 3*C/floor)

def clippedRemainderConstant (floor C : ℝ) : ℝ :=
  C * ((2*C+1)/floor^2 + 1/floor^3 + (1+2*C)/floor)

theorem record_regular_remainder_bound
    (h truth : PureVector d) (data : Fin n → Record d O) (r : Fin n × O)
    (floor C : ℝ) (hf : 0 < floor) (hC : ‖recordFeature data r‖ ≤ C)
    (hp : floor ≤ fittedProbability truth data r) (hq : floor ≤ fittedProbability h data r) :
    ‖remainderCoefficient floor (fittedProbability truth data r) (fittedProbability h data r)
      (observedIndicator data r) ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ •
        tangentFeature h data r‖ ≤
      regularRemainderConstant floor C *
        ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2 := by
  have hC0 := (norm_nonneg _).trans hC
  have hb := remainderCoefficient_regular_bound floor _ _ _ _ _ _ hf hp hq
    (record_noise_abs_le truth data r) (record_increment_bound h truth data r C hC)
    (record_curvature_bound h truth data r C hC)
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ ((3*C*‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2)/floor^2 +
        (C*‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖)^2/floor^3 +
        (3*C*‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2)/floor) * C :=
      mul_le_mul hb ((tangentFeature_norm_le h data r).trans hC) (norm_nonneg _)
        (by positivity)
    _ = _ := by unfold regularRemainderConstant; ring

theorem record_global_remainder_bound
    (h truth : PureVector d) (data : Fin n → Record d O) (r : Fin n × O)
    (floor C : ℝ) (hf : 0 < floor) (hC : ‖recordFeature data r‖ ≤ C) :
    ‖remainderCoefficient floor (fittedProbability truth data r) (fittedProbability h data r)
      (observedIndicator data r) ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ •
        tangentFeature h data r‖ ≤ clippedRemainderConstant floor C := by
  have hC0 := (norm_nonneg _).trans hC
  have hb := remainderCoefficient_global_bound floor _ _ _ _ _ hf
    (record_noise_abs_le truth data r) (record_increment_abs_le_one h truth data r)
    (record_tangent_error_inner_bound h truth data r C hC)
  rw [norm_smul, Real.norm_eq_abs]
  unfold clippedRemainderConstant
  rw [mul_comm C]
  exact mul_le_mul hb ((tangentFeature_norm_le h data r).trans hC) (norm_nonneg _) (by positivity)

def badRowCount (truth : PureVector d) (data : Fin n → Record d O) (floor : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r => fittedProbability truth data r < 2*floor)).card

/-- A uniform bound after inserting an arbitrary preliminary estimate.
The bad-row count uses true probabilities, so its asymptotic control is
proved from the held controller rather than from fitted-weight predictability. -/
theorem record_remainder_bound_if_close
    (h truth : PureVector d) (data : Fin n → Record d O)
    (floor C : ℝ) (hf : 0 < floor) (hC0 : 0 ≤ C)
    (hC : ∀ r, ‖recordFeature data r‖ ≤ C)
    (hclose : C * ‖(P2Adaptive.pureParameter d h).val -
      (P2Adaptive.pureParameter d truth).val‖ ≤ floor) :
    ‖fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
      (fittedProbability h data) (observedIndicator data) floor (preliminaryTangentError h truth)‖ ≤
    ((n * Fintype.card O : ℕ) : ℝ) * regularRemainderConstant floor C *
        ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2 +
      (badRowCount truth data floor : ℝ) * clippedRemainderConstant floor C := by
  classical
  let a := regularRemainderConstant floor C *
    ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖^2
  let b := clippedRemainderConstant floor C
  have ha : 0 ≤ a := by dsimp [a, regularRemainderConstant]; positivity
  have hb : 0 ≤ b := by dsimp [b, clippedRemainderConstant]; positivity
  have hrow (r : Fin n × O) :
      ‖remainderCoefficient floor (fittedProbability truth data r) (fittedProbability h data r)
        (observedIndicator data r) ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ •
          tangentFeature h data r‖ ≤
      a + if fittedProbability truth data r < 2*floor then b else 0 := by
    by_cases hbad : fittedProbability truth data r < 2*floor
    · rw [if_pos hbad]
      have hr := record_global_remainder_bound h truth data r floor C hf (hC r)
      exact hr.trans (by dsimp [b] at *; linarith)
    · rw [if_neg hbad, add_zero]
      have hp : floor ≤ fittedProbability truth data r := by linarith [le_of_not_gt hbad]
      have hinc := (record_increment_bound h truth data r C (hC r)).trans hclose
      have hq : floor ≤ fittedProbability h data r := by
        have hi := (abs_le.mp hinc).1
        linarith [le_of_not_gt hbad]
      exact record_regular_remainder_bound h truth data r floor C hf (hC r) hp hq
  rw [fittedWeightRemainder_eq_sum]
  calc
    _ ≤ ∑ r, ‖remainderCoefficient floor (fittedProbability truth data r) (fittedProbability h data r)
      (observedIndicator data r) ⟪tangentFeature h data r, preliminaryTangentError h truth⟫_ℝ •
        tangentFeature h data r‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin n × O, (a + if fittedProbability truth data r < 2*floor then b else 0) :=
      Finset.sum_le_sum (fun r _ => hrow r)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
      dsimp [badRowCount, a, b]
      ring

theorem record_normalMap_coercive
    (h : PureVector d) (data : Fin n → Record d O) (floor ridge κ : ℝ)
    (hf : 0 < floor) (hf1 : floor ≤ 1)
    (hframe : ∀ t : Fin n, ∀ x : HermitianSpace (d+1),
      κ * ‖x‖^2 ≤ ∑ y, ⟪recordFeature data (t,y), x⟫_ℝ^2) :
    CoerciveLeastSquares.Coercive
      (normalMap (tangentFeature h data)
        (fun r => (denominator floor (fittedProbability h data r))⁻¹) ridge)
      (ridge + (n : ℝ)*κ) := by
  intro x
  rw [normalMap_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, gram_quadratic]
  have hw (r : Fin n × O) : 1 ≤ (denominator floor (fittedProbability h data r))⁻¹ := by
    apply (one_le_inv₀ (denominator_pos hf _)).mpr
    exact max_le (fittedProbability_le_one h data r) hf1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    mul_le_mul_of_nonneg_right (hw r) (sq_nonneg ⟪tangentFeature h data r,x⟫_ℝ))
  simp only [one_mul] at hsum
  have hbase : (n : ℝ)*κ*‖x‖^2 ≤ ∑ r : Fin n × O, ⟪tangentFeature h data r,x⟫_ℝ^2 := by
    simp only [Fintype.sum_prod_type, tangentFeature,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hframe t x.val)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    change (n : ℝ) * (κ * ‖x‖^2) ≤ _ at hs
    simpa only [mul_assoc] using hs
  nlinarith

end
end QubitOracle.AdaptiveDesign.TangentGLS
