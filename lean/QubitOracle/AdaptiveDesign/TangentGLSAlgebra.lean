import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The finite-record tangent GLS solve

The real Hilbert space `E` can be the pure-state tangent space. Every fitted
probability is protected by a strictly positive known floor. The correction
is an actual inverse linear solve, not a supplied solution or efficiency
certificate. The normal equation, uniqueness, and error cancellation are
proved for every finite record.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open Filter
open scoped BigOperators Topology InnerProductSpace
noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype R]

def denominator (floor : ℝ) (q : ℝ) : ℝ := max q floor

theorem denominator_pos {floor : ℝ} (hf : 0 < floor) (q : ℝ) :
    0 < denominator floor q := lt_of_lt_of_le hf (le_max_right _ _)

def gram (feature : R → E) (weight : R → ℝ) : E →ₗ[ℝ] E where
  toFun x := ∑ r, (weight r * ⟪feature r, x⟫_ℝ) • feature r
  map_add' x y := by
    simp [inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [inner_smul_right, mul_smul, Finset.smul_sum, mul_comm, mul_left_comm]

@[simp] theorem gram_apply (feature : R → E) (weight : R → ℝ) (x : E) :
    gram feature weight x = ∑ r, (weight r * ⟪feature r, x⟫_ℝ) • feature r := rfl

theorem gram_quadratic (feature : R → E) (weight : R → ℝ) (x : E) :
    ⟪x, gram feature weight x⟫_ℝ =
      ∑ r, weight r * ⟪feature r, x⟫_ℝ ^ 2 := by
  simp [gram, inner_sum, inner_smul_right, real_inner_comm, pow_two, mul_assoc]

def score (feature : R → E) (weight residual : R → ℝ) : E :=
  ∑ r, (weight r * residual r) • feature r

def normalMap (feature : R → E) (weight : R → ℝ) (ridge : ℝ) : E →ₗ[ℝ] E :=
  ridge • LinearMap.id + gram feature weight

@[simp] theorem normalMap_apply (feature : R → E) (weight : R → ℝ)
    (ridge : ℝ) (x : E) : normalMap feature weight ridge x =
      ridge • x + gram feature weight x := rfl

theorem normalMap_coercive (feature : R → E) (weight : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) :
    CoerciveLeastSquares.Coercive (normalMap feature weight ridge) ridge := by
  intro x
  rw [normalMap_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, gram_quadratic]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun r _ =>
    mul_nonneg (hw r) (sq_nonneg _))

def normalEquiv (feature : R → E) (weight : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo (normalMap feature weight ridge)
    (CoerciveLeastSquares.injective_of_coercive _ ridge hr
      (normalMap_coercive feature weight hw ridge))

def correction (feature : R → E) (weight residual : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge) : E :=
  (normalEquiv feature weight hw ridge hr).symm (score feature weight residual)

theorem correction_normalEquation (feature : R → E) (weight residual : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge) :
    normalMap feature weight ridge (correction feature weight residual hw ridge hr) =
      score feature weight residual :=
  (normalEquiv feature weight hw ridge hr).apply_symm_apply _

theorem correction_unique (feature : R → E) (weight residual : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge) (x : E)
    (hx : normalMap feature weight ridge x = score feature weight residual) :
    x = correction feature weight residual hw ridge hr :=
  (normalEquiv feature weight hw ridge hr).injective
    (hx.trans (correction_normalEquation feature weight residual hw ridge hr).symm)

def fittedCorrection (feature : R → E) (q residual : R → ℝ)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) : E :=
  correction feature (fun r => (denominator floor (q r))⁻¹) residual
    (fun r => (inv_pos.mpr (denominator_pos hf (q r))).le) ridge hr

/-- The quadratic criterion in the paper, expressed in any real tangent
Hilbert space. It contains exactly the protected inverse-probability weights. -/
def objective (feature : R → E) (weight residual : R → ℝ) (ridge : ℝ) (x : E) : ℝ :=
  ridge / 2 * ‖x‖ ^ 2 +
    (∑ r, weight r * (residual r - ⟪feature r, x⟫_ℝ) ^ 2) / 2

theorem objective_expansion (feature : R → E) (weight residual : R → ℝ)
    (ridge : ℝ) (x z : E) :
    objective feature weight residual ridge (x + z) -
        objective feature weight residual ridge x =
      ⟪z, normalMap feature weight ridge x - score feature weight residual⟫_ℝ +
        ⟪z, normalMap feature weight ridge z⟫_ℝ / 2 := by
  have hsum : (∑ r, weight r * (residual r - ⟪feature r, x + z⟫_ℝ) ^ 2) -
      (∑ r, weight r * (residual r - ⟪feature r, x⟫_ℝ) ^ 2) =
      2 * (∑ r, weight r * ⟪feature r, z⟫_ℝ *
        (⟪feature r, x⟫_ℝ - residual r)) +
        ∑ r, weight r * ⟪feature r, z⟫_ℝ ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [inner_add_right]
    ring
  have hcross : ⟪z, gram feature weight x - score feature weight residual⟫_ℝ =
      ∑ r, weight r * ⟪feature r, z⟫_ℝ *
        (⟪feature r, x⟫_ℝ - residual r) := by
    simp only [inner_sub_right, gram_apply, score, inner_sum, inner_smul_right,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [real_inner_comm z (feature r)]
    ring
  have hnormalCross : ⟪z, normalMap feature weight ridge x -
      score feature weight residual⟫_ℝ = ridge * ⟪z, x⟫_ℝ +
      ∑ r, weight r * ⟪feature r, z⟫_ℝ *
        (⟪feature r, x⟫_ℝ - residual r) := by
    rw [normalMap_apply, show ridge • x + gram feature weight x -
        score feature weight residual =
        ridge • x + (gram feature weight x - score feature weight residual) by abel,
      inner_add_right, inner_smul_right, hcross]
  rw [objective, objective, norm_add_sq_real, hnormalCross]
  rw [normalMap_apply, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, gram_quadratic]
  rw [real_inner_comm x z]
  linarith

theorem correction_minimizes (feature : R → E) (weight residual : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge) (x : E) :
    objective feature weight residual ridge
      (correction feature weight residual hw ridge hr) ≤
        objective feature weight residual ridge x := by
  let c := correction feature weight residual hw ridge hr
  have h := objective_expansion feature weight residual ridge c (x - c)
  have hn : normalMap feature weight ridge c = score feature weight residual :=
    correction_normalEquation feature weight residual hw ridge hr
  rw [add_sub_cancel, hn, sub_self, inner_zero_right, zero_add] at h
  have hpos := normalMap_coercive feature weight hw ridge (x - c)
  have hnonneg : 0 ≤ ⟪x - c, normalMap feature weight ridge (x - c)⟫_ℝ :=
    (mul_nonneg hr.le (sq_nonneg _)).trans hpos
  linarith

/-- Exact cancellation identity behind the explanation in the paper.
The Taylor remainder is an explicit vector; its asymptotic control is a
separate theorem, not an assumed efficiency conclusion. -/
theorem correction_error_cancellation
    (feature : R → E) (weight residual : R → ℝ)
    (hw : ∀ r, 0 ≤ weight r) (ridge : ℝ) (hr : 0 < ridge)
    (preliminaryError trueScore remainder : E)
    (hexpansion : score feature weight residual =
      trueScore - normalMap feature weight ridge preliminaryError + remainder) :
    correction feature weight residual hw ridge hr = -preliminaryError +
      (normalEquiv feature weight hw ridge hr).symm trueScore +
      (normalEquiv feature weight hw ridge hr).symm remainder := by
  unfold correction
  rw [hexpansion, map_add, map_sub]
  have hc : (normalEquiv feature weight hw ridge hr).symm
      (normalMap feature weight ridge preliminaryError) = preliminaryError :=
    (normalEquiv feature weight hw ridge hr).symm_apply_apply preliminaryError
  rw [hc]
  abel

end
end QubitOracle.AdaptiveDesign.TangentGLS
