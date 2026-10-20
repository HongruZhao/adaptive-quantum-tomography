import Mathlib
import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
/-!
# A finite identifying frame is uniformly coercive

Only finite-dimensional real inner-product geometry is used.  A separating
finite collection of effects has a strictly positive least-squares frame
constant. Isometric transport preserves the same constant, even when the
transport changes predictably after every batch.
-/
namespace QubitOracle.AdaptiveDesign.FiniteFrameCoercivity

open scoped BigOperators InnerProductSpace
noncomputable section

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]

/-- All real linear measurement coordinates of the proposed frame. -/
def analysisMap (v : ι → E) : E →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => ⟪v i, x⟫_ℝ)
  map_add' x y := by ext i; simp [inner_add_right]
  map_smul' c x := by ext i; simp [inner_smul_right]

@[simp] theorem analysisMap_apply (v : ι → E) (x : E) (i : ι) :
    analysisMap v x i = ⟪v i, x⟫_ℝ := rfl

/-- Unweighted least-squares frame operator. -/
def frameOperator (v : ι → E) : E →ₗ[ℝ] E where
  toFun x := ∑ i, ⟪v i, x⟫_ℝ • v i
  map_add' x y := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [inner_smul_right, mul_smul, Finset.smul_sum]

@[simp] theorem frameOperator_apply (v : ι → E) (x : E) :
    frameOperator v x = ∑ i, ⟪v i, x⟫_ℝ • v i := rfl

theorem frameOperator_quadratic (v : ι → E) (x : E) :
    ⟪x, frameOperator v x⟫_ℝ = ∑ i, ⟪v i, x⟫_ℝ ^ 2 := by
  simp [frameOperator, inner_sum, inner_smul_right, real_inner_comm, pow_two]

theorem analysisMap_norm_sq (v : ι → E) (x : E) :
    ‖analysisMap v x‖ ^ 2 = ∑ i, ⟪v i, x⟫_ℝ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Separation of zero suffices; no spanning witness has to be supplied. -/
theorem analysisMap_injective_of_separating (v : ι → E)
    (hsep : ∀ x : E, (∀ i, ⟪v i, x⟫_ℝ = 0) → x = 0) :
    Function.Injective (analysisMap v) := by
  apply (LinearMap.ker_eq_bot).1
  apply LinearMap.ker_eq_bot'.2
  intro x hx
  apply hsep x
  intro i
  have hh := congrArg (fun y : EuclideanSpace ℝ ι => y i) hx
  simpa using hh

/-- Finite-dimensional injectivity supplies a positive constant for the
quadratic frame bound. This is proved, not an oracle field. -/
theorem exists_positive_coercivity_of_injective [FiniteDimensional ℝ E]
    (v : ι → E) (hinj : Function.Injective (analysisMap v)) :
    ∃ κ : ℝ, 0 < κ ∧ CoerciveLeastSquares.Coercive (frameOperator v) κ := by
  obtain ⟨K, hK, hbound⟩ := (analysisMap v).injective_iff_antilipschitz.1 hinj
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨((K : ℝ) ^ 2)⁻¹, by positivity, ?_⟩
  intro x
  have hn : ‖x‖ ≤ (K : ℝ) * ‖analysisMap v x‖ := by
    simpa only [dist_zero_right, map_zero] using hbound.le_mul_dist x 0
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hn 2
  rw [mul_pow] at hsq
  rw [frameOperator_quadratic, ← analysisMap_norm_sq]
  have hKsq : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hKr
  calc
    ((K : ℝ) ^ 2)⁻¹ * ‖x‖ ^ 2 ≤
        ((K : ℝ) ^ 2)⁻¹ * ((K : ℝ) ^ 2 * ‖analysisMap v x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 hKsq.le)
    _ = ‖analysisMap v x‖ ^ 2 := by field_simp

theorem exists_positive_coercivity_of_separating [FiniteDimensional ℝ E]
    (v : ι → E) (hsep : ∀ x : E, (∀ i, ⟪v i, x⟫_ℝ = 0) → x = 0) :
    ∃ κ : ℝ, 0 < κ ∧ CoerciveLeastSquares.Coercive (frameOperator v) κ :=
  exists_positive_coercivity_of_injective v (analysisMap_injective_of_separating v hsep)

/-- Inner products with transported effects equal the original measurement
coordinates of the inversely transported state. -/
theorem transported_measurement (U : E ≃ₗᵢ[ℝ] F) (v : E) (x : F) :
    ⟪U v, x⟫_ℝ = ⟪v, U.symm x⟫_ℝ := by
  simpa only [U.apply_symm_apply] using U.inner_map_map v (U.symm x)

theorem frameOperator_transport_quadratic (U : E ≃ₗᵢ[ℝ] F)
    (v : ι → E) (x : F) :
    ⟪x, frameOperator (fun i => U (v i)) x⟫_ℝ =
      ⟪U.symm x, frameOperator v (U.symm x)⟫_ℝ := by
  simp only [frameOperator_quadratic, transported_measurement]

/-- A changing unitary/orthogonal frame has the *same* coercivity constant. -/
theorem coercivity_preserved_by_isometry (U : E ≃ₗᵢ[ℝ] F)
    (v : ι → E) (κ : ℝ)
    (hv : CoerciveLeastSquares.Coercive (frameOperator v) κ) :
    CoerciveLeastSquares.Coercive (frameOperator (fun i => U (v i))) κ := by
  intro x
  rw [frameOperator_transport_quadratic]
  simpa only [U.symm.norm_map] using hv (U.symm x)

/-- Once the reference POVM identifies the real state coordinates, every
isometric transport satisfies a common deterministic lower frame bound. -/
theorem exists_uniform_transport_coercivity [FiniteDimensional ℝ E]
    (v : ι → E) (hinj : Function.Injective (analysisMap v)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ U : E ≃ₗᵢ[ℝ] F,
      CoerciveLeastSquares.Coercive (frameOperator (fun i => U (v i))) κ := by
  obtain ⟨κ, hκ, hv⟩ := exists_positive_coercivity_of_injective v hinj
  exact ⟨κ, hκ, fun U => coercivity_preserved_by_isometry U v κ hv⟩

/-- Coordinatewise probability injectivity is exactly the condition needed
by the analysis map; the Euclidean wrapper adds no assumption. -/
theorem analysisMap_injective_iff (v : ι → E) :
    Function.Injective (analysisMap v) ↔
      Function.Injective (fun x : E => fun i => ⟪v i, x⟫_ℝ) := by
  constructor
  · intro hinj x y hxy
    apply hinj
    ext i
    exact congrFun hxy i
  · intro hinj x y hxy
    apply hinj
    funext i
    exact congrArg (fun z : EuclideanSpace ℝ ι => z i) hxy

end
end QubitOracle.AdaptiveDesign.FiniteFrameCoercivity
