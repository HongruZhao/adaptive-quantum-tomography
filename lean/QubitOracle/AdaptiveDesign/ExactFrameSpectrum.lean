import QubitOracle.AdaptiveDesign.FiniteFrameCoercivity

/-! The exact least-eigenvalue constant in the uniform-frame lemma.
The constant is the infimum of the Rayleigh quotient; it is proved to
be an eigenvalue and no larger than any other eigenvalue. -/
namespace QubitOracle.AdaptiveDesign.ExactFrameSpectrum
open FiniteFrameCoercivity Module.End
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E F O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype O]

theorem frame_symmetric (v : O → E) : (frameOperator v).IsSymmetric := by
  intro x y
  simp [frameOperator,inner_sum,sum_inner,inner_smul_left,inner_smul_right,real_inner_comm]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem frame_quadratic_nonnegative (v : O → E) (x : E) :
    0 ≤ ⟪x,frameOperator v x⟫_ℝ := by
  rw [frameOperator_quadratic]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def leastEigenvalue (v : O → E) : ℝ :=
  ⨅ x : {x : E // x ≠ 0}, ⟪frameOperator v x.val,x.val⟫_ℝ / ‖x.val‖^2

theorem rayleigh_bddBelow (v : O → E) :
    BddBelow (Set.range (fun x : {x : E // x ≠ 0} =>
      ⟪frameOperator v x.val,x.val⟫_ℝ / ‖x.val‖^2)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨x,rfl⟩
  dsimp only
  rw [real_inner_comm]
  exact div_nonneg (frame_quadratic_nonnegative v x.val) (sq_nonneg _)

theorem leastEigenvalue_is_eigenvalue [FiniteDimensional ℝ E] [Nontrivial E] (v : O → E) :
    HasEigenvalue (frameOperator v) (leastEigenvalue v) := by
  simpa [leastEigenvalue] using (frame_symmetric v).hasEigenvalue_iInf_of_finiteDimensional

theorem leastEigenvalue_lower_bound (v : O → E) :
    CoerciveLeastSquares.Coercive (frameOperator v) (leastEigenvalue v) := by
  intro x
  by_cases hx : x=0
  · simp [hx]
  have hp : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hh := ciInf_le (rayleigh_bddBelow v) (⟨x,hx⟩ : {x : E // x ≠ 0})
  change leastEigenvalue v ≤ ⟪frameOperator v x,x⟫_ℝ / ‖x‖^2 at hh
  rw [real_inner_comm] at hh
  exact (le_div_iff₀ hp).mp hh

theorem leastEigenvalue_is_least (v : O → E) (μ : ℝ) (hμ : HasEigenvalue (frameOperator v) μ) :
    leastEigenvalue v ≤ μ := by
  obtain ⟨x,hx,hne⟩ := hμ.exists_hasEigenvector
  have he : frameOperator v x=μ • x := by simpa only [mem_genEigenspace_one] using hx
  have hh := ciInf_le (rayleigh_bddBelow v) (⟨x,hne⟩ : {x : E // x ≠ 0})
  change leastEigenvalue v ≤ ⟪frameOperator v x,x⟫_ℝ / ‖x‖^2 at hh
  simpa [he,inner_smul_left,real_inner_self_eq_norm_sq,
    norm_ne_zero_iff.mpr hne] using hh

theorem leastEigenvalue_positive_iff_identifying [FiniteDimensional ℝ E] [Nontrivial E]
    (v : O → E) :
    0 < leastEigenvalue v ↔ ∀ x : E, (∀ o, ⟪v o,x⟫_ℝ=0) → x=0 := by
  constructor
  · intro hk x hx
    have hh := leastEigenvalue_lower_bound v x
    rw [frameOperator_quadratic] at hh
    simp only [hx,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
    have hn : ‖x‖^2=0 := by nlinarith [sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro hsep
    obtain ⟨k,hk,hbound⟩ := exists_positive_coercivity_of_separating v hsep
    letI : Nonempty {x : E // x ≠ 0} :=
      ⟨⟨(exists_ne (0:E)).choose,(exists_ne (0:E)).choose_spec⟩⟩
    apply lt_of_lt_of_le hk
    apply le_ciInf
    intro x
    have hp : 0 < ‖x.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr x.property)
    rw [real_inner_comm]
    exact (le_div_iff₀ hp).mpr (hbound x.val)

theorem exact_frame_transport (U : E ≃ₗᵢ[ℝ] F) (v : O → E) :
    frameOperator (fun o => U (v o)) =
      U.toLinearMap.comp ((frameOperator v).comp U.symm.toLinearMap) := by
  ext x
  simp [frameOperator,transported_measurement,LinearMap.comp_apply]

theorem transported_eigenvalue (U : E ≃ₗᵢ[ℝ] F) (v : O → E) (μ : ℝ)
    (hμ : HasEigenvalue (frameOperator v) μ) :
    HasEigenvalue (frameOperator (fun o => U (v o))) μ := by
  obtain ⟨x,hx,hne⟩ := hμ.exists_hasEigenvector
  apply hasEigenvalue_of_hasEigenvector (x := U x)
  apply hasEigenvector_iff.mpr
  constructor
  · have he : frameOperator v x=μ • x := by simpa only [mem_genEigenspace_one] using hx
    simp [exact_frame_transport,LinearMap.comp_apply,he]
  · exact fun hz => hne (U.injective (by simpa using hz))

theorem frame_spectrum_invariant (U : E ≃ₗᵢ[ℝ] F) (v : O → E) (μ : ℝ) :
    HasEigenvalue (frameOperator (fun o => U (v o))) μ ↔ HasEigenvalue (frameOperator v) μ := by
  constructor
  · intro h
    simpa using transported_eigenvalue U.symm (fun o => U (v o)) μ h
  · exact transported_eigenvalue U v μ

end
end QubitOracle.AdaptiveDesign.ExactFrameSpectrum
