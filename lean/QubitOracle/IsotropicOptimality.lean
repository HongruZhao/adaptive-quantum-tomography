import QubitOracle.RankOneLosses

/-!
# Sharp isotropic trace-budget optimization

This file proves the finite classical matrix inequality needed after a
Gill--Massar trace budget has been supplied.  For a positive-definite
information matrix on `k` coordinates with `trace M <= k/2`, isotropic risk
`g trace(M^{-1})` is at least `2 g k`.  For `g > 0`, equality holds exactly at
`M = (1/2) I`.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι]

/-- Sum of nonnegative coordinatewise deviations from the isotropic equality
case. -/
def dispersion (m : ι → ℝ) : ℝ :=
  ∑ i, (2 * m i - 1) ^ 2 / m i

lemma reciprocal_decomposition (m : ι → ℝ) (hm : ∀ i, m i ≠ 0) :
    (∑ i, (m i)⁻¹) =
      4 * (Fintype.card ι : ℝ) - 4 * (∑ i, m i) + dispersion m := by
  classical
  have hpoint (i : ι) :
      (m i)⁻¹ = 4 - 4 * m i + (2 * m i - 1) ^ 2 / m i := by
    field_simp [hm i]
    ring
  calc
    (∑ i, (m i)⁻¹) = ∑ i, (4 - 4 * m i + (2 * m i - 1) ^ 2 / m i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = 4 * (Fintype.card ι : ℝ) - 4 * (∑ i, m i) + dispersion m := by
      simp [dispersion, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
      ring

lemma dispersion_nonneg (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    0 ≤ dispersion m := by
  exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hm i).le

/-- Reciprocal-sum lower bound under the half-dimension trace budget. -/
theorem reciprocal_sum_lower_bound (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    (hbudget : (∑ i, m i) ≤ (Fintype.card ι : ℝ) / 2) :
    2 * (Fintype.card ι : ℝ) ≤ ∑ i, (m i)⁻¹ := by
  rw [reciprocal_decomposition m fun i => (hm i).ne']
  have hd := dispersion_nonneg m hm
  linarith

/-- Sharp equality characterization for the reciprocal-sum inequality. -/
theorem reciprocal_sum_eq_lower_bound_iff (m : ι → ℝ)
    (hm : ∀ i, 0 < m i)
    (hbudget : (∑ i, m i) ≤ (Fintype.card ι : ℝ) / 2) :
    (∑ i, (m i)⁻¹) = 2 * (Fintype.card ι : ℝ) ↔
      ∀ i, m i = 1 / 2 := by
  constructor
  · intro heq
    have hdecomp := reciprocal_decomposition m fun i => (hm i).ne'
    have hdnonneg := dispersion_nonneg m hm
    have hdzero : dispersion m = 0 := by
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) =>
        div_nonneg (sq_nonneg (2 * m i - 1)) (hm i).le)).mp hdzero
    intro i
    have hi := hterm i (Finset.mem_univ i)
    have hsquare : (2 * m i - 1) ^ 2 = 0 := by
      simpa [(hm i).ne'] using hi
    nlinarith
  · intro hhalf
    simp [hhalf]
    ring

section Matrix

variable [DecidableEq ι]

lemma posDef_inv_eq_spectral (M : Matrix ι ι ℝ) (hM : M.PosDef) :
    M⁻¹ =
      (hM.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i)⁻¹) *
        star (hM.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) := by
  let U : Matrix ι ι ℝ := hM.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal hM.isHermitian.eigenvalues
  let Dinv : Matrix ι ι ℝ :=
    Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i)⁻¹)
  have hstarU : star U * U = 1 := by
    exact Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
  have hUstar : U * star U = 1 := by
    exact Unitary.coe_mul_star_self hM.isHermitian.eigenvectorUnitary
  have hDDinv : D * Dinv = 1 := by
    change Matrix.diagonal hM.isHermitian.eigenvalues *
      Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    rw [Matrix.diagonal_eq_one]
    funext i
    simp [(hM.eigenvalues_pos i).ne']
  apply Matrix.inv_eq_right_inv
  conv_lhs =>
    lhs
    rw [hM.isHermitian.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  change (U * D * star U) * (U * Dinv * star U) = 1
  calc
    (U * D * star U) * (U * Dinv * star U) =
        U * D * (star U * U) * Dinv * star U := by
      simp only [Matrix.mul_assoc]
    _ = U * (D * Dinv) * star U := by rw [hstarU]; simp [Matrix.mul_assoc]
    _ = 1 := by rw [hDDinv]; simpa using hUstar

lemma posDef_trace_inv_eq_sum_inv_eigenvalues (M : Matrix ι ι ℝ)
    (hM : M.PosDef) :
    M⁻¹.trace = ∑ i, (hM.isHermitian.eigenvalues i)⁻¹ := by
  rw [posDef_inv_eq_spectral M hM]
  rw [Matrix.trace_mul_cycle]
  simp

/-- Isotropic quadratic asymptotic risk associated with an information
matrix. -/
def isotropicRisk (g : ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  g * M⁻¹.trace

/-- Exact risk of the half-identity information matrix. -/
theorem isotropicRisk_half_identity (g : ℝ) :
    isotropicRisk g ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) =
      2 * g * (Fintype.card ι : ℝ) := by
  rw [isotropicRisk]
  have hinv :
      (((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ))⁻¹) =
        (2 : ℝ) • (1 : Matrix ι ι ℝ) := by
    apply Matrix.inv_eq_right_inv
    norm_num [smul_smul]
  rw [hinv, Matrix.trace_smul, Matrix.trace_one]
  norm_num
  ring

/-- Sharp isotropic-risk lower bound under a half-dimension trace budget. -/
theorem isotropicRisk_lower_bound (g : ℝ) (M : Matrix ι ι ℝ)
    (hg : 0 ≤ g) (hM : M.PosDef)
    (hbudget : M.trace ≤ (Fintype.card ι : ℝ) / 2) :
    2 * g * (Fintype.card ι : ℝ) ≤ isotropicRisk g M := by
  have htrace : M.trace = ∑ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.trace_eq_sum_eigenvalues
  have hbudget' :
      (∑ i, hM.isHermitian.eigenvalues i) ≤ (Fintype.card ι : ℝ) / 2 := by
    rwa [← htrace]
  have hlower := reciprocal_sum_lower_bound hM.isHermitian.eigenvalues
    hM.eigenvalues_pos hbudget'
  rw [isotropicRisk, posDef_trace_inv_eq_sum_inv_eigenvalues M hM]
  calc
    2 * g * (Fintype.card ι : ℝ) =
        g * (2 * (Fintype.card ι : ℝ)) := by ring
    _ ≤ g * ∑ i, (hM.isHermitian.eigenvalues i)⁻¹ :=
      mul_le_mul_of_nonneg_left hlower hg

/-- For positive loss weight, equality in the risk bound holds exactly at the
half identity. -/
theorem isotropicRisk_eq_lower_bound_iff (g : ℝ) (M : Matrix ι ι ℝ)
    (hg : 0 < g) (hM : M.PosDef)
    (hbudget : M.trace ≤ (Fintype.card ι : ℝ) / 2) :
    isotropicRisk g M = 2 * g * (Fintype.card ι : ℝ) ↔
      M = (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) := by
  have htrace : M.trace = ∑ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.trace_eq_sum_eigenvalues
  have hbudget' :
      (∑ i, hM.isHermitian.eigenvalues i) ≤ (Fintype.card ι : ℝ) / 2 := by
    rwa [← htrace]
  constructor
  · intro hrisk
    have heqsum :
        (∑ i, (hM.isHermitian.eigenvalues i)⁻¹) =
          2 * (Fintype.card ι : ℝ) := by
      rw [isotropicRisk, posDef_trace_inv_eq_sum_inv_eigenvalues M hM] at hrisk
      nlinarith
    have heigen : ∀ i, hM.isHermitian.eigenvalues i = 1 / 2 :=
      (reciprocal_sum_eq_lower_bound_iff hM.isHermitian.eigenvalues
        hM.eigenvalues_pos hbudget').mp heqsum
    rw [hM.isHermitian.spectral_theorem]
    have heigenfun : hM.isHermitian.eigenvalues = fun _ => 1 / 2 :=
      funext heigen
    rw [heigenfun]
    simp only [Unitary.conjStarAlgAut_apply]
    have hcomp : (RCLike.ofReal ∘ fun _ : ι => (1 / 2 : ℝ)) =
        fun _ => (1 / 2 : ℝ) := by
      funext i
      norm_num
    have hdiag : Matrix.diagonal (fun _ : ι => (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) := by
      calc
        Matrix.diagonal (fun _ : ι => (1 / 2 : ℝ)) =
            Matrix.diagonal ((1 / 2 : ℝ) • fun _ : ι => (1 : ℝ)) := by
          congr 1
          funext i
          simp
        _ = (1 / 2 : ℝ) • Matrix.diagonal (fun _ : ι => (1 : ℝ)) :=
          Matrix.diagonal_smul _ _
        _ = (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) := by
          rw [Matrix.diagonal_one]
    rw [hcomp, hdiag]
    simp
  · intro hhalf
    rw [hhalf]
    exact isotropicRisk_half_identity g

end Matrix

end


end QubitOracle
