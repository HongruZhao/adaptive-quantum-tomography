import QubitOracle.IsotropicOptimality

/-!
# Mixed-qubit oracle trace optimization

This module proves the sharp finite-dimensional optimization that remains
after the mixed-qubit information constraint has been reduced to eigenvalue
coordinates.  If `r i > 0` are the eigenvalues of the positive square root of
the loss matrix and `a i > 0` are the information eigenvalues, then

`sum_i (r i)^2 / a i >= (sum_i r i)^2`

under `sum_i a i <= 1`.  Equality holds exactly at
`a i = r i / sum_j r j`.  Thus the minimum is the square of the trace of the
square root, and the unique optimizer is proportional to that square root.

The concrete matrix theorems below prove all trace and inverse identities for
diagonal matrices in the chosen eigenbasis.  The final bridge theorems state
the exact identities needed to transport the result to arbitrary matrices.
What is deliberately not proved here is the fully coordinate-free step that,
for arbitrary positive-definite `C` and `A`, constructs Mathlib's matrix
square root, changes to a spectral basis for `C`, and shows that off-diagonal
coordinates of `A` cannot improve `trace (C * A⁻¹)`.  No such statement is
introduced as an axiom: its required conclusions are explicit hypotheses of
the bridge theorems.
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι]

/-- Trace of the square root in eigenvalue coordinates.  The intended
interpretation is that `r i` are the positive eigenvalues of `sqrt C`. -/
def mixedOracleSqrtTrace (r : ι → ℝ) : ℝ :=
  ∑ i, r i

/-- The objective `trace (C A⁻¹)` after simultaneous diagonal reduction,
where the eigenvalues of `C` are `(r i)^2`. -/
def mixedOracleEigenRisk (r a : ι → ℝ) : ℝ :=
  ∑ i, (r i) ^ 2 / a i

/-- Nonnegative remainder measuring deviation from the oracle optimizer. -/
def mixedOracleDispersion (r a : ι → ℝ) : ℝ :=
  ∑ i, (r i - mixedOracleSqrtTrace r * a i) ^ 2 / a i

/-- Exact completion-of-squares identity behind the oracle bound. -/
lemma mixedOracleEigenRisk_decomposition (r a : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    mixedOracleEigenRisk r a =
      2 * (mixedOracleSqrtTrace r) ^ 2 -
        (mixedOracleSqrtTrace r) ^ 2 * (∑ i, a i) +
        mixedOracleDispersion r a := by
  classical
  have hpoint (i : ι) :
      (r i) ^ 2 / a i =
        2 * mixedOracleSqrtTrace r * r i -
          (mixedOracleSqrtTrace r) ^ 2 * a i +
          (r i - mixedOracleSqrtTrace r * a i) ^ 2 / a i := by
    field_simp [ha i]
    ring
  calc
    mixedOracleEigenRisk r a =
        ∑ i, (2 * mixedOracleSqrtTrace r * r i -
          (mixedOracleSqrtTrace r) ^ 2 * a i +
          (r i - mixedOracleSqrtTrace r * a i) ^ 2 / a i) := by
      unfold mixedOracleEigenRisk
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = 2 * (mixedOracleSqrtTrace r) ^ 2 -
        (mixedOracleSqrtTrace r) ^ 2 * (∑ i, a i) +
        mixedOracleDispersion r a := by
      simp only [mixedOracleDispersion, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [mixedOracleSqrtTrace]
      ring

/-- The completion-of-squares remainder is nonnegative for positive
information eigenvalues. -/
lemma mixedOracleDispersion_nonneg (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i) :
    0 ≤ mixedOracleDispersion r a := by
  exact Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (ha i).le

/-- Sharp weighted reciprocal inequality under the unit trace budget. -/
theorem mixedOracleEigenRisk_lower_bound (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hbudget : (∑ i, a i) ≤ 1) :
    (mixedOracleSqrtTrace r) ^ 2 ≤ mixedOracleEigenRisk r a := by
  rw [mixedOracleEigenRisk_decomposition r a fun i => (ha i).ne']
  have hgap : 0 ≤ 1 - ∑ i, a i := sub_nonneg.mpr hbudget
  have hscaled :
      0 ≤ (mixedOracleSqrtTrace r) ^ 2 * (1 - ∑ i, a i) :=
    mul_nonneg (sq_nonneg _) hgap
  have hdisp := mixedOracleDispersion_nonneg r a ha
  nlinarith

/-- Equality in the weighted reciprocal inequality uniquely fixes every
information eigenvalue. -/
theorem mixedOracleEigenRisk_eq_value_iff (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hs : 0 < mixedOracleSqrtTrace r)
    (hbudget : (∑ i, a i) ≤ 1) :
    mixedOracleEigenRisk r a = (mixedOracleSqrtTrace r) ^ 2 ↔
      ∀ i, a i = r i / mixedOracleSqrtTrace r := by
  constructor
  · intro heq
    have hdecomp := mixedOracleEigenRisk_decomposition r a
      (fun i => (ha i).ne')
    have hdispnonneg := mixedOracleDispersion_nonneg r a ha
    have hgap : 0 ≤ 1 - ∑ i, a i := sub_nonneg.mpr hbudget
    have hscaled :
        0 ≤ (mixedOracleSqrtTrace r) ^ 2 * (1 - ∑ i, a i) :=
      mul_nonneg (sq_nonneg _) hgap
    have hdispzero : mixedOracleDispersion r a = 0 := by
      nlinarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) =>
        div_nonneg
          (sq_nonneg (r i - mixedOracleSqrtTrace r * a i))
          (ha i).le)).mp hdispzero
    intro i
    have hi := hterm i (Finset.mem_univ i)
    have hsquare :
        (r i - mixedOracleSqrtTrace r * a i) ^ 2 = 0 := by
      simpa [(ha i).ne'] using hi
    apply (eq_div_iff hs.ne').2
    nlinarith
  · intro hopt
    have hsum : (∑ i, a i) = 1 := by
      calc
        (∑ i, a i) =
            ∑ i, r i / mixedOracleSqrtTrace r := by
          apply Finset.sum_congr rfl
          intro i _
          exact hopt i
        _ = mixedOracleSqrtTrace r / mixedOracleSqrtTrace r := by
          rw [← Finset.sum_div]
          rfl
        _ = 1 := div_self hs.ne'
    have hpointzero (i : ι) :
        r i - mixedOracleSqrtTrace r * a i = 0 := by
      rw [hopt i]
      field_simp [hs.ne'] <;> ring
    have hdispzero : mixedOracleDispersion r a = 0 := by
      simp [mixedOracleDispersion, hpointzero]
    rw [mixedOracleEigenRisk_decomposition r a
      (fun i => (ha i).ne'), hsum, hdispzero]
    ring

/-- Oracle information eigenvalues, normalized to use the full trace
budget. -/
def mixedOracleEigenOptimizer (r : ι → ℝ) (i : ι) : ℝ :=
  r i / mixedOracleSqrtTrace r

/-- The oracle eigenvalues saturate the unit trace budget. -/
theorem mixedOracleEigenOptimizer_sum (r : ι → ℝ)
    (hs : mixedOracleSqrtTrace r ≠ 0) :
    (∑ i, mixedOracleEigenOptimizer r i) = 1 := by
  unfold mixedOracleEigenOptimizer
  rw [← Finset.sum_div]
  exact div_self hs

/-- Strictly positive square-root eigenvalues give a feasible strictly
positive optimizer. -/
theorem mixedOracleEigenOptimizer_pos (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hs : 0 < mixedOracleSqrtTrace r) :
    ∀ i, 0 < mixedOracleEigenOptimizer r i := by
  intro i
  exact div_pos (hr i) hs

/-- The oracle eigenvalues attain the predicted value. -/
theorem mixedOracleEigenOptimizer_value (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hs : 0 < mixedOracleSqrtTrace r) :
    mixedOracleEigenRisk r (mixedOracleEigenOptimizer r) =
      (mixedOracleSqrtTrace r) ^ 2 := by
  have hpos := mixedOracleEigenOptimizer_pos r hr hs
  have hbudget :
      (∑ i, mixedOracleEigenOptimizer r i) ≤ 1 :=
    (mixedOracleEigenOptimizer_sum r hs.ne').le
  exact (mixedOracleEigenRisk_eq_value_iff r
    (mixedOracleEigenOptimizer r) hpos hs hbudget).2 fun i => rfl

/-- Feasible eigenvalue allocations for the unit trace budget. -/
def mixedOracleEigenFeasible (a : ι → ℝ) : Prop :=
  (∀ i, 0 < a i) ∧ (∑ i, a i) ≤ 1

/-- Set of objective values attained by feasible eigenvalue allocations. -/
def mixedOracleEigenRiskValues (r : ι → ℝ) : Set ℝ :=
  {x | ∃ a, mixedOracleEigenFeasible a ∧
    x = mixedOracleEigenRisk r a}

/-- The predicted value is the attained minimum of the eigenvalue problem. -/
theorem mixedOracleEigenOptimizer_isLeast (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hs : 0 < mixedOracleSqrtTrace r) :
    IsLeast (mixedOracleEigenRiskValues r)
      ((mixedOracleSqrtTrace r) ^ 2) := by
  constructor
  · refine ⟨mixedOracleEigenOptimizer r, ?_, ?_⟩
    · exact ⟨mixedOracleEigenOptimizer_pos r hr hs,
        (mixedOracleEigenOptimizer_sum r hs.ne').le⟩
    · exact (mixedOracleEigenOptimizer_value r hr hs).symm
  · intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    exact mixedOracleEigenRisk_lower_bound r a ha.1 ha.2

section Matrix

variable [DecidableEq ι]

/-- Loss matrix with eigenvalues `(r i)^2` in the selected basis. -/
def mixedOracleDiagonalCost (r : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => (r i) ^ 2

/-- Positive square-root factor of `mixedOracleDiagonalCost` in the selected
basis. -/
def mixedOracleDiagonalSqrt (r : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal r

/-- Information matrix with eigenvalues `a i` in the selected basis. -/
def mixedOracleDiagonalInformation (a : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal a

/-- The displayed diagonal square root squares exactly to the cost matrix. -/
theorem mixedOracleDiagonalSqrt_sq (r : ι → ℝ) :
    mixedOracleDiagonalSqrt r * mixedOracleDiagonalSqrt r =
      mixedOracleDiagonalCost r := by
  unfold mixedOracleDiagonalSqrt mixedOracleDiagonalCost
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-- Matrix trace of the displayed square root is the sum of its eigenvalues. -/
theorem mixedOracleDiagonalSqrt_trace (r : ι → ℝ) :
    (mixedOracleDiagonalSqrt r).trace = mixedOracleSqrtTrace r := by
  simp [mixedOracleDiagonalSqrt, mixedOracleSqrtTrace]

/-- Matrix trace of diagonal information is its eigenvalue sum. -/
theorem mixedOracleDiagonalInformation_trace (a : ι → ℝ) :
    (mixedOracleDiagonalInformation a).trace = ∑ i, a i := by
  simp [mixedOracleDiagonalInformation]

/-- Exact inverse of a diagonal information matrix. -/
lemma mixedOracleDiagonalInformation_inv (a : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    (mixedOracleDiagonalInformation a)⁻¹ =
      Matrix.diagonal (fun i => (a i)⁻¹) := by
  unfold mixedOracleDiagonalInformation
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  rw [Matrix.diagonal_eq_one]
  funext i
  simp [ha i]

/-- Matrix-form objective for the diagonal reduction. -/
def mixedOracleDiagonalRisk (r a : ι → ℝ) : ℝ :=
  Matrix.trace
    (mixedOracleDiagonalCost r * (mixedOracleDiagonalInformation a)⁻¹)

/-- Exact reduction of the matrix trace objective to the eigenvalue sum. -/
theorem mixedOracleDiagonalRisk_eq_eigenRisk (r a : ι → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    mixedOracleDiagonalRisk r a = mixedOracleEigenRisk r a := by
  rw [mixedOracleDiagonalRisk, mixedOracleDiagonalInformation_inv a ha]
  unfold mixedOracleDiagonalCost
  rw [Matrix.diagonal_mul_diagonal]
  simp [mixedOracleEigenRisk, div_eq_mul_inv]

/-- Matrix oracle optimizer in the selected eigenbasis. -/
def mixedOracleDiagonalOptimizer (r : ι → ℝ) : Matrix ι ι ℝ :=
  mixedOracleDiagonalInformation (mixedOracleEigenOptimizer r)

/-- The matrix optimizer is proportional to the displayed square root. -/
theorem mixedOracleDiagonalOptimizer_eq_smul_sqrt (r : ι → ℝ) :
    mixedOracleDiagonalOptimizer r =
      (mixedOracleSqrtTrace r)⁻¹ • mixedOracleDiagonalSqrt r := by
  unfold mixedOracleDiagonalOptimizer mixedOracleDiagonalInformation
    mixedOracleDiagonalSqrt
  calc
    Matrix.diagonal (mixedOracleEigenOptimizer r) =
        Matrix.diagonal ((mixedOracleSqrtTrace r)⁻¹ • r) := by
      congr 1
      funext i
      simp [mixedOracleEigenOptimizer, div_eq_mul_inv, mul_comm]
    _ = (mixedOracleSqrtTrace r)⁻¹ • Matrix.diagonal r :=
      Matrix.diagonal_smul _ _

/-- The diagonal matrix optimizer saturates the matrix trace budget. -/
theorem mixedOracleDiagonalOptimizer_trace (r : ι → ℝ)
    (hs : mixedOracleSqrtTrace r ≠ 0) :
    (mixedOracleDiagonalOptimizer r).trace = 1 := by
  rw [mixedOracleDiagonalOptimizer,
    mixedOracleDiagonalInformation_trace,
    mixedOracleEigenOptimizer_sum r hs]

/-- Sharp matrix trace-risk lower bound in the exact diagonal reduction. -/
theorem mixedOracleDiagonalRisk_lower_bound (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hbudget : (mixedOracleDiagonalInformation a).trace ≤ 1) :
    (mixedOracleDiagonalSqrt r).trace ^ 2 ≤
      mixedOracleDiagonalRisk r a := by
  rw [mixedOracleDiagonalSqrt_trace,
    mixedOracleDiagonalRisk_eq_eigenRisk r a fun i => (ha i).ne']
  apply mixedOracleEigenRisk_lower_bound r a ha
  rwa [mixedOracleDiagonalInformation_trace] at hbudget

/-- The diagonal optimizer attains `(trace (sqrt C))^2`. -/
theorem mixedOracleDiagonalOptimizer_value (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hs : 0 < mixedOracleSqrtTrace r) :
    mixedOracleDiagonalRisk r (mixedOracleEigenOptimizer r) =
      (mixedOracleDiagonalSqrt r).trace ^ 2 := by
  rw [mixedOracleDiagonalRisk_eq_eigenRisk r
      (mixedOracleEigenOptimizer r)
      (fun i => (mixedOracleEigenOptimizer_pos r hr hs i).ne'),
    mixedOracleDiagonalSqrt_trace]
  exact mixedOracleEigenOptimizer_value r hr hs

/-- Equality in the diagonal matrix bound holds exactly at the oracle matrix;
this is uniqueness within the exact eigenvalue reduction. -/
theorem mixedOracleDiagonalRisk_eq_value_iff (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hs : 0 < mixedOracleSqrtTrace r)
    (hbudget : (mixedOracleDiagonalInformation a).trace ≤ 1) :
    mixedOracleDiagonalRisk r a =
        (mixedOracleDiagonalSqrt r).trace ^ 2 ↔
      mixedOracleDiagonalInformation a =
        mixedOracleDiagonalOptimizer r := by
  have hbudget' : (∑ i, a i) ≤ 1 := by
    rwa [mixedOracleDiagonalInformation_trace] at hbudget
  have hscalar := mixedOracleEigenRisk_eq_value_iff r a ha hs hbudget'
  constructor
  · intro heq
    have heq' :
        mixedOracleEigenRisk r a = (mixedOracleSqrtTrace r) ^ 2 := by
      rwa [mixedOracleDiagonalRisk_eq_eigenRisk r a
          (fun i => (ha i).ne'),
        mixedOracleDiagonalSqrt_trace] at heq
    have hcoords := hscalar.mp heq'
    have hfun : a = mixedOracleEigenOptimizer r := funext hcoords
    unfold mixedOracleDiagonalOptimizer
    rw [hfun]
  · intro hmatrix
    have hcoords : ∀ i, a i = mixedOracleEigenOptimizer r i := by
      intro i
      have hii := congrArg
        (fun M : Matrix ι ι ℝ => M i i) hmatrix
      simpa [mixedOracleDiagonalInformation,
        mixedOracleDiagonalOptimizer] using hii
    have heq := hscalar.mpr hcoords
    rwa [mixedOracleDiagonalRisk_eq_eigenRisk r a
        (fun i => (ha i).ne'),
      mixedOracleDiagonalSqrt_trace]

/-- Coordinate-reduction bridge for the lower bound.  Its three equality
hypotheses are precisely the remaining spectral/change-of-basis obligation
for a general pair `C, A`. -/
theorem mixedOracleRisk_lower_bound_of_eigen_reduction
    (C sqrtC A : Matrix ι ι ℝ) (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hbudget : A.trace ≤ 1)
    (htraceA : A.trace = ∑ i, a i)
    (htraceSqrtC : sqrtC.trace = mixedOracleSqrtTrace r)
    (hrisk : Matrix.trace (C * A⁻¹) = mixedOracleEigenRisk r a) :
    sqrtC.trace ^ 2 ≤ Matrix.trace (C * A⁻¹) := by
  rw [htraceSqrtC, hrisk]
  apply mixedOracleEigenRisk_lower_bound r a ha
  rwa [← htraceA]

/-- Coordinate-reduction bridge for uniqueness.  The last hypothesis is the
explicit coordinate identification of the proportional square-root matrix;
no coordinate-free square-root theorem is assumed by this module. -/
theorem mixedOracleRisk_eq_value_iff_of_eigen_reduction
    (C sqrtC A : Matrix ι ι ℝ) (r a : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (hs : 0 < mixedOracleSqrtTrace r)
    (hbudget : A.trace ≤ 1)
    (htraceA : A.trace = ∑ i, a i)
    (htraceSqrtC : sqrtC.trace = mixedOracleSqrtTrace r)
    (hrisk : Matrix.trace (C * A⁻¹) = mixedOracleEigenRisk r a)
    (hoptimizer :
      (∀ i, a i = mixedOracleEigenOptimizer r i) ↔
        A = (mixedOracleSqrtTrace r)⁻¹ • sqrtC) :
    Matrix.trace (C * A⁻¹) = sqrtC.trace ^ 2 ↔
      A = (mixedOracleSqrtTrace r)⁻¹ • sqrtC := by
  have hbudget' : (∑ i, a i) ≤ 1 := by
    rwa [← htraceA]
  rw [hrisk, htraceSqrtC]
  exact (mixedOracleEigenRisk_eq_value_iff r a ha hs hbudget').trans
    hoptimizer

end Matrix

end

end Paper
end QubitOracle

#print axioms QubitOracle.Paper.mixedOracleEigenOptimizer_isLeast
#print axioms QubitOracle.Paper.mixedOracleDiagonalRisk_lower_bound
#print axioms QubitOracle.Paper.mixedOracleDiagonalOptimizer_value
#print axioms QubitOracle.Paper.mixedOracleDiagonalRisk_eq_value_iff
#print axioms QubitOracle.Paper.mixedOracleRisk_eq_value_iff_of_eigen_reduction
