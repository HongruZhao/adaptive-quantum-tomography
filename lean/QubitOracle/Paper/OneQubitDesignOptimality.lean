import Mathlib

/-!
# Exact reciprocal-information design optimality

After whitening by the local Bures metric, a one-qubit separable design has a
unit information-trace budget.  The pure model has two local coordinates and
the mixed model has three.  This file proves directly that reciprocal risk is
minimized by equal allocation.
-/

namespace QubitOracle.Paper

noncomputable def twoCoordinateReciprocalRisk (a b : ℝ) : ℝ :=
  a⁻¹ + b⁻¹

noncomputable def threeCoordinateReciprocalRisk (a b c : ℝ) : ℝ :=
  a⁻¹ + b⁻¹ + c⁻¹

private theorem two_positive_reciprocal_pair
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 ≤ a / b + b / a := by
  field_simp
  nlinarith [sq_nonneg (a - b)]

private theorem three_positive_reciprocal_product
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 ≤ (a + b + c) * threeCoordinateReciprocalRisk a b c := by
  have hab : 2 ≤ a / b + b / a :=
    two_positive_reciprocal_pair ha hb
  have hac : 2 ≤ a / c + c / a :=
    two_positive_reciprocal_pair ha hc
  have hbc : 2 ≤ b / c + c / b :=
    two_positive_reciprocal_pair hb hc
  unfold threeCoordinateReciprocalRisk
  field_simp
  nlinarith [
    mul_nonneg ha.le (sq_nonneg (b - c)),
    mul_nonneg hb.le (sq_nonneg (a - c)),
    mul_nonneg hc.le (sq_nonneg (a - b))]

/-- Two positive information eigenvalues under a unit trace budget have
reciprocal sum at least four. -/
theorem pure_twoCoordinate_information_budget_lower_bound
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbudget : a + b ≤ 1) :
    4 ≤ twoCoordinateReciprocalRisk a b := by
  have hpair := two_positive_reciprocal_pair ha hb
  have hproduct :
      4 ≤ (a + b) * twoCoordinateReciprocalRisk a b := by
    unfold twoCoordinateReciprocalRisk
    calc
      4 ≤ 2 + (a / b + b / a) := by linarith
      _ = (a + b) * (a⁻¹ + b⁻¹) := by
        field_simp
        ring
  have hrisk : 0 ≤ twoCoordinateReciprocalRisk a b := by
    exact add_nonneg (inv_nonneg.2 ha.le) (inv_nonneg.2 hb.le)
  calc
    4 ≤ (a + b) * twoCoordinateReciprocalRisk a b := hproduct
    _ ≤ 1 * twoCoordinateReciprocalRisk a b :=
      mul_le_mul_of_nonneg_right hbudget hrisk
    _ = twoCoordinateReciprocalRisk a b := one_mul _

/-- Three positive information eigenvalues under a unit trace budget have
reciprocal sum at least nine. -/
theorem mixed_threeCoordinate_information_budget_lower_bound
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbudget : a + b + c ≤ 1) :
    9 ≤ threeCoordinateReciprocalRisk a b c := by
  have hproduct := three_positive_reciprocal_product ha hb hc
  have hrisk : 0 ≤ threeCoordinateReciprocalRisk a b c := by
    unfold threeCoordinateReciprocalRisk
    positivity
  calc
    9 ≤ (a + b + c) * threeCoordinateReciprocalRisk a b c := hproduct
    _ ≤ 1 * threeCoordinateReciprocalRisk a b c :=
      mul_le_mul_of_nonneg_right hbudget hrisk
    _ = threeCoordinateReciprocalRisk a b c := one_mul _

theorem pure_equal_design_attains_reciprocal_bound :
    twoCoordinateReciprocalRisk (1 / 2) (1 / 2) = 4 := by
  norm_num [twoCoordinateReciprocalRisk]

theorem mixed_equal_design_attains_reciprocal_bound :
    threeCoordinateReciprocalRisk (1 / 3) (1 / 3) (1 / 3) = 9 := by
  norm_num [threeCoordinateReciprocalRisk]

/-- With Bures weight `1/4`, the pure local design lower bound is one. -/
theorem pure_bures_design_constant_lower_bound
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbudget : a + b ≤ 1) :
    1 ≤ (1 / 4 : ℝ) * twoCoordinateReciprocalRisk a b := by
  nlinarith [pure_twoCoordinate_information_budget_lower_bound ha hb hbudget]

/-- With Bures weight `1/4`, the mixed local design lower bound is `9/4`. -/
theorem mixed_bures_design_constant_lower_bound
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbudget : a + b + c ≤ 1) :
    (9 / 4 : ℝ) ≤
      (1 / 4 : ℝ) * threeCoordinateReciprocalRisk a b c := by
  nlinarith [
    mixed_threeCoordinate_information_budget_lower_bound
      ha hb hc hbudget]

theorem pure_equal_design_attains_bures_constant :
    (1 / 4 : ℝ) *
      twoCoordinateReciprocalRisk (1 / 2) (1 / 2) = 1 := by
  norm_num [twoCoordinateReciprocalRisk]

theorem mixed_equal_design_attains_bures_constant :
    (1 / 4 : ℝ) *
      threeCoordinateReciprocalRisk (1 / 3) (1 / 3) (1 / 3) = 9 / 4 := by
  norm_num [threeCoordinateReciprocalRisk]

namespace Label

theorem thm_SI_pure_equal_information_design_optimal
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbudget : a + b ≤ 1) :
    1 ≤ (1 / 4 : ℝ) * twoCoordinateReciprocalRisk a b :=
  pure_bures_design_constant_lower_bound ha hb hbudget

theorem thm_SI_mixed_equal_information_design_optimal
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hbudget : a + b + c ≤ 1) :
    (9 / 4 : ℝ) ≤
      (1 / 4 : ℝ) * threeCoordinateReciprocalRisk a b c :=
  mixed_bures_design_constant_lower_bound ha hb hc hbudget

end Label
end QubitOracle.Paper
