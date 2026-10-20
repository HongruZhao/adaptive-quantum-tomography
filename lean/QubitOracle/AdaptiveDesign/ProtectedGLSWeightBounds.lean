import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
/-! Uniform finite-row bounds for fitted inverse-probability weights.
The fitted argument is arbitrary: these inequalities do not assume it is
predictable or independent of the observed outcome. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open scoped BigOperators InnerProductSpace
noncomputable section

theorem denominator_lipschitz (floor p q : ℝ) :
    |denominator floor q - denominator floor p| ≤ |q-p| :=
  abs_max_sub_max_le_abs q p floor

theorem protected_inverse_lipschitz (floor p q : ℝ) (hf : 0 < floor) :
    |(denominator floor q)⁻¹ - (denominator floor p)⁻¹| ≤ |q-p| / floor^2 := by
  have hp := denominator_pos hf p
  have hq := denominator_pos hf q
  have hprod : floor^2 ≤ denominator floor q * denominator floor p := by
    simpa only [pow_two, denominator] using
      (mul_le_mul (le_max_right q floor) (le_max_right p floor) hf.le hq.le)
  have heq : (denominator floor q)⁻¹ - (denominator floor p)⁻¹ =
      (denominator floor p - denominator floor q) /
        (denominator floor q * denominator floor p) := by field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hq hp), abs_sub_comm]
  exact div_le_div₀ (abs_nonneg _) (denominator_lipschitz floor p q)
    (sq_pos_of_pos hf) hprod

def remainderCoefficient (floor p q observed tangentError : ℝ) : ℝ :=
  (observed-p) * (tangentError - (denominator floor q - denominator floor p)) /
      denominator floor p^2 +
    (observed-p) * (denominator floor q - denominator floor p)^2 /
      (denominator floor p^2 * denominator floor q) -
    (q-p-tangentError) / denominator floor q

theorem fittedWeightRemainder_eq_sum {E R : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype R]
    (f : R → E) (p q observed : R → ℝ) (floor : ℝ) (e : E) :
    fittedWeightRemainder f p q observed floor e =
      ∑ r, remainderCoefficient floor (p r) (q r) (observed r) ⟪f r,e⟫_ℝ • f r := rfl

theorem abs_div_bound (x y B m : ℝ) (hm : 0 < m) (hy : m ≤ y) (hx : |x| ≤ B) :
    |x/y| ≤ B/m := by
  rw [abs_div, abs_of_pos (hm.trans_le hy)]
  exact div_le_div₀ ((abs_nonneg x).trans hx) hx hm hy

/-- Quadratic bound on every row where the floor is inactive. The two
inputs are the Born increment and the normal (curvature) error. -/
theorem remainderCoefficient_regular_bound
    (floor p q observed a increment curvature : ℝ)
    (hf : 0 < floor) (hp : floor ≤ p) (hq : floor ≤ q)
    (hz : |observed-p| ≤ 1) (hi : |q-p| ≤ increment)
    (hc : |q-p-a| ≤ curvature) :
    |remainderCoefficient floor p q observed a| ≤
      curvature/floor^2 + increment^2/floor^3 + curvature/floor := by
  have hc0 : 0 ≤ curvature := (abs_nonneg _).trans hc
  have hi0 : 0 ≤ increment := (abs_nonneg _).trans hi
  have hpsq : floor^2 ≤ p^2 := by nlinarith
  have hprod : floor^3 ≤ p^2*q := by
    calc
      floor^3 = floor^2*floor := by ring
      _ ≤ p^2*q := mul_le_mul hpsq hq hf.le (sq_nonneg p)
  have ha : |a-(q-p)| ≤ curvature := by simpa [abs_sub_comm] using hc
  have hfirst : |(observed-p)*(a-(q-p))/p^2| ≤ curvature/floor^2 := by
    apply abs_div_bound _ _ _ _ (sq_pos_of_pos hf) hpsq
    rw [abs_mul]
    calc
      _ ≤ 1*curvature := mul_le_mul hz ha (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hsecond : |(observed-p)*(q-p)^2/(p^2*q)| ≤ increment^2/floor^3 := by
    apply abs_div_bound _ _ _ _ (pow_pos hf _) hprod
    rw [abs_mul, abs_pow]
    have hsq : |q-p|^2 ≤ increment^2 := by nlinarith [abs_nonneg (q-p)]
    calc
      _ ≤ 1*increment^2 := mul_le_mul hz hsq (sq_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hthird : |(q-p-a)/q| ≤ curvature/floor := abs_div_bound _ _ _ _ hf hq hc
  simp only [remainderCoefficient, denominator, max_eq_left hp, max_eq_left hq]
  exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) (le_refl _)).trans
    (add_le_add (add_le_add hfirst hsecond) hthird))

/-- A global bound, including old records whose denominators stay clipped.
Only finitely many such records will enter the asymptotic application. -/
theorem remainderCoefficient_global_bound
    (floor p q observed a A : ℝ) (hf : 0 < floor)
    (hz : |observed-p| ≤ 1) (hi : |q-p| ≤ 1) (ha : |a| ≤ A) :
    |remainderCoefficient floor p q observed a| ≤
      (A+1)/floor^2 + 1/floor^3 + (1+A)/floor := by
  have hd := denominator_lipschitz floor p q
  have hp := le_max_right p floor
  have hq := le_max_right q floor
  have hp0 := denominator_pos hf p
  have hq0 := denominator_pos hf q
  have hpsq : floor^2 ≤ denominator floor p^2 := by
    change floor^2 ≤ (max p floor)^2
    nlinarith
  have hprod : floor^3 ≤ denominator floor p^2 * denominator floor q := by
    calc
      floor^3 = floor^2*floor := by ring
      _ ≤ _ := mul_le_mul hpsq hq hf.le (sq_nonneg _)
  have hfirst : |(observed-p)*(a-(denominator floor q-denominator floor p)) /
      denominator floor p^2| ≤ (A+1)/floor^2 := by
    apply abs_div_bound _ _ _ _ (sq_pos_of_pos hf) hpsq
    rw [abs_mul]
    have hb : |a-(denominator floor q-denominator floor p)| ≤ A+1 :=
      (abs_sub _ _).trans (add_le_add ha (hd.trans hi))
    simpa only [one_mul] using mul_le_mul hz hb (abs_nonneg _) (by norm_num)
  have hsecond : |(observed-p)*(denominator floor q-denominator floor p)^2 /
      (denominator floor p^2 * denominator floor q)| ≤ 1/floor^3 := by
    apply abs_div_bound _ _ _ _ (pow_pos hf _) hprod
    rw [abs_mul, abs_pow]
    have hb : |denominator floor q-denominator floor p|^2 ≤ 1 := by
      nlinarith [abs_nonneg (denominator floor q-denominator floor p), hd.trans hi]
    simpa only [one_mul] using mul_le_mul hz hb (sq_nonneg _) (by norm_num)
  have hthird : |(q-p-a)/denominator floor q| ≤ (1+A)/floor := by
    apply abs_div_bound _ _ _ _ hf hq
    exact (abs_sub _ _).trans (add_le_add hi ha)
  exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) (le_refl _)).trans
    (add_le_add (add_le_add hfirst hsecond) hthird))

end
end QubitOracle.AdaptiveDesign.TangentGLS
