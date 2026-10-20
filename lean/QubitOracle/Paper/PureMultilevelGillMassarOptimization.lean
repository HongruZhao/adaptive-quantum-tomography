import Mathlib

/-!
# Scalar optimization after the Gill--Massar trace bound

For `2 * d` positive real eigenvalues with total mass at most `d`, the sum of
their reciprocals is at least `4 * d`.  The proof is elementary: the tangent
line to `x \mapsto 1 / x` at `x = 1 / 2` gives

`1 / x >= 4 - 4 * x`.

Summing this inequality gives the claimed lower bound.  The constant spectrum
with every eigenvalue equal to `1 / 2` is feasible and attains equality.
-/

namespace QubitOracle.Paper
namespace PureMultilevelGillMassarOptimization

open scoped BigOperators

/-- The supporting-line inequality for the reciprocal function at `1 / 2`. -/
theorem reciprocal_tangent_at_half {x : Real} (hx : 0 < x) :
    (4 : Real) - 4 * x <= 1 / x := by
  rw [le_div_iff₀ hx]
  nlinarith [sq_nonneg (2 * x - 1)]

/-- Scalar Gill--Massar optimization.  If `2 * d` positive eigenvalues have
sum at most `d`, then the sum of their reciprocals is at least `4 * d`. -/
theorem reciprocal_sum_ge_four_mul
    (d : Nat) (eigenvalue : Fin (2 * d) -> Real)
    (hpositive : forall i, 0 < eigenvalue i)
    (hsum : (∑ i, eigenvalue i) <= (d : Real)) :
    (4 : Real) * d <= ∑ i, 1 / eigenvalue i := by
  have hpointwise : forall i : Fin (2 * d),
      (4 : Real) - 4 * eigenvalue i <= 1 / eigenvalue i := by
    intro i
    exact reciprocal_tangent_at_half (hpositive i)
  have hsummed :
      (∑ i, ((4 : Real) - 4 * eigenvalue i)) <=
        ∑ i, 1 / eigenvalue i := by
    exact Finset.sum_le_sum fun i _ => hpointwise i
  have hevaluate :
      (∑ i, ((4 : Real) - 4 * eigenvalue i)) =
        (8 : Real) * d - 4 * ∑ i, eigenvalue i := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, Nat.cast_mul]
    ring
  rw [hevaluate] at hsummed
  nlinarith

/-- Every entry of the constant half-spectrum is strictly positive. -/
theorem half_eigenvalues_positive (d : Nat) :
    forall _i : Fin (2 * d), 0 < (1 / 2 : Real) := by
  intro _i
  norm_num

/-- The `2 * d` constant eigenvalues `1 / 2` saturate the mass budget `d`. -/
theorem half_eigenvalues_sum_eq (d : Nat) :
    (∑ _i : Fin (2 * d), (1 / 2 : Real)) = (d : Real) := by
  simp [Nat.cast_mul]
  ring

/-- The reciprocal sum of the constant half-spectrum is exactly `4 * d`. -/
theorem half_eigenvalues_reciprocal_sum_eq (d : Nat) :
    (∑ _i : Fin (2 * d), 1 / (1 / 2 : Real)) = (4 : Real) * d := by
  simp [Nat.cast_mul]
  ring

/-- The constant half-spectrum is feasible and attains the lower bound. -/
theorem half_eigenvalues_attain_bound (d : Nat) :
    (forall _i : Fin (2 * d), 0 < (1 / 2 : Real)) ∧
      (∑ _i : Fin (2 * d), (1 / 2 : Real)) <= (d : Real) ∧
      (∑ _i : Fin (2 * d), 1 / (1 / 2 : Real)) = (4 : Real) * d := by
  refine ⟨half_eigenvalues_positive d, ?_,
    half_eigenvalues_reciprocal_sum_eq d⟩
  exact (half_eigenvalues_sum_eq d).le

end PureMultilevelGillMassarOptimization
end QubitOracle.Paper
