import QubitOracle.FiniteGillMassar

/-!
# Interior mixed-qubit Bures control in Bloch scalars

For a truth with squared Bloch radius `rSq`, a displacement with squared norm
`q`, and radial projection `x`, the squared qubit fidelity is

`(1 + rSq + x + sqrt ((1-rSq) (1-rSq-2x-q))) / 2`.

This file proves its local Bures loss is at most `2 q / (1-rSq)` whenever the
displaced state remains in the explicit radial neighborhood
`2 |x| + q <= 1-rSq`. The later matrix-to-Bloch fidelity identification is
kept separate.
-/

namespace QubitOracle
namespace Paper

noncomputable def qubitBlochFidelitySq
    (rSq x q : Real) : Real :=
  (1 + rSq + x + Real.sqrt ((1 - rSq) * (1 - rSq - 2 * x - q))) / 2

noncomputable def qubitBlochBuresSq
    (rSq x q : Real) : Real :=
  2 * (1 - Real.sqrt (qubitBlochFidelitySq rSq x q))

/-- Scalar interior-qubit Bures bound. The Cauchy-Schwarz hypothesis appears
as `x^2 <= rSq*q`; no matrix or asymptotic fact is assumed. -/
theorem qubitBlochBuresSq_local_upper
    (rSq x q : Real)
    (hrSq : 0 <= rSq) (hinterior : rSq < 1)
    (hq : 0 <= q) (hcauchy : x ^ 2 <= rSq * q)
    (hlocal : 2 * |x| + q <= 1 - rSq) :
    qubitBlochBuresSq rSq x q <= 2 * q / (1 - rSq) := by
  let a : Real := 1 - rSq
  let b : Real := a - 2 * x - q
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hlocal_a : 2 * |x| + q <= a := by
    simpa [a] using hlocal
  have hx_abs : |x| <= a / 2 := by
    nlinarith
  have hb : 0 <= b := by
    dsimp [b]
    have hx_le_abs : x <= |x| := le_abs_self x
    nlinarith
  have hax : 0 <= a - x := by
    have hx_le_abs : x <= |x| := le_abs_self x
    nlinarith
  let t : Real := Real.sqrt (a * b)
  have ht : 0 <= t := Real.sqrt_nonneg _
  have hab : 0 <= a * b := mul_nonneg ha.le hb
  have ht_sq : t ^ 2 = a * b := by
    dsimp [t]
    exact Real.sq_sqrt hab
  have hidentity : (a - x) ^ 2 - a * b = x ^ 2 + a * q := by
    dsimp [b]
    ring
  have ht_sq_le : t ^ 2 <= (a - x) ^ 2 := by
    have hright : 0 <= x ^ 2 + a * q :=
      add_nonneg (sq_nonneg x) (mul_nonneg ha.le hq)
    nlinarith
  have ht_le : t <= a - x :=
    (sq_le_sq₀ ht hax).1 ht_sq_le

  let F : Real := (1 + rSq + x + t) / 2
  have hradius_gap : rSq + a = 1 := by
    dsimp [a]
    ring
  have ha_le_one : a <= 1 := by
    dsimp [a]
    linarith
  have hF_nonnegative : 0 <= F := by
    dsimp [F]
    have hneg_abs : -|x| <= x := neg_abs_le x
    nlinarith
  have hF_le_one : F <= 1 := by
    dsimp [F]
    nlinarith
  have hsqrtF : 0 <= Real.sqrt F := Real.sqrt_nonneg _
  have hsqrtF_sq : (Real.sqrt F) ^ 2 = F :=
    Real.sq_sqrt hF_nonnegative
  have hsqrtF_le_one : Real.sqrt F <= 1 := by
    apply (sq_le_sq₀ hsqrtF (by norm_num)).1
    simpa [hsqrtF_sq] using hF_le_one
  have hF_le_sqrtF : F <= Real.sqrt F := by
    nlinarith
  have hroot_loss :
      2 * (1 - Real.sqrt F) <= 2 * (1 - F) := by
    nlinarith

  have hnumerator_nonnegative : 0 <= a - x - t := by
    linarith
  have hdenominator_lower : a / 2 <= a - x + t := by
    have hx_le_abs : x <= |x| := le_abs_self x
    nlinarith
  have hproduct_identity :
      (a - x - t) * (a - x + t) = x ^ 2 + a * q := by
    calc
      (a - x - t) * (a - x + t) = (a - x) ^ 2 - t ^ 2 := by ring
      _ = (a - x) ^ 2 - a * b := by rw [ht_sq]
      _ = x ^ 2 + a * q := hidentity
  have hcauchy_gap : x ^ 2 + a * q <= q := by
    calc
      x ^ 2 + a * q <= rSq * q + a * q :=
        add_le_add hcauchy (le_refl _)
      _ = q := by rw [← add_mul, hradius_gap, one_mul]
  have hhalf_product : (a - x - t) * (a / 2) <= q := by
    calc
      (a - x - t) * (a / 2) <=
          (a - x - t) * (a - x + t) :=
        mul_le_mul_of_nonneg_left hdenominator_lower
          hnumerator_nonnegative
      _ = x ^ 2 + a * q := hproduct_identity
      _ <= q := hcauchy_gap
  have hnumerator_bound : a - x - t <= 2 * q / a := by
    apply (le_div_iff₀ ha).2
    nlinarith
  have hbures_le_numerator :
      2 * (1 - Real.sqrt F) <= a - x - t := by
    calc
      2 * (1 - Real.sqrt F) <= 2 * (1 - F) := hroot_loss
      _ = a - x - t := by
        dsimp [F]
        nlinarith
  have hfinal := hbures_le_numerator.trans hnumerator_bound
  simpa [qubitBlochBuresSq, qubitBlochFidelitySq, F, t, b, a] using hfinal

/-- Coordinate form obtained by substituting the actual Bloch truth and
displacement. -/
noncomputable def mixedBlochBuresSq
    (theta delta : Fin 3 -> Real) : Real :=
  qubitBlochBuresSq (blochNormSq theta)
    (blochDot theta delta) (blochNormSq delta)

theorem mixedBlochBuresSq_local_upper
    (theta delta : Fin 3 -> Real)
    (hinterior : blochNormSq theta < 1)
    (hlocal :
      2 * |blochDot theta delta| + blochNormSq delta <=
        1 - blochNormSq theta) :
    mixedBlochBuresSq theta delta <=
      2 * blochNormSq delta / (1 - blochNormSq theta) := by
  apply qubitBlochBuresSq_local_upper
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact hinterior
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact bloch_cauchy_schwarz theta delta
  · exact hlocal

theorem blochNormSq_smul
    (a : Real) (h : Fin 3 -> Real) :
    blochNormSq (a • h) = a ^ 2 * blochNormSq h := by
  simp only [blochNormSq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Compact-radius consequence under the local scaling `a^2 = 1/n`. -/
theorem mixedBlochBuresSq_compact_upper
    (shots : Nat) (hshots : 0 < shots)
    (a : Real) (theta h : Fin 3 -> Real) (R : Real)
    (hinterior : blochNormSq theta < 1)
    (hR : 0 <= R) (hradius : blochNormSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hlocal :
      2 * |blochDot theta (a • h)| + blochNormSq (a • h) <=
        1 - blochNormSq theta) :
    mixedBlochBuresSq theta (a • h) <=
      (2 * R / (1 - blochNormSq theta)) / (shots : Real) := by
  have hshotsReal : 0 < (shots : Real) := by exact_mod_cast hshots
  have hinv_nonnegative : 0 <= ((shots : Real))⁻¹ :=
    inv_nonneg.mpr hshotsReal.le
  have hgap : 0 < 1 - blochNormSq theta := by linarith
  have hqbound :
      blochNormSq (a • h) <= ((shots : Real))⁻¹ * R := by
    rw [blochNormSq_smul, ha]
    exact mul_le_mul_of_nonneg_left hradius hinv_nonnegative
  calc
    mixedBlochBuresSq theta (a • h) <=
        2 * blochNormSq (a • h) / (1 - blochNormSq theta) :=
      mixedBlochBuresSq_local_upper theta (a • h) hinterior hlocal
    _ <= 2 * (((shots : Real))⁻¹ * R) /
        (1 - blochNormSq theta) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqbound (by norm_num)) hgap.le
    _ = (2 * R / (1 - blochNormSq theta)) / (shots : Real) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

end Paper
end QubitOracle
