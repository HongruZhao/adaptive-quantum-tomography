import QubitOracle.Paper.MixedAxisFisher

/-!
# Uniform stability of mixed-qubit stage information

The eigendirections chosen by an oracle design need not converge when eigenvalues
coalesce.  This file avoids that false requirement: on an interior Bloch ball,
the one-axis Fisher matrix is uniformly continuous in the state, uniformly over
all unit axes.  Consequently any changing finite probability mixture of unit
axes has the same information limit whether evaluated at a consistent
controller or at the truth.
-/

namespace QubitOracle
namespace Paper

open Filter
open scoped BigOperators Topology

/-- Squared Bloch norm is continuous in the product topology. -/
theorem continuous_blochNormSq :
    Continuous (blochNormSq : (Fin 3 -> Real) -> Real) := by
  unfold blochNormSq
  fun_prop

/-- Every coordinate of a unit Bloch axis has absolute value at most one. -/
theorem unitAxis_abs_le_one (u : Fin 3 -> Real)
    (hu : blochNormSq u = 1) (i : Fin 3) :
    |u i| <= 1 := by
  have hsingle : (u i) ^ 2 <= ∑ j, (u j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (u j))
      (Finset.mem_univ i)
  have hsq : (u i) ^ 2 <= 1 := by
    simpa [blochNormSq] using hsingle.trans_eq hu
  nlinarith [abs_nonneg (u i), sq_abs (u i)]

/-- A dimension-three bound uniform over unit axes. -/
theorem blochDot_sub_abs_le_three_norm
    (r s u : Fin 3 -> Real) (hu : blochNormSq u = 1) :
    |blochDot r u - blochDot s u| <= 3 * ‖r - s‖ := by
  have hucoord : ∀ i, |u i| <= 1 := fun i =>
    unitAxis_abs_le_one u hu i
  have hdot :
      blochDot r u - blochDot s u =
        ∑ i, (r - s) i * u i := by
    unfold blochDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    ring
  rw [hdot]
  calc
    |∑ i, (r - s) i * u i| <=
        ∑ i, |(r - s) i * u i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ i, |(r - s) i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_of_le_one_right
        (abs_nonneg ((r - s) i)) (hucoord i)
    _ = ∑ i, ‖(r - s) i‖ := by
      simp [Real.norm_eq_abs]
    _ <= 3 * ‖r - s‖ := by
      simpa using (Pi.sum_norm_apply_le_norm (r - s))

/-- Stability of `x ↦ (1-x^2)⁻¹` on a common positive denominator gap. -/
theorem inverse_one_sub_sq_sub_abs_le
    (x y gamma e : Real)
    (hgamma : 0 < gamma)
    (hxabs : |x| <= 1) (hyabs : |y| <= 1)
    (hdenx : gamma <= 1 - x ^ 2)
    (hdeny : gamma <= 1 - y ^ 2)
    (he : 0 <= e) (hdiff : |x - y| <= e) :
    |(1 - x ^ 2)⁻¹ - (1 - y ^ 2)⁻¹| <=
      (2 * e) / gamma ^ 2 := by
  have hax : 0 < 1 - x ^ 2 := hgamma.trans_le hdenx
  have hay : 0 < 1 - y ^ 2 := hgamma.trans_le hdeny
  have hsum : |x + y| <= 2 := by
    calc
      |x + y| <= |x| + |y| := abs_add_le x y
      _ <= 2 := by linarith
  have hnum : |(1 - y ^ 2) - (1 - x ^ 2)| <= 2 * e := by
    calc
      |(1 - y ^ 2) - (1 - x ^ 2)| =
          |x ^ 2 - y ^ 2| := by
        congr 1
        ring
      _ = |x - y| * |x + y| := by
        rw [show x ^ 2 - y ^ 2 =
          (x - y) * (x + y) by ring, abs_mul]
      _ <= e * 2 :=
        mul_le_mul hdiff hsum (abs_nonneg _) he
      _ = 2 * e := by ring
  have hden : gamma ^ 2 <=
      (1 - x ^ 2) * (1 - y ^ 2) := by
    rw [pow_two]
    exact mul_le_mul hdenx hdeny hgamma.le hax.le
  rw [inv_sub_inv hax.ne' hay.ne', abs_div, abs_mul,
    abs_of_pos hax, abs_of_pos hay]
  exact div_le_div₀
    (mul_nonneg (by norm_num) he) hnum
    (sq_pos_of_pos hgamma) hden

/-- A squared-norm gap yields the same denominator gap for every unit axis. -/
theorem mixedAxis_denominator_ge_of_normSq_le
    (r u : Fin 3 -> Real) (gamma : Real)
    (hr : blochNormSq r <= 1 - gamma)
    (hu : blochNormSq u = 1) :
    gamma <= 1 - blochDot r u ^ 2 := by
  have hcs := bloch_cauchy_schwarz r u
  rw [hu, mul_one] at hcs
  linarith

/-- Entrywise Fisher stability, uniform over all unit axes. -/
theorem mixedAxisFisher_entry_sub_abs_le_of_gap
    (r s u : Fin 3 -> Real) (gamma : Real)
    (hgamma : 0 < gamma)
    (hr : blochNormSq r <= 1 - gamma)
    (hs : blochNormSq s <= 1 - gamma)
    (hu : blochNormSq u = 1) (i j : Fin 3) :
    |mixedAxisFisher r u i j - mixedAxisFisher s u i j| <=
      (6 * ‖r - s‖) / gamma ^ 2 := by
  have hdenr := mixedAxis_denominator_ge_of_normSq_le r u gamma hr hu
  have hdens := mixedAxis_denominator_ge_of_normSq_le s u gamma hs hu
  have hxr : 0 < 1 - blochDot r u ^ 2 := hgamma.trans_le hdenr
  have hxs : 0 < 1 - blochDot s u ^ 2 := hgamma.trans_le hdens
  have hxrabs : |blochDot r u| <= 1 := by
    nlinarith [abs_nonneg (blochDot r u), sq_abs (blochDot r u)]
  have hxsabs : |blochDot s u| <= 1 := by
    nlinarith [abs_nonneg (blochDot s u), sq_abs (blochDot s u)]
  have hnorm : 0 <= 3 * ‖r - s‖ :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  have hinv := inverse_one_sub_sq_sub_abs_le
    (blochDot r u) (blochDot s u) gamma (3 * ‖r - s‖)
    hgamma hxrabs hxsabs hdenr hdens hnorm
    (blochDot_sub_abs_le_three_norm r s u hu)
  have hui := unitAxis_abs_le_one u hu i
  have huj := unitAxis_abs_le_one u hu j
  have houter : |u i * u j| <= 1 := by
    rw [abs_mul]
    calc
      |u i| * |u j| <= |u i| * 1 :=
        mul_le_mul_of_nonneg_left huj (abs_nonneg _)
      _ <= 1 * 1 :=
        mul_le_mul_of_nonneg_right hui (by norm_num)
      _ = 1 := by ring
  have hboundnonneg :
      0 <= (2 * (3 * ‖r - s‖)) / gamma ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) hnorm) (sq_nonneg _)
  change
    |(1 - blochDot r u ^ 2)⁻¹ * (u i * u j) -
      (1 - blochDot s u ^ 2)⁻¹ * (u i * u j)| <= _
  rw [← sub_mul, abs_mul]
  calc
    |(1 - blochDot r u ^ 2)⁻¹ -
        (1 - blochDot s u ^ 2)⁻¹| * |u i * u j| <=
        ((2 * (3 * ‖r - s‖)) / gamma ^ 2) * |u i * u j| :=
      mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
    _ <= ((2 * (3 * ‖r - s‖)) / gamma ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left houter hboundnonneg
    _ = (6 * ‖r - s‖) / gamma ^ 2 := by ring

/-- Fisher information of one finite adaptive design stage. -/
noncomputable def mixedStageInformation
    {M : Type*} [Fintype M]
    (r : Fin 3 -> Real) (mass : M -> Real)
    (axis : M -> Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  ∑ m, mass m • mixedAxisFisher r (axis m)

/-- The one-axis stability bound survives arbitrary changing probability
mixtures. -/
theorem mixedStageInformation_entry_sub_abs_le_of_gap
    {M : Type*} [Fintype M]
    (r s : Fin 3 -> Real) (mass : M -> Real)
    (axis : M -> Fin 3 -> Real) (gamma : Real)
    (hgamma : 0 < gamma)
    (hr : blochNormSq r <= 1 - gamma)
    (hs : blochNormSq s <= 1 - gamma)
    (hmass : ∀ m, 0 <= mass m)
    (hmassSum : ∑ m, mass m = 1)
    (haxis : ∀ m, blochNormSq (axis m) = 1)
    (i j : Fin 3) :
    |mixedStageInformation r mass axis i j -
      mixedStageInformation s mass axis i j| <=
      (6 * ‖r - s‖) / gamma ^ 2 := by
  simp only [mixedStageInformation, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ m, (mass m * mixedAxisFisher r (axis m) i j -
        mass m * mixedAxisFisher s (axis m) i j)| =
        |∑ m, mass m *
          (mixedAxisFisher r (axis m) i j -
           mixedAxisFisher s (axis m) i j)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ <= ∑ m, |mass m *
          (mixedAxisFisher r (axis m) i j -
           mixedAxisFisher s (axis m) i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m, mass m *
          |mixedAxisFisher r (axis m) i j -
           mixedAxisFisher s (axis m) i j| := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [abs_mul, abs_of_nonneg (hmass m)]
    _ <= ∑ m, mass m * ((6 * ‖r - s‖) / gamma ^ 2) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (mixedAxisFisher_entry_sub_abs_le_of_gap
          r s (axis m) gamma hgamma hr hs (haxis m) i j)
        (hmass m)
    _ = (6 * ‖r - s‖) / gamma ^ 2 := by
      rw [← Finset.sum_mul, hmassSum, one_mul]

/-- A consistent controller is eventually inside a fixed ball strictly
containing the truth. -/
theorem eventually_controller_normSq_le_interiorGap
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta)) :
    ∀ᶠ n in atTop,
      blochNormSq (controller n) <=
        1 - (1 - blochNormSq theta) / 2 := by
  have hnorm : Tendsto (fun n => blochNormSq (controller n))
      atTop (nhds (blochNormSq theta)) :=
    continuous_blochNormSq.continuousAt.tendsto.comp hcontroller
  have hstrict : blochNormSq theta <
      1 - (1 - blochNormSq theta) / 2 := by linarith
  filter_upwards [(tendsto_order.1 hnorm).2 _ hstrict] with n hn
  exact hn.le

/-- Uniform mixed-stage stability along any consistent interior controller.
No convergence of the changing measurement axes is assumed. -/
theorem mixedStageInformation_truth_sub_controller_tendsto_zero
    {M : Type*} [Fintype M]
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (mass : Nat -> M -> Real)
    (axis : Nat -> M -> Fin 3 -> Real)
    (hmass : ∀ n m, 0 <= mass n m)
    (hmassSum : ∀ n, ∑ m, mass n m = 1)
    (haxis : ∀ n m, blochNormSq (axis n m) = 1) :
    Tendsto
      (fun n => mixedStageInformation theta (mass n) (axis n) -
        mixedStageInformation (controller n) (mass n) (axis n))
      atTop (nhds 0) := by
  let gamma : Real := (1 - blochNormSq theta) / 2
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hthetaGap : blochNormSq theta <= 1 - gamma := by
    dsimp [gamma]
    linarith
  have hcontrollerGap : ∀ᶠ n in atTop,
      blochNormSq (controller n) <= 1 - gamma := by
    simpa [gamma] using
      eventually_controller_normSq_le_interiorGap
        theta htheta controller hcontroller
  have hnorm : Tendsto (fun n => ‖theta - controller n‖)
      atTop (nhds 0) := by
    simpa using (hcontroller.const_sub theta).norm
  have hbound : Tendsto
      (fun n => (6 * ‖theta - controller n‖) / gamma ^ 2)
      atTop (nhds 0) := by
    simpa using (hnorm.const_mul 6).div_const (gamma ^ 2)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => abs_nonneg _
  · filter_upwards [hcontrollerGap] with n hn
    exact mixedStageInformation_entry_sub_abs_le_of_gap
      theta (controller n) (mass n) (axis n) gamma hgamma
      hthetaGap hn (hmass n) (hmassSum n) (haxis n) i j
  · simpa [Function.comp_def] using hbound

/-- If the controller-evaluated stage information has a limit, then the same
stage design evaluated at the true state has that limit. -/
theorem mixedStageInformation_tendsto_of_controller
    {M : Type*} [Fintype M]
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (mass : Nat -> M -> Real)
    (axis : Nat -> M -> Fin 3 -> Real)
    (hmass : ∀ n m, 0 <= mass n m)
    (hmassSum : ∀ n, ∑ m, mass n m = 1)
    (haxis : ∀ n m, blochNormSq (axis n m) = 1)
    (target : Matrix (Fin 3) (Fin 3) Real)
    (hstage : Tendsto
      (fun n => mixedStageInformation (controller n) (mass n) (axis n))
      atTop (nhds target)) :
    Tendsto
      (fun n => mixedStageInformation theta (mass n) (axis n))
      atTop (nhds target) := by
  have herror := mixedStageInformation_truth_sub_controller_tendsto_zero
    theta htheta controller hcontroller mass axis hmass hmassSum haxis
  have hadd := herror.add hstage
  simpa [sub_add_cancel] using hadd

/-- Concrete sufficient condition used by an oracle controller: exact
controller-stage realization of a target map continuous at the truth. -/
theorem mixedStageInformation_tendsto_of_exact_continuous_target
    {M : Type*} [Fintype M]
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (mass : Nat -> M -> Real)
    (axis : Nat -> M -> Fin 3 -> Real)
    (hmass : ∀ n m, 0 <= mass n m)
    (hmassSum : ∀ n, ∑ m, mass n m = 1)
    (haxis : ∀ n m, blochNormSq (axis n m) = 1)
    (targetMap : (Fin 3 -> Real) -> Matrix (Fin 3) (Fin 3) Real)
    (htarget : ContinuousAt targetMap theta)
    (hexact : ∀ n,
      mixedStageInformation (controller n) (mass n) (axis n) =
        targetMap (controller n)) :
    Tendsto
      (fun n => mixedStageInformation theta (mass n) (axis n))
      atTop (nhds (targetMap theta)) := by
  apply mixedStageInformation_tendsto_of_controller
    theta htheta controller hcontroller mass axis hmass hmassSum haxis
      (targetMap theta)
  convert htarget.tendsto.comp hcontroller using 1
  funext n
  exact hexact n

end Paper
end QubitOracle
