import QubitOracle.Paper.MixedStageStability

/-!
# Continuous rotationally invariant mixed-qubit oracle targets

The radial/tangent formula in the manuscript contains a normalized radial
projector and therefore appears singular at the maximally mixed state.  The
definitions below use algebraically equivalent center-safe formulas.  They
make continuity on the whole open Bloch ball explicit.
-/

namespace QubitOracle
namespace Paper

open scoped Topology

/-- `sqrt (1-||r||^2)`, denoted `q` in the manuscript's mixed-state table. -/
noncomputable def mixedRadialGap (r : Fin 3 -> Real) : Real :=
  Real.sqrt (1 - blochNormSq r)

/-- Each of the two tangent/coherence allocations for Frobenius and squared
trace loss. -/
noncomputable def mixedCoherenceAllocation (r : Fin 3 -> Real) : Real :=
  (2 + mixedRadialGap r)⁻¹

/-- The radial/eigenaxis allocation for Frobenius and squared trace loss. -/
noncomputable def mixedRadialAllocation (r : Fin 3 -> Real) : Real :=
  mixedRadialGap r / (2 + mixedRadialGap r)

/-- The center-safe Frobenius/trace optimal information target.
For nonzero `r`, this equals
`a (I-P_r) + b/(1-||r||^2) P_r`. -/
noncomputable def mixedFrobeniusTraceTarget
    (r : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  let q := mixedRadialGap r
  (2 + q)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) Real) +
    (q * (2 + q) * (1 + q))⁻¹ • blochOuter r

/-- The center-safe Bures optimal information target. -/
noncomputable def mixedBuresTarget
    (r : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  (1 / 3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) +
    (3 * (1 - blochNormSq r))⁻¹ • blochOuter r

/-- Radial rank-one projector away from the maximally mixed state. -/
noncomputable def mixedRadialProjector
    (r : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  (blochNormSq r)⁻¹ • blochOuter r

/-- Tangent-plane projector away from the maximally mixed state. -/
noncomputable def mixedTangentProjector
    (r : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  1 - mixedRadialProjector r

/-- The radial gap is continuous, including at the boundary. -/
theorem continuous_mixedRadialGap : Continuous mixedRadialGap := by
  unfold mixedRadialGap
  simpa [Function.comp_def] using
    Real.continuous_sqrt.comp
      (continuous_const.sub continuous_blochNormSq)

/-- The rank-one Bloch outer-product map is continuous. -/
theorem continuous_blochOuter :
    Continuous (blochOuter :
      (Fin 3 -> Real) -> Matrix (Fin 3) (Fin 3) Real) := by
  unfold blochOuter
  fun_prop

/-- The radial gap is positive at every interior mixed state. -/
theorem mixedRadialGap_pos
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    0 < mixedRadialGap r := by
  exact Real.sqrt_pos.2 (sub_pos.mpr hr)

/-- The Frobenius/trace allocations are nonnegative in the interior. -/
theorem mixedCoherenceAllocation_pos
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    0 < mixedCoherenceAllocation r := by
  unfold mixedCoherenceAllocation
  exact inv_pos.2 (by positivity [mixedRadialGap_pos r hr])

theorem mixedRadialAllocation_pos
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    0 < mixedRadialAllocation r := by
  unfold mixedRadialAllocation
  exact div_pos (mixedRadialGap_pos r hr)
    (by positivity [mixedRadialGap_pos r hr])

/-- The three Frobenius/trace allocations exactly exhaust one copy. -/
theorem mixedAllocations_sum
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    2 * mixedCoherenceAllocation r + mixedRadialAllocation r = 1 := by
  have hden : 2 + mixedRadialGap r ≠ 0 := by
    positivity [mixedRadialGap_pos r hr]
  unfold mixedCoherenceAllocation mixedRadialAllocation
  field_simp [hden]

/-- Scalar identity converting the center-safe Frobenius/trace target to the
radial/tangent form printed in the manuscript. -/
theorem mixedFrobenius_radialCoefficient_eq
    (r : Fin 3 -> Real)
    (hr0 : 0 < blochNormSq r) (hr1 : blochNormSq r < 1) :
    (mixedRadialGap r * (2 + mixedRadialGap r) *
      (1 + mixedRadialGap r))⁻¹ =
      (mixedRadialAllocation r / (1 - blochNormSq r) -
        mixedCoherenceAllocation r) / blochNormSq r := by
  have hq : 0 < mixedRadialGap r := mixedRadialGap_pos r hr1
  have hqSq : mixedRadialGap r ^ 2 = 1 - blochNormSq r := by
    unfold mixedRadialGap
    exact Real.sq_sqrt (sub_nonneg.mpr hr1.le)
  have htwo : 2 + mixedRadialGap r ≠ 0 := by positivity
  have hone : 1 + mixedRadialGap r ≠ 0 := by positivity
  have hgap : 1 - blochNormSq r ≠ 0 := by linarith
  have hnorm : blochNormSq r ≠ 0 := hr0.ne'
  unfold mixedRadialAllocation mixedCoherenceAllocation
  field_simp [hq.ne', htwo, hone, hgap, hnorm]
  nlinarith

/-- Scalar identity converting the center-safe Bures target to the
radial/tangent form printed in the manuscript. -/
theorem mixedBures_radialCoefficient_eq
    (r : Fin 3 -> Real)
    (hr0 : 0 < blochNormSq r) (hr1 : blochNormSq r < 1) :
    (3 * (1 - blochNormSq r))⁻¹ =
      (((1 / 3 : Real) / (1 - blochNormSq r)) - (1 / 3 : Real)) /
        blochNormSq r := by
  have hgap : 1 - blochNormSq r ≠ 0 := by linarith
  have hnorm : blochNormSq r ≠ 0 := hr0.ne'
  field_simp [hgap, hnorm]
  ring

/-- Exact equality between the center-safe and paper radial/tangent formulas
for Frobenius and squared trace loss. -/
theorem mixedFrobeniusTraceTarget_eq_radialTangent
    (r : Fin 3 -> Real)
    (hr0 : 0 < blochNormSq r) (hr1 : blochNormSq r < 1) :
    mixedFrobeniusTraceTarget r =
      mixedCoherenceAllocation r • mixedTangentProjector r +
      (mixedRadialAllocation r / (1 - blochNormSq r)) •
        mixedRadialProjector r := by
  have hcoeff := mixedFrobenius_radialCoefficient_eq r hr0 hr1
  unfold mixedFrobeniusTraceTarget mixedTangentProjector
    mixedRadialProjector mixedCoherenceAllocation
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hcoeff]
  unfold mixedCoherenceAllocation
  ring

/-- Exact equality between the center-safe and paper radial/tangent formulas
for squared Bures loss. -/
theorem mixedBuresTarget_eq_radialTangent
    (r : Fin 3 -> Real)
    (hr0 : 0 < blochNormSq r) (hr1 : blochNormSq r < 1) :
    mixedBuresTarget r =
      (1 / 3 : Real) • mixedTangentProjector r +
      ((1 / 3 : Real) / (1 - blochNormSq r)) •
        mixedRadialProjector r := by
  have hcoeff := mixedBures_radialCoefficient_eq r hr0 hr1
  unfold mixedBuresTarget mixedTangentProjector mixedRadialProjector
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hcoeff]
  ring

/-- The Frobenius/trace target is continuous at every interior state,
including the maximally mixed state. -/
theorem continuousAt_mixedFrobeniusTraceTarget
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    ContinuousAt mixedFrobeniusTraceTarget r := by
  have hgap : 0 < 1 - blochNormSq r := sub_pos.mpr hr
  have hq : 0 < mixedRadialGap r := mixedRadialGap_pos r hr
  have htwo : 2 + mixedRadialGap r ≠ 0 := by positivity
  have hone : 1 + mixedRadialGap r ≠ 0 := by positivity
  have hprod :
      mixedRadialGap r * (2 + mixedRadialGap r) *
        (1 + mixedRadialGap r) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hq.ne' htwo) hone
  have hqcont : ContinuousAt mixedRadialGap r :=
    continuous_mixedRadialGap.continuousAt
  have htwocont : ContinuousAt
      (fun x => 2 + mixedRadialGap x) r :=
    continuousAt_const.add hqcont
  have honecont : ContinuousAt
      (fun x => 1 + mixedRadialGap x) r :=
    continuousAt_const.add hqcont
  have hprodcont : ContinuousAt
      (fun x => mixedRadialGap x * (2 + mixedRadialGap x) *
        (1 + mixedRadialGap x)) r :=
    (hqcont.mul htwocont).mul honecont
  unfold mixedFrobeniusTraceTarget
  exact (htwocont.inv₀ htwo).smul continuousAt_const |>.add
    ((hprodcont.inv₀ hprod).smul continuous_blochOuter.continuousAt)

/-- The Bures target is continuous at every interior state, including the
maximally mixed state. -/
theorem continuousAt_mixedBuresTarget
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1) :
    ContinuousAt mixedBuresTarget r := by
  have hden : 3 * (1 - blochNormSq r) ≠ 0 := by
    positivity
  have hdencont : ContinuousAt
      (fun x => 3 * (1 - blochNormSq x)) r :=
    continuousAt_const.mul
      (continuousAt_const.sub continuous_blochNormSq.continuousAt)
  have hconst : ContinuousAt
      (fun _ : Fin 3 -> Real => (1 / 3 : Real)) r :=
    continuousAt_const
  have honeMatrix : ContinuousAt
      (fun _ : Fin 3 -> Real =>
        (1 : Matrix (Fin 3) (Fin 3) Real)) r :=
    continuousAt_const
  unfold mixedBuresTarget
  exact (hconst.smul honeMatrix).add
    ((hdencont.inv₀ hden).smul continuous_blochOuter.continuousAt)

end Paper
end QubitOracle
