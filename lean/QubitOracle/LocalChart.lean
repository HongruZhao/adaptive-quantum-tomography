import Mathlib
/-!
# Normalized directional paths

This file verifies the one-variable calculus used to differentiate the
rank-one local chart at its reference point.  The definitions are exact; the
probability derivatives used later are not postulated.
-/

namespace QubitOracle

noncomputable section

/-- The reference-coordinate amplitude along a normalized directional path. -/
def radial (t : ℝ) : ℝ :=
  Real.sqrt (1 - t ^ 2 / 4)

/-- The derivative of the reference-coordinate amplitude vanishes at zero. -/
lemma hasDerivAt_radial_zero : HasDerivAt radial 0 0 := by
  have hinner : HasDerivAt (fun t : ℝ => 1 - t ^ 2 / 4) 0 0 := by
    have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
      hasDerivAt_const (x := 0) (c := 1)
    have hp : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
      convert (hasDerivAt_id (x := (0 : ℝ))).pow 2 using 1
      all_goals first | rfl | norm_num
    have hd : HasDerivAt (fun t : ℝ => t ^ 2 / 4) 0 0 := by
      simpa using hp.div_const 4
    convert hc.sub hd using 1
    all_goals first | rfl | norm_num
  change HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2 / 4)) 0 0
  simpa using hinner.sqrt (by norm_num)

/-- A Born probability when the varied coordinate is in phase with the
reference amplitude. -/
def activeProbability (w0 w t : ℝ) : ℝ :=
  (w0 * radial t + (t / 2) * w) ^ 2

/-- A Born probability when the varied coordinate is in quadrature with the
reference amplitude. -/
def inactiveProbability (w0 w t : ℝ) : ℝ :=
  (w0 * radial t) ^ 2 + ((t / 2) * w) ^ 2

/-- Exact derivative of an active-coordinate probability at the chart origin. -/
lemma hasDerivAt_activeProbability_zero (w0 w : ℝ) :
    HasDerivAt (activeProbability w0 w) (w0 * w) 0 := by
  have hamp :
      HasDerivAt (fun t : ℝ => w0 * radial t + (t / 2) * w) (w / 2) 0 := by
    have h₁ : HasDerivAt (fun t : ℝ => w0 * radial t) 0 0 := by
      simpa using hasDerivAt_radial_zero.const_mul w0
    have h₂ : HasDerivAt (fun t : ℝ => (t / 2) * w) (w / 2) 0 := by
      convert ((hasDerivAt_id (x := (0 : ℝ))).div_const 2 |>.mul_const w) using 1
      all_goals first | rfl | ring
    convert h₁.add h₂ using 1
    all_goals first | rfl | ring
  change HasDerivAt
    (fun t : ℝ => (w0 * radial t + t / 2 * w) ^ 2) (w0 * w) 0
  convert hamp.pow 2 using 1
  all_goals try rfl
  norm_num [radial]
  ring

/-- Exact derivative of an inactive-coordinate probability at the chart origin. -/
lemma hasDerivAt_inactiveProbability_zero (w0 w : ℝ) :
    HasDerivAt (inactiveProbability w0 w) 0 0 := by
  have h₁ : HasDerivAt (fun t : ℝ => w0 * radial t) 0 0 := by
    simpa using hasDerivAt_radial_zero.const_mul w0
  have h₂ : HasDerivAt (fun t : ℝ => (t / 2) * w) (w / 2) 0 := by
    convert ((hasDerivAt_id (x := (0 : ℝ))).div_const 2 |>.mul_const w) using 1
    all_goals first | rfl | ring
  change HasDerivAt
    (fun t : ℝ => (w0 * radial t) ^ 2 + (t / 2 * w) ^ 2) 0 0
  convert (h₁.pow 2).add (h₂.pow 2) using 1
  all_goals try rfl
  norm_num [radial]

end

end QubitOracle
