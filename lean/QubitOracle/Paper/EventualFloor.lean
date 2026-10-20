import Mathlib

/-!
# Eventual inactivity of an interior eigenvalue floor

This module proves the deterministic convergence argument in Supplementary
Note 6 for an arbitrary finite- or infinite-dimensional real normed space.
-/

namespace QubitOracle
namespace Paper

open Filter Topology

/-- A convergent interior sequence eventually lies inside any controller ball
whose radial floor vanishes. -/
theorem eventually_inside_vanishing_floor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (xStar : E) (eta : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 xStar))
    (heta : Tendsto eta atTop (𝓝 0))
    (hinterior : ‖xStar‖ < 1) :
    ∀ᶠ n in atTop, ‖x n‖ < 1 - 2 * eta n := by
  have hnorm : Tendsto (fun n => ‖x n‖) atTop (𝓝 ‖xStar‖) :=
    (continuous_norm.tendsto xStar).comp hx
  have htwo : Tendsto (fun n => (2 : ℝ) * eta n) atTop (𝓝 ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul heta
  have hsum : Tendsto (fun n => ‖x n‖ + 2 * eta n)
      atTop (𝓝 ‖xStar‖) := by
    simpa using hnorm.add htwo
  filter_upwards [hsum.eventually (Iio_mem_nhds hinterior)] with n hn
  linarith

/-- Any projection-like safeguard that fixes strict interior points is
eventually inactive under the preceding hypotheses. -/
theorem eventually_floor_projection_inactive
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (project : ℝ → E → E)
    (fixesInterior : ∀ r z, ‖z‖ < r → project r z = z)
    (x : ℕ → E) (xStar : E) (eta : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 xStar))
    (heta : Tendsto eta atTop (𝓝 0))
    (hinterior : ‖xStar‖ < 1) :
    ∀ᶠ n in atTop, project (1 - 2 * eta n) (x n) = x n := by
  filter_upwards [eventually_inside_vanishing_floor x xStar eta hx heta hinterior]
    with n hn
  exact fixesInterior (1 - 2 * eta n) (x n) hn

end Paper
end QubitOracle
