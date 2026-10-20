import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# A finite-dimensional Cramer-Wold bridge from Mathlib's Levy theorem

This file does not assume the Cramer-Wold device.  For a probability measure
on a finite-dimensional real inner-product space, its characteristic function
at `t` is the characteristic function at `1` of the scalar projection
`x |-> <x,t>`.  Therefore weak convergence of every scalar projection gives
pointwise convergence of the vector characteristic functions, and Mathlib's
verified Levy convergence theorem gives weak convergence of the vector laws.

The result applies directly to the two-dimensional pure-qubit tangent score
and the three-dimensional mixed-qubit score.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

namespace OneQubitCramerWoldBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Law of the scalar inner-product projection in direction `t`. -/
def projectedLaw (mu : ProbabilityMeasure E) (t : E) :
    ProbabilityMeasure ℝ :=
  mu.map (by fun_prop : AEMeasurable (fun x : E => ⟪t, x⟫) mu)

/-- The vector characteristic function at `t` is the scalar projected
characteristic function at `1`. -/
theorem charFun_projectedLaw_one (mu : ProbabilityMeasure E) (t : E) :
    charFun (projectedLaw mu t : Measure ℝ) 1 =
      charFun (mu : Measure E) t := by
  change
    charFun ((mu : Measure E).map (fun x : E => ⟪t, x⟫)) 1 =
      charFun (mu : Measure E) t
  symm
  rw [charFun_eq_charFunDual_toDualMap,
    charFunDual_eq_charFun_map_one]
  rfl

/-- Finite-dimensional Cramer-Wold device, derived rather than assumed:
weak convergence of every scalar inner-product projection implies weak
convergence of the vector probability measures. -/
theorem tendsto_of_all_projected_laws
    (mu : ℕ -> ProbabilityMeasure E) (mu0 : ProbabilityMeasure E)
    (hProjected : forall t : E,
      Tendsto (fun n => projectedLaw (mu n) t) atTop
        (nhds (projectedLaw mu0 t))) :
    Tendsto mu atTop (nhds mu0) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
  intro t
  have hScalar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (hProjected t)) (1 : ℝ)
  simpa only [charFun_projectedLaw_one] using hScalar

/-- The exact two-dimensional specialization used by the pure-qubit tangent
score. -/
theorem pureTwoDimensionalScore_tendsto
    (mu : ℕ -> ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (mu0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hProjected : forall t,
      Tendsto (fun n => projectedLaw (mu n) t) atTop
        (nhds (projectedLaw mu0 t))) :
    Tendsto mu atTop (nhds mu0) :=
  tendsto_of_all_projected_laws mu mu0 hProjected

/-- The exact three-dimensional specialization used by the mixed-qubit
score. -/
theorem mixedThreeDimensionalScore_tendsto
    (mu : ℕ -> ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (mu0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin 3)))
    (hProjected : forall t,
      Tendsto (fun n => projectedLaw (mu n) t) atTop
        (nhds (projectedLaw mu0 t))) :
    Tendsto mu atTop (nhds mu0) :=
  tendsto_of_all_projected_laws mu mu0 hProjected

end OneQubitCramerWoldBridge
end
end QubitOracle.Paper
