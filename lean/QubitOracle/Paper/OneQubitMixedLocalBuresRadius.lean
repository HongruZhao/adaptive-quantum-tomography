import QubitOracle.FiniteGillMassar

/-!
# Mixed-qubit local Bures radius

This deterministic module isolates the interior neighborhood used by both
the finite estimator moment bound and the exact Bures/fidelity remainder.
-/

namespace QubitOracle.Paper

/-- Explicit local radius at an interior truth. -/
noncomputable def mixedBuresFidelityLocalRadius (theta : Fin 3 → ℝ) : ℝ :=
  (1 - QubitOracle.blochNormSq theta) / 8

/-- The chosen local radius is strictly positive at every interior truth. -/
theorem mixedBuresFidelityLocalRadius_pos
    {theta : Fin 3 → ℝ} (hInterior : QubitOracle.blochNormSq theta < 1) :
    0 < mixedBuresFidelityLocalRadius theta := by
  unfold mixedBuresFidelityLocalRadius
  positivity

end QubitOracle.Paper
