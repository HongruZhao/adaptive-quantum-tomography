import QubitOracle.FiniteGillMassar

/-!
# Mixed-qubit local quadratic loss core

This deterministic module isolates the local interior Bures quadratic
comparator from protocol, concentration, LAN, and minimax machinery.
-/

namespace QubitOracle.Paper

noncomputable section

/-- Coordinate-free local interior Bures quadratic comparator.  This is not
the exact finite-displacement Bures loss. -/
def mixedInteriorBuresQuadraticLoss
    (theta error : Fin 3 → ℝ) : ℝ :=
  (4 : ℝ)⁻¹ * QubitOracle.blochNormSq error +
    (4 * (1 - QubitOracle.blochNormSq theta))⁻¹ *
      QubitOracle.blochDot theta error ^ 2

end

end QubitOracle.Paper
