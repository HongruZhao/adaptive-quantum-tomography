import QubitOracle.Paper.QubitFoundations

/-!
# Core one-qubit Born regression definitions

This module contains only the finite-dimensional definitions used by both the
regularity and RLS developments.  It deliberately has no controller, LAN, or
asymptotic import.
-/

namespace QubitOracle.Paper

noncomputable section

/-- Binary outcome type for a projective qubit-axis measurement. -/
abbrev QubitRLSOutcome := Bool

/-- Numerical coding of the two projective outcomes. -/
def qubitRLSOutcomeSign : QubitRLSOutcome -> Real
  | false => -1
  | true => 1

/-- Born probability for the outcome coded by `y`. -/
def qubitRLSBornProbability
    (theta u : Fin 3 -> Real) (y : QubitRLSOutcome) : Real :=
  qubitBornTrace theta u (qubitRLSOutcomeSign y)

end

end QubitOracle.Paper
