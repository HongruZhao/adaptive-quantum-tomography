import QubitOracle.Paper.OneQubitConcreteLocalMinimaxReduction

/-!
# Frozen mixed-qubit LAN constructor

This module closes the deterministic matrix-algebra part of the concrete
mixed-qubit LAN package.  It does not assume that the polynomial two-stage
experiment is LAN.  Instead, `constructFrozenMixedQubitLANConclusion` accepts
the exact `Hajek1972Assumption31LAN` witness for that experiment and the exact
identification of its information matrix, then constructs the paper-facing
`FrozenMixedQubitLANConclusion` without any further scientific premise.

Keeping this constructor separate prevents the inverse-information identity
from being conflated with the remaining probabilistic LAN proof.
-/

namespace QubitOracle.Paper

open Matrix

noncomputable section

/-- The displayed mixed frozen information matrix is exactly `(1/3) I_3`. -/
theorem mixedFrozenOracleInformation_eq_smul_one :
    mixedFrozenOracleInformation =
      (1 / 3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) := by
  ext i j
  simp [mixedFrozenOracleInformation, Matrix.one_apply]

/-- The displayed mixed frozen covariance matrix is exactly `3 I_3`. -/
theorem mixedFrozenOracleCovariance_eq_smul_one :
    mixedFrozenOracleCovariance =
      (3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) := by
  ext i j
  simp [mixedFrozenOracleCovariance, Matrix.one_apply]

/-- Equal allocation among the three whitened axes has nonsingular
per-observation information. -/
theorem mixedFrozenOracleInformation_posDef :
    mixedFrozenOracleInformation.PosDef := by
  rw [mixedFrozenOracleInformation_eq_smul_one]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- The inverse of `(1/3) I_3` is exactly `3 I_3`. -/
theorem mixedFrozenOracleInformation_inv_eq_covariance :
    mixedFrozenOracleInformation⁻¹ = mixedFrozenOracleCovariance := by
  rw [mixedFrozenOracleInformation_eq_smul_one]
  letI : Invertible (1 / 3 : Real) :=
    invertibleOfNonzero (by norm_num)
  rw [Matrix.inv_smul (1 : Matrix (Fin 3) (Fin 3) Real)
    (1 / 3 : Real) (by simp)]
  simp [mixedFrozenOracleCovariance_eq_smul_one]

/-- Kernel-checked constructor for the frozen mixed-qubit LAN package.

The first premise must be the actual LAN witness for the concrete experiment;
the second premise identifies its information in the paper's whitened
coordinates.  The covariance field is then a theorem, not an assumption. -/
noncomputable def constructFrozenMixedQubitLANConclusion
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (lan : Hajek1972Assumption31LAN E truth)
    (information_eq : lan.information = mixedFrozenOracleInformation) :
    FrozenMixedQubitLANConclusion E truth := by
  refine
    { lan := lan
      information_eq := information_eq
      inverse_information_eq := ?_ }
  rw [information_eq]
  exact mixedFrozenOracleInformation_inv_eq_covariance

end

end QubitOracle.Paper
