import QubitOracle.AdaptiveDesign.OracleMeanLossTransfer
import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance
-- import QubitOracle.AdaptiveDesign.PVMOptimalVariance -- Section 5 disabled

/-!
# Oracle information and Gaussian-covariance constants

The exact Gill--Massar criterion constants are checked here against all
finite regular single-copy POVMs. The protocol-specific CLTs are imported
and separately audited. Expected physical risk still requires the
moment/capped-limit inputs of the mean-loss transfer theorem.
-/

namespace QubitOracle.AdaptiveDesign.OracleRisk

open QubitOracle QubitOracle.Paper
open scoped BigOperators
noncomputable section

/-- The two mixed-qubit oracle constants equal the selected-design
criterion and lower-bound every regular finite qubit POVM. -/
theorem mixed_oracle_criterion
    (loss : P1Weighted.Loss) (r : Fin 3 → ℝ)
    (hr : blochNormSq r < 1)
    {O : Type} [Fintype O] (P : QubitBlochPOVM O)
    (hP : (qubitClassicalFisher r P).PosDef) :
    P1Weighted.designCriterion loss r
      (P1Weighted.informationTarget loss r) =
        (match loss with
         | .bures => (9/4 : ℝ)
         | .frobenius => (2 + mixedRadialGap r)^2/2) ∧
    P1Weighted.designCriterion loss r
      (P1Weighted.informationTarget loss r) ≤
        P1Weighted.designCriterion loss r (qubitClassicalFisher r P) := by
  exact ⟨P1Weighted.optimal_criterion_value loss r hr,
    P1Weighted.informationTarget_optimal loss r hr P hP⟩

/-- The pure-state Bures quadratic covariance constant is d. -/
theorem pure_bures_covariance_constant (d : ℕ) :
    (1/4 : ℝ) * Matrix.trace
      ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) = d := by
  have h := TangentGLS.limitingCovariance_weightedTrace (d := d) (1/4 : ℝ)
  norm_num at h ⊢
  linarith

/-- The pure-state Frobenius quadratic covariance constant is 2d. -/
theorem pure_frobenius_covariance_constant (d : ℕ) :
    (1/2 : ℝ) * Matrix.trace
      ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) = 2*d := by
  have h := TangentGLS.limitingCovariance_weightedTrace (d := d) (1/2 : ℝ)
  norm_num at h ⊢
  linarith

/-- Every regular finite single-copy POVM has Bures quadratic criterion
at least as large as the covariance constant of either pure-state design. -/
theorem pure_bures_oracle_lower
    {d : ℕ} {Y : Type} [Fintype Y]
    (P : FinitePOVM (Fin (d+1)) Y)
    (hP : (referenceFisher P).PosDef) :
    (d : ℝ) ≤ isotropicRisk (1/4 : ℝ) (referenceFisher P) := by
  simpa using finitePOVM_buresQuadraticRisk_lower_bound P hP

/-- The analogous Frobenius oracle lower bound. -/
theorem pure_frobenius_oracle_lower
    {d : ℕ} {Y : Type} [Fintype Y]
    (P : FinitePOVM (Fin (d+1)) Y)
    (hP : (referenceFisher P).PosDef) :
    (2*d : ℝ) ≤ isotropicRisk (1/2 : ℝ) (referenceFisher P) := by
  simpa using finitePOVM_frobeniusRisk_lower_bound P hP

end
end QubitOracle.AdaptiveDesign.OracleRisk
