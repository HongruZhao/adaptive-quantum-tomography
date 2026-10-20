import QubitOracle.Paper.QuantumDistances

set_option autoImplicit false

/-! The mathematical summaries defined in Section 6. This encodes the
definitions, not the numerical values of a Monte Carlo run or its plots.
Information is indexed from zero, so `information n` is the conditional
information of paper copy `n+1`. -/
namespace QubitOracle.Paper.MainPaperNumericalDefinitions
open QubitOracle.Paper
open scoped BigOperators
noncomputable section

def currentCriterion {p : ℕ} (W : Matrix (Fin p) (Fin p) ℝ)
    (information : ℕ → Matrix (Fin p) (Fin p) ℝ) (n : ℕ+) : ℝ :=
  Matrix.trace (W * (information n)⁻¹)

def averageCriterion {p : ℕ} (W : Matrix (Fin p) (Fin p) ℝ)
    (information : ℕ → Matrix (Fin p) (Fin p) ℝ) (n : ℕ+) : ℝ :=
  Matrix.trace (W * (((n : ℝ)⁻¹ • ∑ t ∈ Finset.range (n : ℕ), information t)⁻¹))

inductive Loss where
  | squaredBures
  | squaredFrobenius

def squaredFrobenius {D : ℕ} (rho sigma : FiniteDensityMatrix (Fin D)) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (rho.val i j-sigma.val i j)

def Loss.value {D : ℕ} (loss : Loss) (rho sigma : FiniteDensityMatrix (Fin D)) : ℝ :=
  match loss with
  | .squaredBures => quantumBuresDistanceSq rho sigma
  | .squaredFrobenius => MainPaperNumericalDefinitions.squaredFrobenius rho sigma

def scaledMeanLoss {D : ℕ} (loss : Loss) (R : ℕ+) (n : ℕ)
    (estimates : Fin (R : ℕ) → FiniteDensityMatrix (Fin D))
    (truth : FiniteDensityMatrix (Fin D)) : ℝ :=
  (R : ℝ)⁻¹ * ∑ r, (n : ℝ) * loss.value (estimates r) truth

theorem scaledMeanLoss_eq {D : ℕ} (loss : Loss) (R : ℕ+) (n : ℕ)
    (estimates : Fin (R : ℕ) → FiniteDensityMatrix (Fin D))
    (truth : FiniteDensityMatrix (Fin D)) :
    scaledMeanLoss loss R n estimates truth =
      (∑ r, (n : ℝ) * loss.value (estimates r) truth) / (R : ℝ) := by
  simp only [scaledMeanLoss, div_eq_mul_inv, mul_comm]

end
end QubitOracle.Paper.MainPaperNumericalDefinitions
