import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Finite-dimensional quantum distances

This module gives the density-matrix definitions used by the three displayed
loss equations in the main paper. Positivity and unit trace are part of the
state type, and the positive square root is Mathlib's continuous functional
calculus. No statistical or literature theorem is assumed here.
-/

namespace QubitOracle.Paper

open scoped ComplexOrder MatrixOrder

noncomputable section

/-- A finite-dimensional density matrix: positive semidefinite with unit trace. -/
structure FiniteDensityMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  val : Matrix n n ℂ
  pos : val.PosSemidef
  trace_one : Matrix.trace val = 1

/-- The finite-dimensional trace norm `Tr sqrt(A^* A)`. -/
def matrixTraceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (CFC.sqrt (star A * A))).re

/-- Trace distance between finite-dimensional quantum states. -/
def quantumTraceDistance {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) : ℝ :=
  (1 / 2 : ℝ) * matrixTraceNorm (rho.val - sigma.val)

/-- Squared Uhlmann fidelity
`(Tr sqrt(sqrt(rho) sigma sqrt(rho)))^2`. -/
def quantumFidelity {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) : ℝ :=
  let sqrtRho : Matrix n n ℂ := CFC.sqrt rho.val
  (Matrix.trace (CFC.sqrt (sqrtRho * sigma.val * sqrtRho))).re ^ 2

/-- Squared Bures distance in the paper's fidelity convention. -/
def quantumBuresDistanceSq {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) : ℝ :=
  2 * (1 - Real.sqrt (quantumFidelity rho sigma))

theorem quantumTraceDistance_formula {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) :
    quantumTraceDistance rho sigma =
      (1 / 2 : ℝ) * matrixTraceNorm (rho.val - sigma.val) := rfl

theorem quantumFidelity_formula {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) :
    quantumFidelity rho sigma =
      (Matrix.trace
        (CFC.sqrt
          (CFC.sqrt rho.val * sigma.val * CFC.sqrt rho.val))).re ^ 2 := rfl

theorem quantumBuresDistanceSq_formula
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : FiniteDensityMatrix n) :
    quantumBuresDistanceSq rho sigma =
      2 * (1 - Real.sqrt (quantumFidelity rho sigma)) := rfl

end

end QubitOracle.Paper
