import QubitOracle.FiniteGillMassar

/-!
# Optional general Gill--Massar contract

This module records the future-facing coordinate-invariant Gill--Massar
statement as an explicit hypothesis interface.  It declares no axiom and no
global instance.  The paper-specific rank-one and interior-qubit inequalities
are proved internally in `FiniteGillMassar.lean`.
-/

namespace QubitOracle

open scoped BigOperators ComplexOrder

noncomputable section

/-- Finite-dimensional quantum statistical model equipped with SLD operators
at one parameter point. -/
structure SLDModel (d p : ℕ) where
  rho : Matrix (Fin d) (Fin d) ℂ
  rho_positive : rho.PosSemidef
  rho_trace : rho.trace = 1
  derivative : Fin p → Matrix (Fin d) (Fin d) ℂ
  derivative_trace_zero : ∀ a, (derivative a).trace = 0
  sld : Fin p → Matrix (Fin d) (Fin d) ℂ
  sld_hermitian : ∀ a, (sld a).IsHermitian
  sld_equation : ∀ a,
    derivative a = (1 / 2 : ℂ) • (sld a * rho + rho * sld a)

/-- SLD quantum Fisher matrix of a model at the represented parameter point. -/
def sldFisher {d p : ℕ} (model : SLDModel d p) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun a b =>
    (model.rho *
      (model.sld a * model.sld b + model.sld b * model.sld a)).trace.re / 2

/-- Born probability of a finite POVM outcome in an SLD model. -/
def modelProbability {d p : ℕ} {O : Type} [Fintype O]
    (model : SLDModel d p) (P : FinitePOVM (Fin d) O) (x : O) : ℝ :=
  (model.rho * P.effect x).trace.re

/-- Derivative of a Born probability in a model coordinate. -/
def modelProbabilityGradient {d p : ℕ} {O : Type} [Fintype O]
    (model : SLDModel d p) (P : FinitePOVM (Fin d) O)
    (x : O) (a : Fin p) : ℝ :=
  (model.derivative a * P.effect x).trace.re

/-- Classical Fisher matrix produced by a finite one-copy POVM.  Outcomes of
zero probability are omitted by `safeRatio`. -/
def modelClassicalFisher {d p : ℕ} {O : Type} [Fintype O]
    (model : SLDModel d p) (P : FinitePOVM (Fin d) O) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun a b => ∑ x, safeRatio (modelProbability model P x)
    (modelProbabilityGradient model P x a *
      modelProbabilityGradient model P x b)

/-- Optional hypothesis carrying the general coordinate-invariant one-copy
Gill--Massar statement.  There is intentionally no global instance. -/
class GeneralGillMassarOneCopyAssumption : Prop where
  oneCopy :
    ∀ {d p : ℕ} {O : Type} [Fintype O]
      (model : SLDModel d p) (P : FinitePOVM (Fin d) O)
      (hd : 0 < d) (hH : (sldFisher model).PosDef),
      Matrix.trace ((sldFisher model)⁻¹ * modelClassicalFisher model P) ≤
        (d : ℝ) - 1

/-- The general inequality is available only when supplied explicitly through
`GeneralGillMassarOneCopyAssumption`. -/
theorem generalGillMassar_oneCopy
    [hGM : GeneralGillMassarOneCopyAssumption]
    {d p : ℕ} {O : Type} [Fintype O]
    (model : SLDModel d p) (P : FinitePOVM (Fin d) O)
    (hd : 0 < d) (hH : (sldFisher model).PosDef) :
    Matrix.trace ((sldFisher model)⁻¹ * modelClassicalFisher model P) ≤
      (d : ℝ) - 1 :=
  hGM.oneCopy model P hd hH

end


end QubitOracle
