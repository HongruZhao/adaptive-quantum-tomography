import QubitOracle.GillMassarBridge

/-!
# Source-faithful one-copy Gill--Massar interface

This module records the source statement separately from the algebraic
consequences needed by the paper.  The source is Gill and Massar,
"State estimation for large ensembles", Phys. Rev. A 61, 042312 (2000),
Theorems I and II and equation (27), arXiv:quant-ph/9902063v2.

The explicit hypothesis interface below is precisely the finite-outcome,
`N = 1` specialization of those results.  For one copy every POVM is already a
separate measurement, so Theorem II covers mixed states; Theorem I covers
pure states.  We additionally restrict to an identifiable coordinate model,
expressed by positive-definiteness of the SLD Fisher matrix, because the
source formula contains its ordinary matrix inverse.

No theorem-shaped proposition is stored in a structure.  The model contains
only a density matrix, physical tangent matrices, SLD matrices, and their
defining equations.  In particular, the conversion from the source trace to
the normalized chart and every subsequent risk inequality are Lean proofs.
-/

namespace QubitOracle.Paper.SourceFaithfulGillMassar

open scoped BigOperators ComplexOrder

noncomputable section

/-- Data at one point of a finite-dimensional quantum statistical model.
The tangent matrices are explicitly Hermitian and trace zero, and the SLDs
satisfy Gill--Massar equation (24). -/
structure OneCopySLDModel (d : ℕ) (ι : Type*) [Fintype ι] where
  state : Matrix (Fin d) (Fin d) ℂ
  state_positive : state.PosSemidef
  state_trace : state.trace = 1
  derivative : ι → Matrix (Fin d) (Fin d) ℂ
  derivative_hermitian : ∀ a, (derivative a).IsHermitian
  derivative_trace_zero : ∀ a, (derivative a).trace = 0
  sld : ι → Matrix (Fin d) (Fin d) ℂ
  sld_hermitian : ∀ a, (sld a).IsHermitian
  sld_equation : ∀ a,
    derivative a = (1 / 2 : ℂ) • (sld a * state + state * sld a)

/-- The SLD (Helstrom) quantum Fisher information matrix, source equation
(25). -/
def sldQuantumFisher {d : ℕ} {ι : Type*} [Fintype ι]
    (model : OneCopySLDModel d ι) : Matrix ι ι ℝ :=
  fun a b =>
    (model.state *
      (model.sld a * model.sld b + model.sld b * model.sld a)).trace.re / 2

/-- Born probability of a finite one-copy POVM outcome. -/
def bornProbability {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O)
    (x : O) : ℝ :=
  (model.state * P.effect x).trace.re

/-- Coordinate derivative of a Born probability. -/
def bornProbabilityDerivative
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O)
    (x : O) (a : ι) : ℝ :=
  (model.derivative a * P.effect x).trace.re

/-- Classical Fisher information of the finite one-copy outcome law, source
equation (20) with `N = 1`.  A zero-probability outcome contributes zero. -/
def oneCopyClassicalFisher
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O) :
    Matrix ι ι ℝ :=
  fun a b => ∑ x, QubitOracle.safeRatio (bornProbability model P x)
    (bornProbabilityDerivative model P x a *
      bornProbabilityDerivative model P x b)

/-- The coordinate-invariant Gill--Massar information trace. -/
def informationTrace
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [DecidableEq ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O) : ℝ :=
  Matrix.trace ((sldQuantumFisher model)⁻¹ *
    oneCopyClassicalFisher model P)

/-- Finite-outcome, one-copy specialization
of Gill--Massar (2000), Theorems I--II, equation (27):
`tr (H⁻¹ I) ≤ d - 1`.

No global instance is declared, so this proposition is not part of the trusted
kernel base. -/
class GillMassar2000OneCopyAssumption
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [DecidableEq ι] [Fintype O]
    (model : OneCopySLDModel d ι)
    (P : QubitOracle.FinitePOVM (Fin d) O) : Prop where
  oneCopy (hd : 0 < d) (hH : (sldQuantumFisher model).PosDef) :
    informationTrace model P ≤ (d : ℝ) - 1

theorem gillMassar2000_theorems_I_II_oneCopy
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [DecidableEq ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O)
    [hGM : GillMassar2000OneCopyAssumption model P]
    (hd : 0 < d) (hH : (sldQuantumFisher model).PosDef) :
    informationTrace model P ≤ (d : ℝ) - 1 :=
  hGM.oneCopy hd hH

/-- Kernel-checked normalization: if the chart's SLD Fisher matrix is the
identity and its classical Fisher matrix is `M`, the source trace is exactly
`trace M`. -/
theorem informationTrace_eq_matrixTrace_of_normalizedChart
    {d : ℕ} {ι : Type*} {O : Type} [Fintype ι] [DecidableEq ι] [Fintype O]
    (model : OneCopySLDModel d ι) (P : QubitOracle.FinitePOVM (Fin d) O)
    (M : Matrix ι ι ℝ)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    informationTrace model P = M.trace := by
  simp [informationTrace, hH, hI]

/-- The source theorem, specialized algebraically to the normalized
`2n`-coordinate chart of a pure state in dimension `n + 1`. -/
theorem paperRankOne_informationTrace_le
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (QubitOracle.TangentIndex n))
    (P : QubitOracle.FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (QubitOracle.TangentIndex n)
      (QubitOracle.TangentIndex n) ℝ)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    M.trace ≤ (n : ℝ) := by
  have hsource := gillMassar2000_theorems_I_II_oneCopy
    model P (Nat.succ_pos n) hHpos
  rw [informationTrace_eq_matrixTrace_of_normalizedChart model P M hH hI]
    at hsource
  have hdim : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by
    push_cast
    ring
  rwa [hdim] at hsource

/-- The preceding source specialization supplies exactly the trace-budget
premise used by the paper's matrix optimization. -/
theorem paperRankOne_satisfiesGillMassarTraceBudget
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (QubitOracle.TangentIndex n))
    (P : QubitOracle.FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (QubitOracle.TangentIndex n)
      (QubitOracle.TangentIndex n) ℝ)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    QubitOracle.SatisfiesGillMassarTraceBudget M :=
  paperRankOne_informationTrace_le model P M hHpos hH hI

/-- Kernel-checked sharp isotropic risk lower bound obtained from the source
information trace and the paper's finite-dimensional matrix inequality. -/
theorem paperRankOne_isotropicRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (QubitOracle.TangentIndex n))
    (P : QubitOracle.FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (QubitOracle.TangentIndex n)
      (QubitOracle.TangentIndex n) ℝ)
    (g : ℝ) (hg : 0 ≤ g) (hM : M.PosDef)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    4 * g * n ≤ QubitOracle.isotropicRisk g M :=
  QubitOracle.gillMassarBudget_risk_lower_bound g M hg hM
    (paperRankOne_satisfiesGillMassarTraceBudget model P M hHpos hH hI)

/-- Frobenius-loss constant derived from the source-shaped interface. -/
theorem paperRankOne_frobeniusRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (QubitOracle.TangentIndex n))
    (P : QubitOracle.FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (QubitOracle.TangentIndex n)
      (QubitOracle.TangentIndex n) ℝ)
    (hM : M.PosDef) (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    2 * n ≤ QubitOracle.isotropicRisk (1 / 2 : ℝ) M := by
  have h := paperRankOne_isotropicRisk_lower_bound
    model P M (1 / 2 : ℝ) (by norm_num) hM hHpos hH hI
  norm_num at h ⊢
  exact h

/-- Bures/fidelity quadratic-loss constant derived from the source-shaped
interface. -/
theorem paperRankOne_buresRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (QubitOracle.TangentIndex n))
    (P : QubitOracle.FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (QubitOracle.TangentIndex n)
      (QubitOracle.TangentIndex n) ℝ)
    (hM : M.PosDef) (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    n ≤ QubitOracle.isotropicRisk (1 / 4 : ℝ) M := by
  have h := paperRankOne_isotropicRisk_lower_bound
    model P M (1 / 4 : ℝ) (by norm_num) hM hHpos hH hI
  norm_num at h ⊢
  exact h

end

end QubitOracle.Paper.SourceFaithfulGillMassar
