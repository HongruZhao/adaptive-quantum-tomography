import QubitOracle.FourDimensional
import QubitOracle.FiniteGillMassar

/-!
# Gill--Massar bridge

This file packages the normalized trace budget as an explicit proposition on
a candidate Fisher matrix.  It first gives abstract results conditional on
that proposition and then discharges it for every finite POVM in the
rank-one reference chart using `rankOne_reference_gillMassar`.  The separate
general SLD axiom module is deliberately not imported here.
-/

namespace QubitOracle

noncomputable section

/-- The rank-one tangent chart in dimension `n + 1` has `2n` real
coordinates. -/
theorem tangentIndex_card (n : ℕ) :
    Fintype.card (TangentIndex n) = 2 * n := by
  simp [TangentIndex]
  omega

/-- Normalized Gill--Massar trace budget for an information matrix on the
rank-one tangent chart.  This is a property, not an axiom asserting that any
particular measurement class satisfies it. -/
def SatisfiesGillMassarTraceBudget {n : ℕ}
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ) : Prop :=
  M.trace ≤ (n : ℝ)

/-- The equal two-basis information matrix is positive definite. -/
theorem equalMixtureFisher_posDef {n : ℕ} (F : OracleFrame n) :
    (equalMixtureFisher F).PosDef := by
  rw [equalMixtureFisher_eq_half_identity]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- The equal two-basis information matrix saturates, hence satisfies, the
normalized trace budget. -/
theorem equalMixture_satisfies_gillMassarTraceBudget {n : ℕ}
    (F : OracleFrame n) :
    SatisfiesGillMassarTraceBudget (equalMixtureFisher F) := by
  rw [SatisfiesGillMassarTraceBudget, equalMixtureFisher_eq_half_identity,
    Matrix.trace_smul, Matrix.trace_one, tangentIndex_card]
  simp only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  ring_nf
  exact le_rfl

/-- Exact isotropic risk attained by the equal two-basis design. -/
theorem equalMixture_isotropicRisk {n : ℕ} (g : ℝ) (F : OracleFrame n) :
    isotropicRisk g (equalMixtureFisher F) = 4 * g * n := by
  rw [equalMixtureFisher_eq_half_identity, isotropicRisk_half_identity,
    tangentIndex_card]
  push_cast
  ring

/-- Frobenius quadratic risk constant in dimension `n + 1`. -/
theorem equalMixture_frobeniusRisk {n : ℕ} (F : OracleFrame n) :
    isotropicRisk (1 / 2 : ℝ) (equalMixtureFisher F) = 2 * n := by
  rw [equalMixture_isotropicRisk]
  norm_num

/-- Squared-trace-distance quadratic risk constant in dimension `n + 1`. -/
theorem equalMixture_traceRisk {n : ℕ} (F : OracleFrame n) :
    isotropicRisk (1 / 4 : ℝ) (equalMixtureFisher F) = n := by
  rw [equalMixture_isotropicRisk]
  norm_num

/-- Bures quadratic risk constant in dimension `n + 1`. -/
theorem equalMixture_buresQuadraticRisk {n : ℕ} (F : OracleFrame n) :
    isotropicRisk (1 / 4 : ℝ) (equalMixtureFisher F) = n :=
  equalMixture_traceRisk F

/-- Conditional Gill--Massar lower bound for every positive-definite
competitor satisfying the explicit trace-budget hypothesis. -/
theorem gillMassarBudget_risk_lower_bound {n : ℕ} (g : ℝ)
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hg : 0 ≤ g) (hM : M.PosDef)
    (hGM : SatisfiesGillMassarTraceBudget M) :
    4 * g * n ≤ isotropicRisk g M := by
  have hbudget : M.trace ≤
      (Fintype.card (TangentIndex n) : ℝ) / 2 := by
    rw [tangentIndex_card]
    push_cast
    simpa [SatisfiesGillMassarTraceBudget] using hGM
  have hconstant :
      2 * g * (Fintype.card (TangentIndex n) : ℝ) = 4 * g * n := by
    rw [tangentIndex_card]
    push_cast
    ring
  rw [← hconstant]
  exact isotropicRisk_lower_bound g M hg hM hbudget

/-- For positive loss weight, a regular competitor attains the conditional
Gill--Massar bound exactly when its information is `(1/2) I`. -/
theorem gillMassarBudget_risk_eq_iff {n : ℕ} (g : ℝ)
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hg : 0 < g) (hM : M.PosDef)
    (hGM : SatisfiesGillMassarTraceBudget M) :
    isotropicRisk g M = 4 * g * n ↔
      M = (1 / 2 : ℝ) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  have hbudget : M.trace ≤
      (Fintype.card (TangentIndex n) : ℝ) / 2 := by
    rw [tangentIndex_card]
    push_cast
    simpa [SatisfiesGillMassarTraceBudget] using hGM
  have hconstant :
      2 * g * (Fintype.card (TangentIndex n) : ℝ) = 4 * g * n := by
    rw [tangentIndex_card]
    push_cast
    ring
  rw [← hconstant]
  exact isotropicRisk_eq_lower_bound_iff g M hg hM hbudget

/-- Abstract design-level optimality theorem.  The caller supplies the
positive-definiteness and Gill--Massar trace-budget proofs for its competitor
class. -/
theorem twoBasis_optimal_under_gillMassar
    {n : ℕ} {Design : Type}
    (information : Design → Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hpos : ∀ xi, (information xi).PosDef)
    (hGM : ∀ xi, SatisfiesGillMassarTraceBudget (information xi))
    (F : OracleFrame n) (g : ℝ) (hg : 0 ≤ g) (xi : Design) :
    isotropicRisk g (equalMixtureFisher F) ≤
      isotropicRisk g (information xi) := by
  rw [equalMixture_isotropicRisk]
  exact gillMassarBudget_risk_lower_bound g (information xi) hg
    (hpos xi) (hGM xi)

/-- A regular competitor ties the equal two-basis design exactly when its
information matrix is the half identity. -/
theorem competitor_ties_twoBasis_iff_isotropic
    {n : ℕ} {Design : Type}
    (information : Design → Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hpos : ∀ xi, (information xi).PosDef)
    (hGM : ∀ xi, SatisfiesGillMassarTraceBudget (information xi))
    (F : OracleFrame n) (g : ℝ) (hg : 0 < g) (xi : Design) :
    isotropicRisk g (information xi) =
        isotropicRisk g (equalMixtureFisher F) ↔
      information xi = (1 / 2 : ℝ) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  rw [equalMixture_isotropicRisk]
  exact gillMassarBudget_risk_eq_iff g (information xi) hg
    (hpos xi) (hGM xi)

/-- Every finite POVM in the rank-one reference chart satisfies the trace
budget, now as a proved theorem rather than a hypothesis. -/
theorem referenceFisher_satisfies_gillMassarTraceBudget
    {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    SatisfiesGillMassarTraceBudget (referenceFisher P) :=
  rankOne_reference_gillMassar P

/-- Unconditional risk lower bound for every regular finite POVM in the
rank-one reference chart. -/
theorem finitePOVM_risk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (g : ℝ) (P : FinitePOVM (Fin (n + 1)) O)
    (hg : 0 ≤ g) (hpos : (referenceFisher P).PosDef) :
    4 * g * n ≤ isotropicRisk g (referenceFisher P) :=
  gillMassarBudget_risk_lower_bound g (referenceFisher P) hg hpos
    (referenceFisher_satisfies_gillMassarTraceBudget P)

/-- The equal two-basis design is optimal among regular finite POVMs for every
nonnegative isotropic quadratic weight. -/
theorem twoBasis_optimal_over_finitePOVM
    {n : ℕ} {O : Type} [Fintype O]
    (F : OracleFrame n) (g : ℝ) (hg : 0 ≤ g)
    (P : FinitePOVM (Fin (n + 1)) O)
    (hpos : (referenceFisher P).PosDef) :
    isotropicRisk g (equalMixtureFisher F) ≤
      isotropicRisk g (referenceFisher P) := by
  rw [equalMixture_isotropicRisk]
  exact finitePOVM_risk_lower_bound g P hg hpos

/-- For a positive isotropic loss weight, a regular finite POVM ties the
two-basis design exactly when its Fisher matrix is `(1/2) I`. -/
theorem finitePOVM_ties_twoBasis_iff_isotropic
    {n : ℕ} {O : Type} [Fintype O]
    (F : OracleFrame n) (g : ℝ) (hg : 0 < g)
    (P : FinitePOVM (Fin (n + 1)) O)
    (hpos : (referenceFisher P).PosDef) :
    isotropicRisk g (referenceFisher P) =
        isotropicRisk g (equalMixtureFisher F) ↔
      referenceFisher P = (1 / 2 : ℝ) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  rw [equalMixture_isotropicRisk]
  exact gillMassarBudget_risk_eq_iff g (referenceFisher P) hg hpos
    (referenceFisher_satisfies_gillMassarTraceBudget P)

theorem finitePOVM_frobeniusRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O)
    (hpos : (referenceFisher P).PosDef) :
    2 * n ≤ isotropicRisk (1 / 2 : ℝ) (referenceFisher P) := by
  have h := finitePOVM_risk_lower_bound (1 / 2 : ℝ) P (by norm_num) hpos
  norm_num at h ⊢
  exact h

theorem finitePOVM_traceRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O)
    (hpos : (referenceFisher P).PosDef) :
    n ≤ isotropicRisk (1 / 4 : ℝ) (referenceFisher P) := by
  have h := finitePOVM_risk_lower_bound (1 / 4 : ℝ) P (by norm_num) hpos
  norm_num at h ⊢
  exact h

theorem finitePOVM_buresQuadraticRisk_lower_bound
    {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O)
    (hpos : (referenceFisher P).PosDef) :
    n ≤ isotropicRisk (1 / 4 : ℝ) (referenceFisher P) :=
  finitePOVM_traceRisk_lower_bound P hpos

/-- Four-dimensional Frobenius quadratic risk constant. -/
theorem fourDimensional_frobeniusRisk :
    isotropicRisk (1 / 2 : ℝ)
      (equalMixtureFisher fourDimensionalFrame) = 6 := by
  norm_num [equalMixture_frobeniusRisk]

/-- Four-dimensional squared-trace-distance quadratic risk constant. -/
theorem fourDimensional_traceRisk :
    isotropicRisk (1 / 4 : ℝ)
      (equalMixtureFisher fourDimensionalFrame) = 3 := by
  norm_num [equalMixture_traceRisk]

/-- Four-dimensional Bures quadratic risk constant. -/
theorem fourDimensional_buresQuadraticRisk :
    isotropicRisk (1 / 4 : ℝ)
      (equalMixtureFisher fourDimensionalFrame) = 3 :=
  fourDimensional_traceRisk

end


end QubitOracle
