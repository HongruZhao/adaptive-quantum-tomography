import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import QubitOracle.TwoBasis
/-!
# Gill--Massar inequalities in the paper's explicit charts

This file contains kernel-checked finite-outcome results.  It proves the
Gill--Massar trace bound for the rank-one reference chart in every finite
dimension and for the interior Bloch-ball chart of a qubit.  The proofs use
only positivity and completeness of the measurement effects and explicit
coordinate formulas; they do not use the general Gill--Massar axiom kept in a
separate module.
-/

namespace QubitOracle

open scoped BigOperators ComplexOrder

noncomputable section

/-- A positive-semidefinite complex matrix satisfies the entrywise
Cauchy--Schwarz inequality. -/
theorem psd_entry_normSq_le_diag_mul_diag {ι : Type}
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (i j : ι) :
    Complex.normSq (A i j) ≤ (A i i).re * (A j j).re := by
  let e : Fin 2 → ι := ![i, j]
  have hB : (A.submatrix e e).PosSemidef := hA.submatrix e
  have hdet := hB.det_nonneg
  have hherm := hA.isHermitian.apply i j
  have hdiag_i := hA.diag_nonneg (i := i)
  have hdiag_j := hA.diag_nonneg (i := j)
  rw [Matrix.det_fin_two] at hdet
  simp [e] at hdet
  simp only [Complex.nonneg_iff] at hdet hdiag_i hdiag_j
  rcases hdet with ⟨hdet, _⟩
  rcases hdiag_i with ⟨hii, hii_im⟩
  rcases hdiag_j with ⟨hjj, hjj_im⟩
  have hji : A j i = star (A i j) := by
    simpa using congrArg star hherm
  rw [hji] at hdet
  simp [Complex.mul_conj] at hdet
  nlinarith

/-- A finite POVM represented by positive-semidefinite complex effects that
sum to the identity. -/
structure FinitePOVM (d O : Type) [Fintype O] [DecidableEq d] where
  effect : O → Matrix d d ℂ
  positive : ∀ x, (effect x).PosSemidef
  complete : ∑ x, effect x = 1

/-- Division used in Fisher information, with outcomes of zero reference
probability omitted. -/
def safeRatio (p q : ℝ) : ℝ :=
  if p = 0 then 0 else q / p

theorem safeRatio_sum {κ : Type} [Fintype κ] (p : ℝ) (f : κ → ℝ) :
    safeRatio p (∑ i, f i) = ∑ i, safeRatio p (f i) := by
  by_cases hp : p = 0
  · simp [safeRatio, hp]
  · simp [safeRatio, hp, Finset.sum_div]

/-! ## Rank-one reference chart -/

/-- Born probability at the reference ray `|0><0|`. -/
def referenceProbability {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) : ℝ :=
  (P.effect x 0 0).re

/-- Probability gradient in the normalized `2n`-coordinate chart. -/
def referenceGradient {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) : TangentIndex n → ℝ
  | Sum.inl a => (P.effect x 0 a.succ).re
  | Sum.inr a => -(P.effect x 0 a.succ).im

/-- Classical Fisher matrix at the rank-one reference ray. -/
def referenceFisher {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    Matrix (TangentIndex n) (TangentIndex n) ℝ :=
  fun a b => ∑ x, safeRatio (referenceProbability P x)
    (referenceGradient P x a * referenceGradient P x b)

def referenceOffdiagEnergy {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) : ℝ :=
  ∑ a : Fin n, Complex.normSq (P.effect x 0 a.succ)

def tangentDiagonalMass {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) : ℝ :=
  ∑ a : Fin n, (P.effect x a.succ a.succ).re

theorem referenceGradient_energy {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) :
    (∑ a, referenceGradient P x a * referenceGradient P x a) =
      referenceOffdiagEnergy P x := by
  simp [referenceGradient, referenceOffdiagEnergy, Fintype.sum_sum_type,
    Complex.normSq_apply, Finset.sum_add_distrib]

theorem referenceFisher_trace {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    (referenceFisher P).trace =
      ∑ x, safeRatio (referenceProbability P x)
        (referenceOffdiagEnergy P x) := by
  change (∑ a, ∑ x, safeRatio (referenceProbability P x)
    (referenceGradient P x a * referenceGradient P x a)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← safeRatio_sum, referenceGradient_energy]

theorem referenceProbability_nonneg {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) :
    0 ≤ referenceProbability P x := by
  have h := (P.positive x).diag_nonneg (i := (0 : Fin (n + 1)))
  exact (Complex.nonneg_iff.mp h).1

theorem tangentDiagonalMass_nonneg {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) :
    0 ≤ tangentDiagonalMass P x := by
  rw [tangentDiagonalMass]
  apply Finset.sum_nonneg
  intro a _
  have h := (P.positive x).diag_nonneg (i := a.succ)
  exact (Complex.nonneg_iff.mp h).1

/-- Each POVM outcome contributes no more relative Fisher information than
its tangent diagonal mass. -/
theorem referenceOutcomeRatio_le_diagonalMass {n : ℕ}
    {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) (x : O) :
    safeRatio (referenceProbability P x) (referenceOffdiagEnergy P x) ≤
      tangentDiagonalMass P x := by
  by_cases hp : referenceProbability P x = 0
  · simp [safeRatio, hp, tangentDiagonalMass_nonneg P x]
  · have hp_pos : 0 < referenceProbability P x :=
      lt_of_le_of_ne (referenceProbability_nonneg P x) (Ne.symm hp)
    rw [safeRatio, if_neg hp]
    apply (div_le_iff₀ hp_pos).2
    calc
      referenceOffdiagEnergy P x ≤
          referenceProbability P x * tangentDiagonalMass P x := by
        rw [referenceOffdiagEnergy, tangentDiagonalMass, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro a _
        exact psd_entry_normSq_le_diag_mul_diag
          (P.effect x) (P.positive x) 0 a.succ
      _ = tangentDiagonalMass P x * referenceProbability P x := by ring

theorem sum_tangentDiagonalMass {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    (∑ x, tangentDiagonalMass P x) = n := by
  calc
    (∑ x, tangentDiagonalMass P x) =
        ∑ x, ∑ a : Fin n, (P.effect x a.succ a.succ).re := by
      rfl
    _ = ∑ a : Fin n, ∑ x, (P.effect x a.succ a.succ).re :=
      Finset.sum_comm
    _ = ∑ _a : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      have hentry := congrArg
        (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M a.succ a.succ)
        P.complete
      simp only [Matrix.sum_apply, Matrix.one_apply, ↓reduceIte] at hentry
      have hre := congrArg Complex.re hentry
      simpa using hre
    _ = n := by simp

/-- Kernel-checked Gill--Massar inequality in the paper's rank-one reference
chart.  It covers every finite POVM in dimension `n + 1`. -/
theorem rankOne_reference_gillMassar {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    (referenceFisher P).trace ≤ (n : ℝ) := by
  rw [referenceFisher_trace, ← sum_tangentDiagonalMass P]
  apply Finset.sum_le_sum
  intro x _
  exact referenceOutcomeRatio_le_diagonalMass P x

theorem qubit_rankOne_reference_gillMassar {O : Type} [Fintype O]
    (P : FinitePOVM (Fin 2) O) :
    (referenceFisher P).trace ≤ 1 := by
  simpa using rankOne_reference_gillMassar (n := 1) P

theorem fourDimensional_rankOne_reference_gillMassar
    {O : Type} [Fintype O] (P : FinitePOVM (Fin 4) O) :
    (referenceFisher P).trace ≤ 3 := by
  simpa using rankOne_reference_gillMassar (n := 3) P

/-! ## Interior Bloch-qubit chart -/

def blochNormSq (v : Fin 3 → ℝ) : ℝ :=
  ∑ i, v i ^ 2

def blochDot (r v : Fin 3 → ℝ) : ℝ :=
  ∑ i, r i * v i

/-- Bloch-coordinate representation of a finite qubit POVM.  Each effect has
the form `weight * I + vector · sigma`; the displayed conditions are its
positivity and completeness constraints. -/
structure QubitBlochPOVM (O : Type) [Fintype O] where
  weight : O → ℝ
  vector : O → Fin 3 → ℝ
  weight_nonneg : ∀ x, 0 ≤ weight x
  vector_normSq_le : ∀ x, blochNormSq (vector x) ≤ (weight x) ^ 2
  sum_weight : ∑ x, weight x = 1
  sum_vector : ∀ i, ∑ x, vector x i = 0

/-- Born probability in the Bloch-ball chart. -/
def qubitProbability {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O) (x : O) : ℝ :=
  P.weight x + blochDot r (P.vector x)

def blochOuter (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => v i * v j

def safeInv (p : ℝ) : ℝ :=
  if p = 0 then 0 else p⁻¹

theorem safeInv_mul (p q : ℝ) :
    safeInv p * q = safeRatio p q := by
  by_cases hp : p = 0
  · simp [safeInv, safeRatio, hp]
  · simp [safeInv, safeRatio, hp, div_eq_mul_inv, mul_comm]

/-- Classical Fisher matrix of a Bloch-coordinate qubit POVM. -/
def qubitClassicalFisher {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ x, safeInv (qubitProbability r P x) • blochOuter (P.vector x)

/-- Explicit inverse SLD Fisher matrix in the interior Bloch-ball chart. -/
def qubitSLDFisherInv (r : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if i = j then 1 else 0) - r i * r j

theorem trace_qubitSLDFisherInv_mul_blochOuter
    (r v : Fin 3 → ℝ) :
    Matrix.trace (qubitSLDFisherInv r * blochOuter v) =
      blochNormSq v - (blochDot r v) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    qubitSLDFisherInv, blochOuter, blochNormSq, blochDot]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hdiag :
      (∑ i : Fin 3, ∑ j : Fin 3, (if i = j then 1 else 0) * (v j * v i)) =
        ∑ i : Fin 3, v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  rw [hdiag]
  congr 1
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, r i * r j * (v j * v i)) =
        ∑ i : Fin 3, (r i * v i) * ∑ j : Fin 3, r j * v j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i : Fin 3, r i * v i) * ∑ j : Fin 3, r j * v j := by
      rw [Finset.sum_mul]
    _ = (∑ i : Fin 3, r i * v i) ^ 2 := by ring

def qubitGillMassarValue {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O) : ℝ :=
  ∑ x, safeRatio (qubitProbability r P x)
    (blochNormSq (P.vector x) - (blochDot r (P.vector x)) ^ 2)

theorem qubitGillMassarValue_eq_trace {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O) :
    qubitGillMassarValue r P =
      Matrix.trace (qubitSLDFisherInv r * qubitClassicalFisher r P) := by
  rw [qubitClassicalFisher, Matrix.mul_sum, Matrix.trace_sum]
  simp only [qubitGillMassarValue]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_smul, Matrix.trace_smul,
    trace_qubitSLDFisherInv_mul_blochOuter]
  simp only [smul_eq_mul]
  rw [safeInv_mul]

theorem bloch_cauchy_schwarz (r v : Fin 3 → ℝ) :
    (blochDot r v) ^ 2 ≤ blochNormSq r * blochNormSq v := by
  simpa [blochDot, blochNormSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) r v)

theorem qubitOutcomeRatio_le {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O)
    (hr : blochNormSq r < 1) (x : O) :
    safeRatio (qubitProbability r P x)
        (blochNormSq (P.vector x) - (blochDot r (P.vector x)) ^ 2) ≤
      P.weight x - blochDot r (P.vector x) := by
  let a := P.weight x
  let v := P.vector x
  let c := blochDot r v
  let V := blochNormSq v
  have ha : 0 ≤ a := P.weight_nonneg x
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hR : 0 ≤ blochNormSq r := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hRle : blochNormSq r ≤ 1 := hr.le
  have hcs : c ^ 2 ≤ blochNormSq r * V := bloch_cauchy_schwarz r v
  have hRV : blochNormSq r * V ≤ V := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRle) hV]
  have hcV : c ^ 2 ≤ V := hcs.trans hRV
  have hVa : V ≤ a ^ 2 := P.vector_normSq_le x
  have hca : c ^ 2 ≤ a ^ 2 := hcV.trans hVa
  have hminus : 0 ≤ a - c := by nlinarith
  have hprob : 0 ≤ qubitProbability r P x := by
    change 0 ≤ a + c
    nlinarith
  by_cases hp : qubitProbability r P x = 0
  · rw [safeRatio, if_pos hp]
    exact hminus
  · have hp_pos : 0 < qubitProbability r P x :=
      lt_of_le_of_ne hprob (Ne.symm hp)
    rw [safeRatio, if_neg hp]
    apply (div_le_iff₀ hp_pos).2
    change V - c ^ 2 ≤ (a - c) * (a + c)
    nlinarith

theorem sum_qubit_complement {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O) :
    (∑ x, (P.weight x - blochDot r (P.vector x))) = 1 := by
  rw [Finset.sum_sub_distrib, P.sum_weight]
  have hdot : (∑ x, blochDot r (P.vector x)) = 0 := by
    calc
      (∑ x, blochDot r (P.vector x)) =
          ∑ x, ∑ i : Fin 3, r i * P.vector x i := by rfl
      _ = ∑ i : Fin 3, ∑ x, r i * P.vector x i := Finset.sum_comm
      _ = ∑ i : Fin 3, r i * ∑ x, P.vector x i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = 0 := by simp [P.sum_vector]
  rw [hdot]
  ring

/-- Kernel-checked Gill--Massar inequality for the paper's interior
Bloch-qubit parameterization. -/
theorem qubit_interior_gillMassar {O : Type} [Fintype O]
    (r : Fin 3 → ℝ) (P : QubitBlochPOVM O)
    (hr : blochNormSq r < 1) :
    Matrix.trace (qubitSLDFisherInv r * qubitClassicalFisher r P) ≤ 1 := by
  rw [← qubitGillMassarValue_eq_trace, qubitGillMassarValue,
    ← sum_qubit_complement r P]
  apply Finset.sum_le_sum
  intro x _
  exact qubitOutcomeRatio_le r P hr x

end


end QubitOracle
