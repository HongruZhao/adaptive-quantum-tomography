import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICFisher
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.FiniteGillMassar
import QubitOracle.TwoBasis
/-! # Phase pairing of an arbitrary finite rank-one POVM

The starting POVM is globally identifying and regular at the reference ray.
Its Fisher information is NOT a hypothesis. The labelled fair mixture with
a quarter-phase partner has half-QFI, proved from rank one and completeness.
No complement-library identity is used.

The hardware gate gives +pi/2 only to the reference level. Applying it to
the state before measuring P conjugates effects by its adjoint; branch
therefore stores gate.conjTranspose. The adjoint gate differs from the complement-phase
matrix by the global scalar -i, so the two conventions give the same effects.
-/
namespace QubitOracle.AdaptiveDesign.PhasePair
open QubitOracle QubitOracle.Paper GeneralPOVM
open GlobalPFSIC (projector projector_apply projector_posSemidef)
open GlobalPFSICHermitian
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section

/-- Hardware phases: i on the reference level, 1 on every other level. -/
def phase (d : ℕ) : Fin (d+1) → ℂ := Fin.cases Complex.I (fun _ => 1)

def gate (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  Matrix.diagonal (phase d)

theorem gate_unitary (d : ℕ) : gate d ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext i j
  simp only [gate, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    refine Fin.cases ?_ (fun k => ?_) i <;> simp [phase, Matrix.one_apply]
  · simp [hij, Ne.symm hij, Matrix.diagonal_apply]

theorem gate_adjoint_unitary (d : ℕ) :
    (gate d).conjTranspose ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.mp (gate_unitary d)

/-- The adjoint state gate is globally phase-equivalent to the
complement-phase matrix, so conjugating effects gives the same experiment. -/
theorem gate_adjoint_eq_globalPhase_complement (d : ℕ) :
    (gate d).conjTranspose = (-Complex.I) •
      Matrix.diagonal (Fin.cases (1 : ℂ) (fun _ : Fin d => Complex.I)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    refine Fin.cases ?_ (fun k => ?_) i <;>
      simp [gate, phase, Matrix.conjTranspose_apply, Matrix.smul_apply,
        Matrix.diagonal_apply]
  · simp [gate, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, hij, Ne.symm hij]

/-- Effect conjugation for a fair branch: the hardware state gate is V,
while the phase branch has effects V* P.effect V. -/
def branch (d : ℕ) (b : Bool) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  if b then (gate d).conjTranspose else 1

theorem branch_unitary (d : ℕ) (b : Bool) :
    branch d b ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
  cases b
  · simp [branch]
  · simpa [branch] using gate_adjoint_unitary d

variable {d : ℕ} {O : Type} [Fintype O]

/-- Positive rank-one effects, with weights absorbed into the factors.
Regularity below excludes the zero factor. -/
def RankOne (P : FinitePOVM (Fin (d+1)) O) : Prop :=
  ∀ o, ∃ v : Fin (d+1) → ℂ, P.effect o = projector v

def paired (P : FinitePOVM (Fin (d+1)) O) :
    FinitePOVM (Fin (d+1)) (Bool × O) where
  effect o := (1/2 : ℝ) • GeneralPOVM.effect P (branch d o.1) o.2
  positive o := (GeneralPOVM.effect_positive P (branch d o.1) o.2).smul (by norm_num)
  complete := by
    simp only [Fintype.sum_prod_type, ← Finset.smul_sum,
      GeneralPOVM.effect_complete P _ (branch_unitary d _), Fintype.sum_bool]
    rw [smul_add, ← add_smul]
    norm_num

theorem paired_effect_false (P : FinitePOVM (Fin (d+1)) O) (o : O) :
    (paired P).effect (false,o) = (1/2 : ℝ) • P.effect o := by
  simp [paired, GeneralPOVM.effect, branch]

theorem paired_effect_true (P : FinitePOVM (Fin (d+1)) O) (o : O) :
    (paired P).effect (true,o) =
      (1/2 : ℝ) • ((gate d).conjTranspose * P.effect o * gate d) := by
  simp [paired, GeneralPOVM.effect, branch]

theorem gate_effect_entry (P : FinitePOVM (Fin (d+1)) O) (o : O)
    (i j : Fin (d+1)) :
    GeneralPOVM.effect P (gate d) o i j =
      phase d i * P.effect o i j * star (phase d j) := by
  simp [GeneralPOVM.effect, gate, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, mul_assoc]

theorem gate_adjoint_effect_entry (P : FinitePOVM (Fin (d+1)) O) (o : O)
    (i j : Fin (d+1)) :
    GeneralPOVM.effect P (gate d).conjTranspose o i j =
      star (phase d i) * P.effect o i j * phase d j := by
  simp [GeneralPOVM.effect, gate, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, mul_assoc]

theorem paired_referenceProbability (P : FinitePOVM (Fin (d+1)) O)
    (b : Bool) (o : O) :
    referenceProbability (paired P) (b,o) = (1/2 : ℝ) * referenceProbability P o := by
  cases b
  · simp [referenceProbability, paired_effect_false, Matrix.smul_apply]
  · simp [referenceProbability, paired, branch, Matrix.smul_apply,
      gate_adjoint_effect_entry, phase]

theorem paired_regular (P : FinitePOVM (Fin (d+1)) O) (hp : Regular P) :
    Regular (paired P) := by
  rintro ⟨b,o⟩
  rw [paired_referenceProbability]
  exact mul_pos (by norm_num) (hp o)

theorem paired_identifying (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) :
    Identifying (paired P) := by
  intro A hA
  apply hI A
  intro o
  have he : GeneralPOVM.effectVector (paired P) (false,o) =
      (1/2 : ℝ) • GeneralPOVM.effectVector P o := by
    apply toMatrix_injective
    exact paired_effect_false P o
  have hh := hA (false,o)
  rw [he, real_inner_smul_left] at hh
  linarith

theorem paired_gradient_false (P : FinitePOVM (Fin (d+1)) O)
    (o : O) (x : TangentIndex d) :
    referenceGradient (paired P) (false,o) x = (1/2 : ℝ) * referenceGradient P o x := by
  cases x <;> simp [referenceGradient, paired_effect_false, Matrix.smul_apply]

theorem paired_gradient_true_inl (P : FinitePOVM (Fin (d+1)) O) (o : O) (j : Fin d) :
    referenceGradient (paired P) (true,o) (.inl j) = (1/2 : ℝ) * (P.effect o 0 j.succ).im := by
  simp [referenceGradient, paired, branch, Matrix.smul_apply, gate_adjoint_effect_entry,
    phase, Complex.mul_re, Complex.mul_im]

theorem paired_gradient_true_inr (P : FinitePOVM (Fin (d+1)) O) (o : O) (j : Fin d) :
    referenceGradient (paired P) (true,o) (.inr j) = (1/2 : ℝ) * (P.effect o 0 j.succ).re := by
  simp [referenceGradient, paired, branch, Matrix.smul_apply, gate_adjoint_effect_entry,
    phase, Complex.mul_re, Complex.mul_im]

theorem paired_fisher_term (P : FinitePOVM (Fin (d+1)) O) (hp : Regular P)
    (o : O) (v : Fin (d+1) → ℂ) (hv : P.effect o = projector v)
    (x y : TangentIndex d) :
    (∑ b : Bool, safeRatio (referenceProbability (paired P) (b,o))
      (referenceGradient (paired P) (b,o) x * referenceGradient (paired P) (b,o) y)) =
      (1/2 : ℝ) * realify (projector (fun j : Fin d => v j.succ)) x y := by
  have hp0 : (v 0).re * (v 0).re + (v 0).im * (v 0).im ≠ 0 := by
    have hh := ne_of_gt (hp o)
    simpa [referenceProbability, hv, projector_apply, Complex.mul_re] using hh
  have hp1 : (v 0).re ^ 2 + (v 0).im ^ 2 ≠ 0 := by simpa [pow_two] using hp0
  rcases x with j | j <;> rcases y with k | k
  all_goals
    simp only [Fintype.sum_bool, paired_referenceProbability, paired_gradient_false,
      paired_gradient_true_inl, paired_gradient_true_inr, safeRatio_eq_div]
    simp [referenceProbability, referenceGradient, hv, projector_apply,
      realify, Complex.mul_re, Complex.mul_im]
    field_simp [hp0, hp1]
    ring

theorem tail_projector_sum (P : FinitePOVM (Fin (d+1)) O)
    (v : O → Fin (d+1) → ℂ) (hv : ∀ o, P.effect o = projector (v o)) :
    (∑ o, projector (fun j : Fin d => v o j.succ)) = 1 := by
  ext j k
  have hh := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => A j.succ k.succ) P.complete
  simpa [Matrix.sum_apply, hv, projector_apply, Matrix.one_apply] using hh

theorem realify_sum {I : Type} [Fintype I] (A : I → Matrix (Fin d) (Fin d) ℂ) :
    realify (∑ i, A i) = ∑ i, realify (A i) := by
  ext x y
  rcases x with j | j <;> rcases y with k | k <;>
    simp [realify, Matrix.sum_apply, Finset.sum_neg_distrib]

/-- Half-QFI is derived from rank-one factorization and completeness. -/
theorem paired_fisherSymmetric (P : FinitePOVM (Fin (d+1)) O) (hp : Regular P)
    (v : O → Fin (d+1) → ℂ) (hv : ∀ o, P.effect o = projector (v o)) :
    FisherSymmetric (paired P) := by
  have hs : (∑ o, realify (projector (fun j : Fin d => v o j.succ))) = 1 := by
    rw [← realify_sum, tail_projector_sum P v hv, realify_one]
  ext x y
  change (∑ bo : Bool × O, safeRatio (referenceProbability (paired P) bo)
    (referenceGradient (paired P) bo x * referenceGradient (paired P) bo y)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [paired_fisher_term P hp _ _ (hv _) x y, ← Finset.mul_sum]
  have hh := congrArg (fun A : Matrix (TangentIndex d) (TangentIndex d) ℝ => A x y) hs
  simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using congrArg (fun t : ℝ => (1/2)*t) hh

theorem paired_apparatus (P : FinitePOVM (Fin (d+1)) O)
    (hI : Identifying P) (hp : Regular P)
    (v : O → Fin (d+1) → ℂ) (hv : ∀ o, P.effect o = projector (v o)) :
    Identifying (paired P) ∧ Regular (paired P) ∧ FisherSymmetric (paired P) :=
  ⟨paired_identifying P hI, paired_regular P hp, paired_fisherSymmetric P hp v hv⟩

/-- Public version: no reference Fisher identity is assumed. -/
theorem paired_fisher_of_rankOne (P : FinitePOVM (Fin (d+1)) O)
    (hp : Regular P) (hR : RankOne P) : FisherSymmetric (paired P) := by
  classical
  choose v hv using hR
  exact paired_fisherSymmetric P hp v hv

theorem paired_conditions (P : FinitePOVM (Fin (d+1)) O)
    (hI : Identifying P) (hp : Regular P) (hR : RankOne P) :
    Identifying (paired P) ∧ Regular (paired P) ∧ FisherSymmetric (paired P) :=
  ⟨paired_identifying P hI, paired_regular P hp, paired_fisher_of_rankOne P hp hR⟩

end
end QubitOracle.AdaptiveDesign.PhasePair
