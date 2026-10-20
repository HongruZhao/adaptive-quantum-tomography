import QubitOracle.LocalChart
/-!
# The two-basis oracle calculation

For a `(n + 1)`-dimensional rank-one model, the real tangent space has two
copies of `Fin n`.  A real orthogonal matrix with uniform first row generates
two orthonormal measurement bases.  This file proves from exact Born
probabilities that the bases have complementary Fisher-information blocks and
that their equal mixture is one half of the identity.

No optimality inequality or asymptotic statistical assertion is used here.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

/-- Real-amplitude directions followed by imaginary-amplitude directions. -/
abbrev TangentIndex (n : ℕ) := Sum (Fin n) (Fin n)

/-- A real orthogonal coefficient matrix with the uniform reference row used
by the two-basis construction. -/
structure OracleFrame (n : ℕ) where
  W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  orthogonal : W ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ
  uniformFirstRow : ∀ k, W 0 k = 1 / Real.sqrt (n + 1 : ℝ)

namespace OracleFrame

variable {n : ℕ} (F : OracleFrame n)

/-- Uniform reference amplitudes never vanish. -/
lemma firstRow_ne_zero (k : Fin (n + 1)) : F.W 0 k ≠ 0 := by
  rw [F.uniformFirstRow]
  positivity

/-- Orthogonality written as the row Gram identity used in the Fisher sum. -/
lemma row_gram (a b : Fin (n + 1)) :
    (∑ k, F.W a k * F.W b k) = if a = b then 1 else 0 := by
  have h := congrFun (congrFun
    ((Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mp F.orthogonal) a) b
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

end OracleFrame

/-- The reference-state probability of outcome `k`. -/
def baseProbability {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) : ℝ :=
  (F.W 0 k) ^ 2

/-- The probability gradient for the first basis. -/
def chiGradient {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ
  | Sum.inl a => F.W 0 k * F.W a.succ k
  | Sum.inr _ => 0

/-- The probability gradient for the second basis. -/
def tauGradient {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ
  | Sum.inl _ => 0
  | Sum.inr a => F.W 0 k * F.W a.succ k

/-- Exact one-coordinate probability paths for the first basis. -/
def chiProbabilityPath {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ → ℝ
  | Sum.inl a => activeProbability (F.W 0 k) (F.W a.succ k)
  | Sum.inr a => inactiveProbability (F.W 0 k) (F.W a.succ k)

/-- Exact one-coordinate probability paths for the second basis. -/
def tauProbabilityPath {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ → ℝ
  | Sum.inl a => inactiveProbability (F.W 0 k) (F.W a.succ k)
  | Sum.inr a => activeProbability (F.W 0 k) (F.W a.succ k)

/-- Exact complex amplitudes underlying `chiProbabilityPath`. -/
def chiAmplitudePath {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ → ℂ
  | Sum.inl a, t =>
      ⟨F.W 0 k * radial t + (t / 2) * F.W a.succ k, 0⟩
  | Sum.inr a, t =>
      ⟨F.W 0 k * radial t, (t / 2) * F.W a.succ k⟩

/-- Exact complex amplitudes underlying `tauProbabilityPath`. -/
def tauAmplitudePath {n : ℕ} (F : OracleFrame n) (k : Fin (n + 1)) :
    TangentIndex n → ℝ → ℂ
  | Sum.inl a, t =>
      ⟨(t / 2) * F.W a.succ k, F.W 0 k * radial t⟩
  | Sum.inr a, t =>
      ⟨0, F.W 0 k * radial t + (t / 2) * F.W a.succ k⟩

/-- A directional restriction of the normalized local chart in adapted
coordinates. -/
def directionalState {n : ℕ} (x : TangentIndex n) (t : ℝ) :
    Fin (n + 1) → ℂ :=
  Fin.cases (radial t : ℂ) fun a =>
    match x with
    | Sum.inl b => if a = b then (t / 2 : ℝ) else 0
    | Sum.inr b => if a = b then (t / 2 : ℝ) * Complex.I else 0

/-- The coefficient norm of a directional chart state is one throughout the
chart domain. -/
theorem directionalState_normalized {n : ℕ} (x : TangentIndex n) (t : ℝ)
    (ht : t ^ 2 ≤ 4) :
    (∑ i, Complex.normSq (directionalState x t i)) = 1 := by
  have hnonneg : 0 ≤ 1 - t ^ 2 / 4 := by linarith
  have hradial : radial t ^ 2 = 1 - t ^ 2 / 4 := by
    rw [radial, Real.sq_sqrt hnonneg]
  rcases x with a | a <;>
    simp [directionalState, Fin.sum_univ_succ, apply_ite] <;>
    nlinarith [hradial]

/-- Bra-ket amplitude of a state coefficient vector in a column basis. -/
def measurementAmplitude {d : Type} [Fintype d]
    (B : Matrix d d ℂ) (psi : d → ℂ) (k : d) : ℂ :=
  ∑ i, star (B i k) * psi i

/-- The first displayed probability is exactly a squared Born amplitude. -/
theorem chiProbabilityPath_eq_normSq {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    chiProbabilityPath F k x t = Complex.normSq (chiAmplitudePath F k x t) := by
  rcases x with a | a <;>
    simp [chiProbabilityPath, chiAmplitudePath, activeProbability,
      inactiveProbability, Complex.normSq_mk] <;> ring

/-- The second displayed probability is exactly a squared Born amplitude. -/
theorem tauProbabilityPath_eq_normSq {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    tauProbabilityPath F k x t = Complex.normSq (tauAmplitudePath F k x t) := by
  rcases x with a | a <;>
    simp [tauProbabilityPath, tauAmplitudePath, activeProbability,
      inactiveProbability, Complex.normSq_mk] <;> ring

/-- The stated first-basis gradient is the derivative of the exact path. -/
theorem chiProbabilityPath_hasDerivAt_zero {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) :
    HasDerivAt (chiProbabilityPath F k x) (chiGradient F k x) 0 := by
  rcases x with a | a
  · simpa [chiProbabilityPath, chiGradient] using
      hasDerivAt_activeProbability_zero (F.W 0 k) (F.W a.succ k)
  · simpa [chiProbabilityPath, chiGradient] using
      hasDerivAt_inactiveProbability_zero (F.W 0 k) (F.W a.succ k)

/-- The stated second-basis gradient is the derivative of the exact path. -/
theorem tauProbabilityPath_hasDerivAt_zero {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) :
    HasDerivAt (tauProbabilityPath F k x) (tauGradient F k x) 0 := by
  rcases x with a | a
  · simpa [tauProbabilityPath, tauGradient] using
      hasDerivAt_inactiveProbability_zero (F.W 0 k) (F.W a.succ k)
  · simpa [tauProbabilityPath, tauGradient] using
      hasDerivAt_activeProbability_zero (F.W 0 k) (F.W a.succ k)

/-- Every first-basis path starts at the declared reference probability. -/
theorem chiProbabilityPath_zero {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) :
    chiProbabilityPath F k x 0 = baseProbability F k := by
  rcases x with a | a <;>
    simp [chiProbabilityPath, activeProbability, inactiveProbability,
      radial, baseProbability]

/-- Every second-basis path starts at the declared reference probability. -/
theorem tauProbabilityPath_zero {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) :
    tauProbabilityPath F k x 0 = baseProbability F k := by
  rcases x with a | a <;>
    simp [tauProbabilityPath, activeProbability, inactiveProbability,
      radial, baseProbability]

/-- Classical Fisher information for a finite outcome model at a point with
probabilities `p` and coordinate derivatives `dp`. -/
def classicalFisher {O P : Type} [Fintype O]
    (p : O → ℝ) (dp : O → P → ℝ) : Matrix P P ℝ :=
  fun a b => ∑ k, dp k a * dp k b / p k

/-- Fisher information of the first basis at the reference state. -/
def chiFisher {n : ℕ} (F : OracleFrame n) :
    Matrix (TangentIndex n) (TangentIndex n) ℝ :=
  classicalFisher (baseProbability F) (chiGradient F)

/-- Fisher information of the second basis at the reference state. -/
def tauFisher {n : ℕ} (F : OracleFrame n) :
    Matrix (TangentIndex n) (TangentIndex n) ℝ :=
  classicalFisher (baseProbability F) (tauGradient F)

/-- Identity on real-amplitude tangent directions and zero elsewhere. -/
def realBlock (n : ℕ) : Matrix (TangentIndex n) (TangentIndex n) ℝ
  | Sum.inl a, Sum.inl b => if a = b then 1 else 0
  | _, _ => 0

/-- Identity on imaginary-amplitude tangent directions and zero elsewhere. -/
def imagBlock (n : ℕ) : Matrix (TangentIndex n) (TangentIndex n) ℝ
  | Sum.inr a, Sum.inr b => if a = b then 1 else 0
  | _, _ => 0

lemma cancel_probability (w0 wa wb : ℝ) (h0 : w0 ≠ 0) :
    (w0 * wa) * (w0 * wb) / w0 ^ 2 = wa * wb := by
  field_simp

/-- The first basis supplies exactly the real-amplitude Fisher block. -/
theorem chiFisher_eq_realBlock {n : ℕ} (F : OracleFrame n) :
    chiFisher F = realBlock n := by
  ext x y
  rcases x with a | a <;> rcases y with b | b
  · change (∑ k, (F.W 0 k * F.W a.succ k) *
        (F.W 0 k * F.W b.succ k) / (F.W 0 k) ^ 2) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    simpa [realBlock] using F.row_gram a.succ b.succ
  · simp [chiFisher, classicalFisher, chiGradient, baseProbability, realBlock]
  · simp [chiFisher, classicalFisher, chiGradient, baseProbability, realBlock]
  · simp [chiFisher, classicalFisher, chiGradient, baseProbability, realBlock]

/-- The second basis supplies exactly the imaginary-amplitude Fisher block. -/
theorem tauFisher_eq_imagBlock {n : ℕ} (F : OracleFrame n) :
    tauFisher F = imagBlock n := by
  ext x y
  rcases x with a | a <;> rcases y with b | b
  · simp [tauFisher, classicalFisher, tauGradient, baseProbability, imagBlock]
  · simp [tauFisher, classicalFisher, tauGradient, baseProbability, imagBlock]
  · simp [tauFisher, classicalFisher, tauGradient, baseProbability, imagBlock]
  · change (∑ k, (F.W 0 k * F.W a.succ k) *
        (F.W 0 k * F.W b.succ k) / (F.W 0 k) ^ 2) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    simpa [imagBlock] using F.row_gram a.succ b.succ

/-- The two complementary blocks sum to the full tangent identity. -/
theorem realBlock_add_imagBlock (n : ℕ) :
    realBlock n + imagBlock n =
      (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  ext x y
  rcases x with a | a <;> rcases y with b | b <;>
    simp [realBlock, imagBlock, Matrix.one_apply]

/-- Fisher information of the design that chooses either basis with
probability one half. -/
def equalMixtureFisher {n : ℕ} (F : OracleFrame n) :
    Matrix (TangentIndex n) (TangentIndex n) ℝ :=
  (1 / 2 : ℝ) • chiFisher F + (1 / 2 : ℝ) • tauFisher F

/-- Main finite algebraic endpoint: the equal two-basis mixture is isotropic. -/
theorem equalMixtureFisher_eq_half_identity {n : ℕ} (F : OracleFrame n) :
    equalMixtureFisher F =
      (1 / 2 : ℝ) • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  rw [equalMixtureFisher, chiFisher_eq_realBlock, tauFisher_eq_imagBlock,
    ← smul_add, realBlock_add_imagBlock]

/-- Coefficient matrix of the first orthonormal basis. -/
def chiBasis {n : ℕ} (F : OracleFrame n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i k => (F.W i k : ℂ)

/-- Reference-row phase that exchanges the two tangent quadratures. -/
def phase (i : Fin (n + 1)) : ℂ :=
  if i = 0 then -Complex.I else 1

/-- Diagonal row-phase matrix for the second basis. -/
def phaseMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal phase

/-- Coefficient matrix of the second orthonormal basis. -/
def tauBasis {n : ℕ} (F : OracleFrame n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  phaseMatrix n * chiBasis F

lemma tauBasis_apply {n : ℕ} (F : OracleFrame n)
    (i k : Fin (n + 1)) :
    tauBasis F i k = phase i * (F.W i k : ℂ) := by
  simp [tauBasis, phaseMatrix, chiBasis]

/-- The first amplitude formula is the bra-ket amplitude in `chiBasis`. -/
theorem chiAmplitudePath_eq_measurementAmplitude {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    chiAmplitudePath F k x t =
      measurementAmplitude (chiBasis F) (directionalState x t) k := by
  rcases x with a | a <;>
    simp [measurementAmplitude, Fin.sum_univ_succ, chiBasis, directionalState,
      chiAmplitudePath] <;>
    apply Complex.ext <;> simp <;> ring

/-- The second amplitude formula is the bra-ket amplitude in `tauBasis`. -/
theorem tauAmplitudePath_eq_measurementAmplitude {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    tauAmplitudePath F k x t =
      measurementAmplitude (tauBasis F) (directionalState x t) k := by
  rcases x with a | a <;>
    simp [measurementAmplitude, Fin.sum_univ_succ, tauBasis_apply, phase,
      directionalState, tauAmplitudePath] <;>
    apply Complex.ext <;> simp <;> ring

/-- The first coefficient matrix is unitary. -/
theorem chiBasis_mem_unitary {n : ℕ} (F : OracleFrame n) :
    chiBasis F ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h := congrFun (congrFun
    ((Matrix.mem_orthogonalGroup_iff' (Fin (n + 1)) ℝ).mp F.orthogonal) i) j
  have hc := congrArg Complex.ofReal h
  by_cases hij : i = j <;>
    simpa [chiBasis, Matrix.mul_apply, Matrix.one_apply, hij] using hc

/-- The row-phase matrix is unitary. -/
theorem phaseMatrix_mem_unitary (n : ℕ) :
    phaseMatrix n ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar : star (phaseMatrix n) = Matrix.diagonal (star phase) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [phaseMatrix]
    · simp [phaseMatrix, hij, Ne.symm hij]
  rw [hstar]
  change Matrix.diagonal (star phase) * Matrix.diagonal phase = 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;>
      simp [phase, hi]
  · simp [hij]

/-- The second coefficient matrix is unitary. -/
theorem tauBasis_mem_unitary {n : ℕ} (F : OracleFrame n) :
    tauBasis F ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  exact (Matrix.unitaryGroup (Fin (n + 1)) ℂ).mul_mem
    (phaseMatrix_mem_unitary n) (chiBasis_mem_unitary F)

/-- First basis transported from adapted coordinates to a laboratory frame. -/
def transportedChiBasis {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (F : OracleFrame n) :=
  E * chiBasis F

/-- Second basis transported from adapted coordinates to a laboratory frame. -/
def transportedTauBasis {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (F : OracleFrame n) :=
  E * tauBasis F

/-- Unitary transport preserves the first orthonormal basis. -/
theorem transportedChiBasis_mem_unitary {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) (F : OracleFrame n) :
    transportedChiBasis E F ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  exact (Matrix.unitaryGroup (Fin (n + 1)) ℂ).mul_mem hE
    (chiBasis_mem_unitary F)

/-- Unitary transport preserves the second orthonormal basis. -/
theorem transportedTauBasis_mem_unitary {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) (F : OracleFrame n) :
    transportedTauBasis E F ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  exact (Matrix.unitaryGroup (Fin (n + 1)) ℂ).mul_mem hE
    (tauBasis_mem_unitary F)

/-- The hardware pre-readout rotation associated with a column basis. -/
def preReadout {d : Type} [Fintype d] (B : Matrix d d ℂ) : Matrix d d ℂ :=
  star B

/-- The adjoint of a unitary basis matrix is a unitary pre-readout rotation. -/
theorem preReadout_mem_unitary {d : Type} [Fintype d] [DecidableEq d]
    (B : Matrix d d ℂ) (hB : B ∈ Matrix.unitaryGroup d ℂ) :
    preReadout B ∈ Matrix.unitaryGroup d ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simpa [preReadout] using (Matrix.mem_unitaryGroup_iff').mp hB

lemma measurementAmplitude_eq_mulVec {d : Type} [Fintype d]
    (B : Matrix d d ℂ) (psi : d → ℂ) (k : d) :
    measurementAmplitude B psi k = (star B).mulVec psi k := by
  rfl

/-- Changing both state and measurement basis by the same unitary leaves every
Born amplitude unchanged. -/
theorem measurementAmplitude_transport {d : Type} [Fintype d] [DecidableEq d]
    (E B : Matrix d d ℂ) (hE : E ∈ Matrix.unitaryGroup d ℂ)
    (psi : d → ℂ) (k : d) :
    measurementAmplitude (E * B) (E.mulVec psi) k =
      measurementAmplitude B psi k := by
  simp only [measurementAmplitude_eq_mulVec]
  rw [star_mul]
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [(Matrix.mem_unitaryGroup_iff').mp hE, Matrix.mul_one]

/-- The first exact amplitude formula remains valid in every adapted
laboratory frame. -/
theorem chiAmplitudePath_eq_transportedMeasurementAmplitude {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    chiAmplitudePath F k x t =
      measurementAmplitude (transportedChiBasis E F)
        (E.mulVec (directionalState x t)) k := by
  rw [chiAmplitudePath_eq_measurementAmplitude]
  exact (measurementAmplitude_transport E (chiBasis F) hE
    (directionalState x t) k).symm

/-- The second exact amplitude formula remains valid in every adapted
laboratory frame. -/
theorem tauAmplitudePath_eq_transportedMeasurementAmplitude {n : ℕ}
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ) (F : OracleFrame n)
    (k : Fin (n + 1)) (x : TangentIndex n) (t : ℝ) :
    tauAmplitudePath F k x t =
      measurementAmplitude (transportedTauBasis E F)
        (E.mulVec (directionalState x t)) k := by
  rw [tauAmplitudePath_eq_measurementAmplitude]
  exact (measurementAmplitude_transport E (tauBasis F) hE
    (directionalState x t) k).symm

end

end QubitOracle
