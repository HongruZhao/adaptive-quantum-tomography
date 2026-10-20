import QubitOracle.AdaptiveDesign.GeneralPOVMModel

/-! # Reference Fisher symmetry is invariant under a correct-ray frame
The only Fisher hypothesis is a matrix identity at ONE reference state.
The full unitary-fiber identity is derived, not assumed.
-/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open QubitOracle QubitOracle.Paper Filter
open scoped BigOperators Topology ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def realify {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ
  | .inl j, .inl k => (Q j k).re
  | .inl j, .inr k => -(Q j k).im
  | .inr j, .inl k => (Q j k).im
  | .inr j, .inr k => (Q j k).re

def realVector {d : ℕ} (v : Fin d → ℂ) : TangentIndex d → ℝ
  | .inl j => (v j).re
  | .inr j => (v j).im

theorem realify_one (d : ℕ) : realify (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  classical
  ext x y
  rcases x with j | j <;> rcases y with k | k <;>
    by_cases h : j = k <;> simp [realify, Matrix.one_apply, h]

theorem realify_mul {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℂ) :
    realify (Q * R) = realify Q * realify R := by
  ext x y
  rcases x with j | j <;> rcases y with k | k <;>
    simp [realify, Matrix.mul_apply, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  all_goals ring

theorem realify_conjTranspose {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) :
    realify Q.conjTranspose = (realify Q).transpose := by
  ext x y
  rcases x with j | j <;> rcases y with k | k <;>
    simp [realify, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realify_orthogonal {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    realify Q * (realify Q).transpose = 1 := by
  have hh : Q * Q.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  rw [← realify_conjTranspose, ← realify_mul, hh, realify_one]

theorem realVector_mulVec {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    realVector (Q.mulVec v) = (realify Q).mulVec (realVector v) := by
  funext x
  cases x <;> simp [realVector, realify, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

def mass {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) : ℝ := (effect P U o 0 0).re

def gradient {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) : TangentIndex d → ℝ
  | .inl j => (effect P U o 0 j.succ).re
  | .inr j => -(effect P U o 0 j.succ).im

def fisher {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o, safeRatio (mass P U o) (gradient P U o x * gradient P U o y)

/-- C2: all listed outcomes have positive probability at the reference ray. -/
def Regular {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) : Prop :=
  ∀ o, 0 < referenceProbability P o

/-- C3: local Fisher symmetry, solely at the computational reference ray. -/
def FisherSymmetric {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) : Prop :=
  referenceFisher P = (1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)

theorem effect_head_row {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) (o : O) (j : Fin (d+1)) :
    effect P U o 0 j = ∑ k, U 0 0 * P.effect o 0 k * star (U j k) := by
  have hz : ∀ k : Fin d, U 0 k.succ = 0 := fun k =>
    unitary_firstRow_eq_zero_of_overlap_one U hU h k.succ (Fin.succ_ne_zero k)
  simp [effect, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hz]

theorem mass_of_overlap_one {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) (o : O) :
    mass P U o = referenceProbability P o := by
  have hz : ∀ k : Fin d, U 0 k.succ = 0 := fun k =>
    unitary_firstRow_eq_zero_of_overlap_one U hU h k.succ (Fin.succ_ne_zero k)
  have hn : U 0 0 * star (U 0 0) = 1 := by
    calc
      _ = (Complex.normSq (U 0 0) : ℂ) := Complex.mul_conj (U 0 0)
      _ = 1 := by rw [show Complex.normSq (U 0 0) = 1 from h]; rfl
  have he : effect P U o 0 0 = P.effect o 0 0 := by
    rw [effect_head_row P U hU h, Fin.sum_univ_succ]
    simp only [hz, star_zero, mul_zero, Finset.sum_const_zero, add_zero]
    calc
      _ = (U 0 0 * star (U 0 0)) * P.effect o 0 0 := by ring
      _ = _ := by rw [hn, one_mul]
  exact congrArg Complex.re he

theorem gradient_of_overlap_one {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) (o : O) :
    gradient P U o = (realify (fiberComplement U)).mulVec (referenceGradient P o) := by
  have hc (j : Fin d) : star (effect P U o 0 j.succ) =
      (fiberComplement U).mulVec (fun k => star (P.effect o 0 k.succ)) j := by
    rw [effect_head_row P U hU h, Fin.sum_univ_succ]
    have hz := unitary_firstColumn_eq_zero_of_overlap_one U hU h j.succ (Fin.succ_ne_zero j)
    simp only [hz, star_zero, mul_zero, zero_add, star_sum, star_mul', star_star,
      Matrix.mulVec, dotProduct, fiberComplement]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have href : referenceGradient P o = realVector (fun k => star (P.effect o 0 k.succ)) := by
    funext x
    cases x <;> simp [referenceGradient, realVector]
  rw [href, ← realVector_mulVec]
  funext x
  cases x with
  | inl j => simpa [gradient, realVector] using congrArg Complex.re (hc j)
  | inr j => simpa [gradient, realVector] using congrArg Complex.im (hc j)

/-- In real arithmetic the zero-outcome convention is exactly total division. -/
theorem safeRatio_eq_div (p q : ℝ) : safeRatio p q = q / p := by
  by_cases h : p = 0 <;> simp [safeRatio, h]

def weightedGram {I O : Type} [Fintype O] (p : O → ℝ) (g : O → I → ℝ) :
    Matrix I I ℝ := ∑ o, (p o)⁻¹ • Matrix.vecMulVec (g o) (g o)

theorem weightedGram_apply {I O : Type} [Fintype O]
    (p : O → ℝ) (g : O → I → ℝ) (x y : I) :
    weightedGram p g x y = ∑ o, safeRatio (p o) (g o x * g o y) := by
  simp only [weightedGram, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, safeRatio_eq_div, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem weightedGram_transport {I O : Type} [Fintype I] [Fintype O]
    (p : O → ℝ) (g : O → I → ℝ) (R : Matrix I I ℝ) :
    weightedGram p (fun o => R.mulVec (g o)) = R * weightedGram p g * R.transpose := by
  simp only [weightedGram, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem fisher_of_overlap_one {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hP : FisherSymmetric P)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) :
    fisher P U = (1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  have he : fisher P U = weightedGram (referenceProbability P)
      (fun o => (realify (fiberComplement U)).mulVec (referenceGradient P o)) := by
    ext x y
    simp only [fisher, weightedGram_apply, mass_of_overlap_one P U hU h,
      gradient_of_overlap_one P U hU h]
  have href : weightedGram (referenceProbability P) (referenceGradient P) = referenceFisher P := by
    ext x y
    exact weightedGram_apply _ _ x y
  rw [he, weightedGram_transport, href, hP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    realify_orthogonal _ (fiberComplement_mem_unitary U hU h)]

theorem mass_continuous {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (o : O) : Continuous (fun U => mass P U o) := by
  unfold mass effect
  fun_prop

theorem gradient_continuous {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (o : O) (x : TangentIndex d) :
    Continuous (fun U => gradient P U o x) := by
  cases x <;> simp only [gradient, effect] <;> fun_prop

theorem fisher_continuousAt {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hp : ∀ o, mass P U o ≠ 0) : ContinuousAt (fisher P) U := by
  apply continuousAt_pi.2
  intro x
  apply continuousAt_pi.2
  intro y
  unfold fisher
  simp only [safeRatio_eq_div]
  have hterm (o : O) : ContinuousAt (fun V =>
      (gradient P V o x * gradient P V o y) / mass P V o) U :=
    ((gradient_continuous P o x).continuousAt.mul (gradient_continuous P o y).continuousAt).div
      (mass_continuous P o).continuousAt (hp o)
  fun_prop

/-- Ray convergence suffices: the phase and complement need not converge. -/
theorem fisher_tendsto {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hp : Regular P) (hF : FisherSymmetric P)
    (controller : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => controllerTrueOverlapSq (controller n)) atTop (𝓝 1)) :
    Tendsto (fun n => fisher P (controller n)) atTop
      (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ}
    isCompact_unitaryMatrices controller hU
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h
    (fisher P) ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) ?_
  intro U hU h
  refine ⟨fisher_continuousAt P U ?_, fisher_of_overlap_one P hF U hU h⟩
  intro o
  rw [mass_of_overlap_one P U hU h]
  exact (hp o).ne'

theorem fisher_generalTruth_tendsto {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hp : Regular P) (hF : FisherSymmetric P)
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (controller : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => GlobalPFSIC.frameProjector (controller n)) atTop
      (𝓝 (GlobalPFSIC.frameProjector T))) :
    Tendsto (fun n => fisher P (T.conjTranspose * controller n)) atTop
      (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) :=
  fisher_tendsto P hp hF _ (fun n => GlobalPFSIC.relative_unitary T (controller n) hT (hU n))
    (GlobalPFSIC.relative_overlap_tendsto T hT controller h)

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
