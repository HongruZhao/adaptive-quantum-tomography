import QubitOracle.AdaptiveDesign.GlobalPFSICFisher

/-! # The Fisher gradients are derivatives of exact normalized Born probabilities -/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

open scoped BigOperators

noncomputable section

def amplitudePath (alpha : ℝ) (b : ℂ) (t : ℝ) : ℂ :=
  (alpha : ℂ) * (radial t : ℂ) + (t/2 : ℝ) * b

theorem normSq_amplitudePath_hasDerivAt_zero (alpha : ℝ) (b : ℂ) :
    HasDerivAt (fun t => Complex.normSq (amplitudePath alpha b t)) (alpha*b.re) 0 := by
  have hr : HasDerivAt (fun t : ℝ => alpha * radial t + (t/2)*b.re) (b.re/2) 0 := by
    convert (hasDerivAt_radial_zero.const_mul alpha).add
      (((hasDerivAt_id (x := (0:ℝ))).div_const 2).mul_const b.re) using 1 <;> first | rfl | ring
  have hi : HasDerivAt (fun t : ℝ => (t/2)*b.im) (b.im/2) 0 := by
    convert ((hasDerivAt_id (x := (0:ℝ))).div_const 2).mul_const b.im using 1 <;> first | rfl | ring
  convert (hr.pow 2).add (hi.pow 2) using 1
  all_goals first
    | rfl
    | (funext t; simp [amplitudePath, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring)
    | (norm_num [radial] <;> ring)

def exactBornAmplitude {d : ℕ} (o : Outcome d) (x : TangentIndex d) (t : ℝ) : ℂ :=
  ∑ i, star (measurementVector o i) * directionalState x t i

def exactBornProbability {d : ℕ} (o : Outcome d) (x : TangentIndex d) (t : ℝ) : ℝ :=
  effectWeight d * Complex.normSq (exactBornAmplitude o x t)

theorem exactBornAmplitude_inl {d : ℕ} (o : Outcome d) (j : Fin d) (t : ℝ) :
    exactBornAmplitude o (.inl j) t =
      amplitudePath (Real.sqrt (latitude d o.1)) (star (measurementVector o j.succ)) t := by
  simp [exactBornAmplitude, directionalState, Fin.sum_univ_succ, amplitudePath,
    measurementVector, liftVector, mul_comm]

theorem exactBornAmplitude_inr {d : ℕ} (o : Outcome d) (j : Fin d) (t : ℝ) :
    exactBornAmplitude o (.inr j) t =
      amplitudePath (Real.sqrt (latitude d o.1))
        (Complex.I * star (measurementVector o j.succ)) t := by
  simp [exactBornAmplitude, directionalState, Fin.sum_univ_succ, amplitudePath,
    measurementVector, liftVector]
  ring

theorem exactBornProbability_at_zero {d : ℕ} (o : Outcome d) (x : TangentIndex d) :
    exactBornProbability o x 0 = effectWeight d * latitude d o.1 := by
  rcases x with j | j
  · simp [exactBornProbability, exactBornAmplitude_inl, amplitudePath, radial,
      Real.mul_self_sqrt (latitude_pos d o.1).le]
  · simp [exactBornProbability, exactBornAmplitude_inr, amplitudePath, radial,
      Real.mul_self_sqrt (latitude_pos d o.1).le]

/-- The advertised Fisher gradient is the actual derivative of the Born law. -/
theorem exactBornProbability_hasDerivAt_zero (d : ℕ) (hd : 0 < d)
    (o : Outcome d) (x : TangentIndex d) :
    HasDerivAt (exactBornProbability o x)
      (referenceGradient (measurementPOVM d hd) o x) 0 := by
  rw [measurementPOVM_referenceGradient]
  rcases x with j | j
  · have h := (normSq_amplitudePath_hasDerivAt_zero
      (Real.sqrt (latitude d o.1)) (star (measurementVector o j.succ))).const_mul (effectWeight d)
    convert h using 1
    all_goals first
      | rfl
      | (funext t; simp only [exactBornProbability, exactBornAmplitude_inl])
      | (simp [measurementVector, liftVector, phaseCoordinate, Complex.mul_re, Complex.mul_im] <;> ring)
  · have h := (normSq_amplitudePath_hasDerivAt_zero
      (Real.sqrt (latitude d o.1)) (Complex.I * star (measurementVector o j.succ))).const_mul (effectWeight d)
    convert h using 1
    all_goals first
      | rfl
      | (funext t; simp only [exactBornProbability, exactBornAmplitude_inr])
      | (simp [measurementVector, liftVector, phaseCoordinate, Complex.mul_re, Complex.mul_im] <;> ring)

def complexAmplitudePath (a b : ℂ) (t : ℝ) : ℂ :=
  a * (radial t : ℂ) + (t/2 : ℝ) * b

theorem normSq_complexAmplitudePath_hasDerivAt_zero (a b : ℂ) :
    HasDerivAt (fun t => Complex.normSq (complexAmplitudePath a b t))
      (star a * b).re 0 := by
  have hr : HasDerivAt (fun t : ℝ => a.re * radial t + (t/2)*b.re) (b.re/2) 0 := by
    convert (hasDerivAt_radial_zero.const_mul a.re).add
      (((hasDerivAt_id (x := (0:ℝ))).div_const 2).mul_const b.re) using 1
    all_goals first | rfl | ring
  have hi : HasDerivAt (fun t : ℝ => a.im * radial t + (t/2)*b.im) (b.im/2) 0 := by
    convert (hasDerivAt_radial_zero.const_mul a.im).add
      (((hasDerivAt_id (x := (0:ℝ))).div_const 2).mul_const b.im) using 1
    all_goals first | rfl | ring
  convert (hr.pow 2).add (hi.pow 2) using 1
  all_goals first
    | rfl
    | (funext t; simp [complexAmplitudePath, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im] <;> ring)
    | (norm_num [radial, Complex.mul_re] <;> ring)

def genericBornAmplitude {d : ℕ} (w : Fin (d+1) → ℂ)
    (x : TangentIndex d) (t : ℝ) : ℂ :=
  ∑ i, star (w i) * directionalState x t i

def genericBornProbability {d : ℕ} (c : ℝ) (w : Fin (d+1) → ℂ)
    (x : TangentIndex d) (t : ℝ) : ℝ :=
  c * Complex.normSq (genericBornAmplitude w x t)

def genericEffectGradient {d : ℕ} (c : ℝ) (w : Fin (d+1) → ℂ) : TangentIndex d → ℝ
  | .inl j => ((c • projector w : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) 0 j.succ).re
  | .inr j => -((c • projector w : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) 0 j.succ).im

theorem genericBornAmplitude_inl {d : ℕ} (w : Fin (d+1) → ℂ) (j : Fin d) (t : ℝ) :
    genericBornAmplitude w (.inl j) t = complexAmplitudePath (star (w 0)) (star (w j.succ)) t := by
  simp [genericBornAmplitude, directionalState, Fin.sum_univ_succ,
    complexAmplitudePath, mul_comm]

theorem genericBornAmplitude_inr {d : ℕ} (w : Fin (d+1) → ℂ) (j : Fin d) (t : ℝ) :
    genericBornAmplitude w (.inr j) t =
      complexAmplitudePath (star (w 0)) (Complex.I * star (w j.succ)) t := by
  simp [genericBornAmplitude, directionalState, Fin.sum_univ_succ, complexAmplitudePath]
  ring

/-- Every transported rank-one effect has the stated exact Born gradient;
no normalization or positivity premise is needed for this calculus identity. -/
theorem genericBornProbability_hasDerivAt_zero {d : ℕ} (c : ℝ)
    (w : Fin (d+1) → ℂ) (x : TangentIndex d) :
    HasDerivAt (genericBornProbability c w x) (genericEffectGradient c w x) 0 := by
  rcases x with j | j
  · have h := (normSq_complexAmplitudePath_hasDerivAt_zero
      (star (w 0)) (star (w j.succ))).const_mul c
    convert h using 1
    all_goals first
      | rfl
      | (funext t; simp only [genericBornProbability, genericBornAmplitude_inl])
      | (simp [genericEffectGradient, Matrix.smul_apply, projector_apply,
          Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring)
  · have h := (normSq_complexAmplitudePath_hasDerivAt_zero
      (star (w 0)) (Complex.I * star (w j.succ))).const_mul c
    convert h using 1
    all_goals first
      | rfl
      | (funext t; simp only [genericBornProbability, genericBornAmplitude_inr])
      | (simp [genericEffectGradient, Matrix.smul_apply, projector_apply,
          Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring)


end

end QubitOracle.AdaptiveDesign.GlobalPFSIC
