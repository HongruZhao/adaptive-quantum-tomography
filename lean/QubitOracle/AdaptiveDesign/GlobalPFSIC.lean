import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
/-!
# Two-latitude, four-phase globally identifying pure-state measurement

This file constructs actual positive matrix effects in every complex Hilbert
dimension `d+1`, with `d>0`. Its complement library is explicitly implemented
in `GlobalPFSICLibrary`; no existence or spanning axiom is imported.
-/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

open scoped BigOperators ComplexOrder

noncomputable section

abbrev Outcome (d : ℕ) := Bool × Fin 4 × LibraryIndex d

def latitude (d : ℕ) (b : Bool) : ℝ :=
  if b then 3 / (2 * (d+1 : ℝ)) else 1 / (2 * (d+1 : ℝ))

def effectWeight (d : ℕ) : ℝ := (d+1 : ℝ) / (8 * d * (4*d+1))

theorem latitude_pos (d : ℕ) (b : Bool) : 0 < latitude d b := by
  cases b <;> simp only [latitude, Bool.false_eq_true, ↓reduceIte] <;> positivity

theorem latitude_lt_one (d : ℕ) (hd : 0 < d) (b : Bool) : latitude d b < 1 := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 2 * (d+1 : ℝ) := by positivity
  cases b <;> simp only [latitude, Bool.false_eq_true, ↓reduceIte]
    <;> apply (div_lt_one hden).mpr <;> linarith

theorem effectWeight_pos (d : ℕ) (hd : 0 < d) : 0 < effectWeight d := by
  unfold effectWeight
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  positivity

theorem outcome_card (d : ℕ) : Fintype.card (Outcome d) = 8*d*(4*d+1) := by
  simp [Outcome, library_card]
  ring

def liftVector {d : ℕ} (alpha beta : ℝ) (s : Fin 4) (v : Fin d → ℂ) :
    Fin (d+1) → ℂ :=
  Fin.cases (alpha : ℂ) (fun j => phase4 s * (beta : ℂ) * v j)

def measurementVector {d : ℕ} (o : Outcome d) : Fin (d+1) → ℂ :=
  liftVector (Real.sqrt (latitude d o.1)) (Real.sqrt (1-latitude d o.1))
    o.2.1 (libraryVector o.2.2)

def effect {d : ℕ} (o : Outcome d) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (effectWeight d) • projector (measurementVector o)

theorem effect_posSemidef {d : ℕ} (hd : 0 < d) (o : Outcome d) :
    (effect o).PosSemidef :=
  (projector_posSemidef (measurementVector o)).smul (effectWeight_pos d hd).le

theorem measurementVector_normalized {d : ℕ} (hd : 0 < d) (o : Outcome d) :
    (∑ a, Complex.normSq (measurementVector o a)) = 1 := by
  have ht : 0 ≤ latitude d o.1 := (latitude_pos d o.1).le
  have hu : 0 ≤ 1-latitude d o.1 := sub_nonneg.mpr (latitude_lt_one d hd o.1).le
  simp only [measurementVector, liftVector, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, map_mul, phase4_normSq,
    Complex.normSq_ofReal, one_mul]
  rw [Real.mul_self_sqrt ht, Real.mul_self_sqrt hu, ← Finset.mul_sum, libraryVector_normSq]
  ring

theorem effect_reference_entry {d : ℕ} (o : Outcome d) :
    (effect o 0 0).re = effectWeight d * latitude d o.1 := by
  have ht : 0 ≤ latitude d o.1 := (latitude_pos d o.1).le
  simp [effect, Matrix.smul_apply, projector_apply, measurementVector,
    liftVector, Complex.mul_re, Real.mul_self_sqrt ht]

theorem effect_reference_probability_pos {d : ℕ} (hd : 0 < d) (o : Outcome d) :
    0 < (effect o 0 0).re := by
  rw [effect_reference_entry]
  exact mul_pos (effectWeight_pos d hd) (latitude_pos d o.1)

theorem projector_lift_zero_zero {d : ℕ} (alpha beta : ℝ) (s : Fin 4)
    (v : Fin d → ℂ) :
    projector (liftVector alpha beta s v) 0 0 = (alpha ^ 2 : ℝ) := by
  simp [projector_apply, liftVector, sq]

theorem projector_lift_succ_succ {d : ℕ} (alpha beta : ℝ) (s : Fin 4)
    (v : Fin d → ℂ) (j k : Fin d) :
    projector (liftVector alpha beta s v) j.succ k.succ =
      (beta ^ 2 : ℝ) * projector v j k := by
  fin_cases s <;> simp [projector_apply, liftVector, phase4, sq]
    <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem projector_lift_zero_succ {d : ℕ} (alpha beta : ℝ) (s : Fin 4)
    (v : Fin d → ℂ) (k : Fin d) :
    projector (liftVector alpha beta s v) 0 k.succ =
      (alpha * beta : ℝ) * star (phase4 s) * star (v k) := by
  simp [projector_apply, liftVector]
  ring

theorem projector_lift_succ_zero {d : ℕ} (alpha beta : ℝ) (s : Fin 4)
    (v : Fin d → ℂ) (j : Fin d) :
    projector (liftVector alpha beta s v) j.succ 0 =
      (alpha * beta : ℝ) * phase4 s * v j := by
  simp [projector_apply, liftVector]
  ring

theorem effect_zero_zero {d : ℕ} (o : Outcome d) :
    effect o 0 0 = (effectWeight d * latitude d o.1 : ℝ) := by
  simp only [effect, measurementVector, Matrix.smul_apply, projector_lift_zero_zero,
    Real.sq_sqrt (latitude_pos d o.1).le, Complex.real_smul, Complex.ofReal_mul]

theorem effect_succ_succ {d : ℕ} (hd : 0 < d) (o : Outcome d) (j k : Fin d) :
    effect o j.succ k.succ =
      (effectWeight d * (1-latitude d o.1) : ℝ) *
        projector (libraryVector o.2.2) j k := by
  have ht : 0 ≤ 1-latitude d o.1 := sub_nonneg.mpr (latitude_lt_one d hd o.1).le
  simp only [effect, measurementVector, Matrix.smul_apply, projector_lift_succ_succ,
    Real.sq_sqrt ht, Complex.real_smul, Complex.ofReal_mul, mul_assoc]

theorem effect_zero_succ_phase_sum {d : ℕ} (b : Bool)
    (v : LibraryIndex d) (k : Fin d) :
    (∑ s : Fin 4, effect (b,s,v) 0 k.succ) = 0 := by
  simp only [effect, measurementVector, Matrix.smul_apply, projector_lift_zero_succ]
  simp [phase4, Fin.sum_univ_succ]

theorem effect_succ_zero_phase_sum {d : ℕ} (b : Bool)
    (v : LibraryIndex d) (j : Fin d) :
    (∑ s : Fin 4, effect (b,s,v) j.succ 0) = 0 := by
  simp only [effect, measurementVector, Matrix.smul_apply, projector_lift_succ_zero]
  simp [phase4, Fin.sum_univ_succ]

theorem head_normalization (d : ℕ) (hd : 0 < d) :
    (4 : ℝ) * (Fintype.card (LibraryIndex d) : ℝ) * effectWeight d *
      (latitude d false + latitude d true) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h4 : (4*(d:ℝ)+1) ≠ 0 := ne_of_gt (by positivity)
  have hp : (d:ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  rw [library_card]
  simp only [effectWeight, latitude, Bool.false_eq_true, ↓reduceIte,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

theorem tail_normalization (d : ℕ) (hd : 0 < d) :
    (4 : ℝ) * effectWeight d *
      ((1-latitude d false) + (1-latitude d true)) * (4*d+1) = 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h4 : (4*(d:ℝ)+1) ≠ 0 := ne_of_gt (by positivity)
  have hp : (d:ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  simp only [effectWeight, latitude, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring

theorem effect_sum_zero_zero {d : ℕ} (hd : 0 < d) :
    (∑ o : Outcome d, effect o) 0 0 = 1 := by
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, effect_zero_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.sum_bool,
    Complex.ofReal_mul, nsmul_eq_mul]
  have h := congrArg Complex.ofReal (head_normalization d hd)
  push_cast at h
  linear_combination h

theorem effect_sum_zero_succ {d : ℕ} (k : Fin d) :
    (∑ o : Outcome d, effect o) 0 k.succ = 0 := by
  simp only [Matrix.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finset.sum_comm]
  simp only [effect_zero_succ_phase_sum, Finset.sum_const_zero]

theorem effect_sum_succ_zero {d : ℕ} (j : Fin d) :
    (∑ o : Outcome d, effect o) j.succ 0 = 0 := by
  simp only [Matrix.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finset.sum_comm]
  simp only [effect_succ_zero_phase_sum, Finset.sum_const_zero]

theorem effect_sum_succ_succ {d : ℕ} (hd : 0 < d) (j k : Fin d) :
    (∑ o : Outcome d, effect o) j.succ k.succ =
      (1 : Matrix (Fin d) (Fin d) ℂ) j k := by
  have ht := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A j k)
    (library_projector_sum d)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at ht
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, effect_succ_succ hd,
    ← Finset.mul_sum, ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.sum_bool,
    nsmul_eq_mul]
  have h := congrArg Complex.ofReal (tail_normalization d hd)
  push_cast at h ⊢
  linear_combination (1 : Matrix (Fin d) (Fin d) ℂ) j k * h

/-- The explicitly constructed positive effects form a POVM in every dimension. -/
theorem effect_sum {d : ℕ} (hd : 0 < d) :
    (∑ o : Outcome d, effect o) = 1 := by
  ext j k
  refine Fin.cases ?_ (fun a => ?_) j <;> refine Fin.cases ?_ (fun b => ?_) k
  · simpa using effect_sum_zero_zero hd
  · simpa [Matrix.one_apply, Ne.symm (Fin.succ_ne_zero b)] using effect_sum_zero_succ b
  · simpa using effect_sum_succ_zero a
  · simpa [Matrix.one_apply] using effect_sum_succ_succ hd a b

end

end QubitOracle.AdaptiveDesign.GlobalPFSIC
