import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.FiniteGillMassar

/-! # Exact Born Fisher information of the constructed globally identifying POVM -/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

open scoped BigOperators ComplexOrder

noncomputable section

def measurementPOVM (d : ℕ) (hd : 0 < d) :
    FinitePOVM (Fin (d+1)) (Outcome d) where
  effect := effect
  positive := effect_posSemidef hd
  complete := effect_sum hd

def phaseCoordinate {d : ℕ} (s : Fin 4) (v : Fin d → ℂ) : TangentIndex d → ℝ
  | .inl j => (phase4 s * v j).re
  | .inr j => (phase4 s * v j).im

def realifiedProjector {d : ℕ} (v : Fin d → ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ
  | .inl j, .inl k => (projector v j k).re
  | .inr j, .inr k => (projector v j k).re
  | .inl j, .inr k => -(projector v j k).im
  | .inr j, .inl k => (projector v j k).im

theorem phaseCoordinate_covariance {d : ℕ} (v : Fin d → ℂ)
    (x y : TangentIndex d) :
    (∑ s : Fin 4, phaseCoordinate s v x * phaseCoordinate s v y) =
      2 * realifiedProjector v x y := by
  rcases x with j | j <;> rcases y with k | k
    <;> simp [phaseCoordinate, realifiedProjector, projector_apply,
      phase4, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
    <;> ring

theorem realifiedProjector_family_sum {d : ℕ} {V : Type*} [Fintype V]
    (vectors : V → Fin d → ℂ) (c : ℝ)
    (hframe : (∑ v, projector (vectors v)) =
      (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) :
    (∑ v, realifiedProjector (vectors v)) =
      c • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  classical
  have hreal (j k : Fin d) : (∑ v, (projector (vectors v) j k).re) =
      c * (1 : Matrix (Fin d) (Fin d) ℝ) j k := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j k).re) hframe
    by_cases hjk : j = k <;>
      simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, hjk] using h
  have himag (j k : Fin d) : (∑ v, (projector (vectors v) j k).im) = 0 := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j k).im) hframe
    by_cases hjk : j = k <;>
      simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, hjk] using h
  ext x y
  rcases x with j | j <;> rcases y with k | k
  · simpa only [realifiedProjector, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Sum.inl.injEq] using hreal j k
  · simp only [realifiedProjector, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, reduceCtorEq, if_false, mul_zero]
    rw [Finset.sum_neg_distrib, himag]
    simp
  · simpa only [realifiedProjector, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, reduceCtorEq, if_false, mul_zero] using himag j k
  · simpa only [realifiedProjector, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, Sum.inr.injEq] using hreal j k

theorem realifiedProjector_library_sum (d : ℕ) :
    (∑ v : LibraryIndex d, realifiedProjector (libraryVector v)) =
      (4*(d:ℝ)+1) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  apply realifiedProjector_family_sum
  simpa using library_projector_sum d

theorem phaseCoordinate_family_covariance {d : ℕ} {V : Type*} [Fintype V]
    (vectors : V → Fin d → ℂ) (c : ℝ)
    (hframe : (∑ v, projector (vectors v)) =
      (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))
    (x y : TangentIndex d) :
    (∑ s : Fin 4, ∑ v, phaseCoordinate s (vectors v) x * phaseCoordinate s (vectors v) y) =
      (2*c) * (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) x y := by
  rw [Finset.sum_comm]
  simp_rw [phaseCoordinate_covariance, ← Finset.mul_sum]
  have h := congrArg (fun A : Matrix (TangentIndex d) (TangentIndex d) ℝ => A x y)
    (realifiedProjector_family_sum vectors c hframe)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [h]
  ring

theorem phaseCoordinate_library_covariance (d : ℕ)
    (x y : TangentIndex d) :
    (∑ s : Fin 4, ∑ v : LibraryIndex d,
      phaseCoordinate s (libraryVector v) x * phaseCoordinate s (libraryVector v) y) =
      (2*(4*(d:ℝ)+1)) * (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) x y := by
  rw [Finset.sum_comm]
  simp_rw [phaseCoordinate_covariance, ← Finset.mul_sum]
  have h := congrArg (fun A : Matrix (TangentIndex d) (TangentIndex d) ℝ => A x y)
    (realifiedProjector_library_sum d)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [h]
  ring

theorem measurementPOVM_referenceProbability (d : ℕ) (hd : 0 < d) (o : Outcome d) :
    referenceProbability (measurementPOVM d hd) o = effectWeight d * latitude d o.1 :=
  effect_reference_entry o

theorem measurementPOVM_referenceGradient (d : ℕ) (hd : 0 < d)
    (o : Outcome d) (x : TangentIndex d) :
    referenceGradient (measurementPOVM d hd) o x =
      effectWeight d * Real.sqrt (latitude d o.1) * Real.sqrt (1-latitude d o.1) *
        phaseCoordinate o.2.1 (libraryVector o.2.2) x := by
  rcases x with j | j
  all_goals
    simp only [referenceGradient, measurementPOVM, effect, measurementVector,
      Matrix.smul_apply, projector_lift_zero_succ, Complex.real_smul]
    simp [phaseCoordinate, Complex.mul_re, Complex.mul_im]
    ring

/-- Scalar cancellation shared by every unitary-transported complement library. -/
theorem fisher_ratio_cancel (c t a b : ℝ) (hc : 0 < c) (ht : 0 < t) (hu : t ≤ 1) :
    safeRatio (c*t)
      ((c * Real.sqrt t * Real.sqrt (1-t) * a) *
        (c * Real.sqrt t * Real.sqrt (1-t) * b)) =
      c * (1-t) * (a*b) := by
  rw [safeRatio, if_neg (ne_of_gt (mul_pos hc ht))]
  have ht2 := Real.sq_sqrt ht.le
  have hu2 := Real.sq_sqrt (sub_nonneg.mpr hu)
  field_simp
  simp only [ht2, hu2]

theorem measurementPOVM_referenceFisher_term (d : ℕ) (hd : 0 < d)
    (o : Outcome d) (x y : TangentIndex d) :
    safeRatio (referenceProbability (measurementPOVM d hd) o)
      (referenceGradient (measurementPOVM d hd) o x *
        referenceGradient (measurementPOVM d hd) o y) =
      effectWeight d * (1-latitude d o.1) *
        (phaseCoordinate o.2.1 (libraryVector o.2.2) x *
          phaseCoordinate o.2.1 (libraryVector o.2.2) y) := by
  have hc := effectWeight_pos d hd
  have ht := latitude_pos d o.1
  have hu : 0 ≤ 1-latitude d o.1 := sub_nonneg.mpr (latitude_lt_one d hd o.1).le
  rw [measurementPOVM_referenceProbability, measurementPOVM_referenceGradient,
    measurementPOVM_referenceGradient, safeRatio,
    if_neg (ne_of_gt (mul_pos hc ht))]
  have ht2 := Real.sq_sqrt ht.le
  have hu2 := Real.sq_sqrt hu
  field_simp
  simp only [ht2, hu2]

theorem measurementPOVM_referenceFisher (d : ℕ) (hd : 0 < d) :
    referenceFisher (measurementPOVM d hd) =
      (1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  ext x y
  simp only [referenceFisher, measurementPOVM_referenceFisher_term,
    Fintype.sum_prod_type, ← Finset.mul_sum, phaseCoordinate_library_covariance,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_bool]
  have hn := tail_normalization d hd
  linear_combination (1/2 : ℝ) * (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) x y * hn

end

end QubitOracle.AdaptiveDesign.GlobalPFSIC
