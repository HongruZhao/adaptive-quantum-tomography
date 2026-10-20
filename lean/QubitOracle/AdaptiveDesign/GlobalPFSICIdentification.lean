import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
/-!
# Global identification by the explicit finite PFSIC

Two latitudes separate the reference diagonal from the complement quadratic
form. Four phases separate both cross blocks. The concrete complement library
then determines every remaining matrix entry. This proves injectivity on all
complex matrices, which is stronger than the physical Hermitian restriction.
-/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

open scoped BigOperators

noncomputable section

def tailBlock {d : ℕ} (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := fun j k => A j.succ k.succ

def headRow {d : ℕ} (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (v : Fin d → ℂ) : ℂ := ∑ k, A 0 k.succ * v k

def headColumn {d : ℕ} (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (v : Fin d → ℂ) : ℂ := ∑ j, star (v j) * A j.succ 0

theorem quadratic_liftVector {d : ℕ}
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (alpha beta : ℝ) (s : Fin 4) (v : Fin d → ℂ) :
    quadratic A (liftVector alpha beta s v) =
      (alpha ^ 2 : ℝ) * A 0 0 + (beta ^ 2 : ℝ) * quadratic (tailBlock A) v +
        (alpha * beta : ℝ) *
          (phase4 s * headRow A v + star (phase4 s) * headColumn A v) := by
  have hphase : star (phase4 s) * phase4 s = 1 := by
    fin_cases s <;> norm_num [phase4, Complex.I_sq]
  have hhead (k : Fin d) :
      star (alpha : ℂ) * A 0 k.succ * (phase4 s * (beta : ℂ) * v k) =
        (alpha * beta : ℝ) * phase4 s * (A 0 k.succ * v k) := by
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hcolumn (j : Fin d) :
      star (phase4 s * (beta : ℂ) * v j) * A j.succ 0 * (alpha : ℂ) =
        (alpha * beta : ℝ) * star (phase4 s) * (star (v j) * A j.succ 0) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have htail (j k : Fin d) :
      star (phase4 s * (beta : ℂ) * v j) * A j.succ k.succ *
        (phase4 s * (beta : ℂ) * v k) =
        (beta ^ 2 : ℝ) * (star (v j) * A j.succ k.succ * v k) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
    calc
      _ = (star (phase4 s) * phase4 s) * (beta : ℂ) ^ 2 *
          (star (v j) * A j.succ k.succ * v k) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [hphase]; simp only [Complex.star_def]; ring
  simp only [quadratic, liftVector, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
  simp_rw [hhead, hcolumn, htail, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, headRow, headColumn, tailBlock, quadratic,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow, Complex.ofReal_mul]
  ring

theorem quadratic_measurementVector {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (b : Bool) (s : Fin 4) (v : LibraryIndex d) :
    quadratic A (measurementVector (b,s,v)) =
      (latitude d b : ℂ) * A 0 0 + ((1-latitude d b : ℝ) : ℂ) *
        quadratic (tailBlock A) (libraryVector v) +
      (Real.sqrt (latitude d b) * Real.sqrt (1-latitude d b) : ℝ) *
        (phase4 s * headRow A (libraryVector v) +
          star (phase4 s) * headColumn A (libraryVector v)) := by
  rw [measurementVector, quadratic_liftVector]
  rw [Real.sq_sqrt (latitude_pos d b).le,
    Real.sq_sqrt (sub_nonneg.mpr (latitude_lt_one d hd b).le)]

theorem quadratic_phase_sum {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (b : Bool) (v : LibraryIndex d) :
    (∑ s : Fin 4, quadratic A (measurementVector (b,s,v))) =
      4 * ((latitude d b : ℂ) * A 0 0 + ((1-latitude d b : ℝ) : ℂ) *
        quadratic (tailBlock A) (libraryVector v)) := by
  simp only [quadratic_measurementVector hd]
  simp [Fin.sum_univ_succ, phase4]
  ring

theorem latitude_false_lt_true (d : ℕ) : latitude d false < latitude d true := by
  simp only [latitude, Bool.false_eq_true, ↓reduceIte]
  exact div_lt_div_of_pos_right (by norm_num) (by positivity)

theorem two_latitudes_detect {d : ℕ} (x z : ℂ)
    (hfalse : (latitude d false : ℂ) * x + ((1-latitude d false : ℝ) : ℂ) * z = 0)
    (htrue : (latitude d true : ℂ) * x + ((1-latitude d true : ℝ) : ℂ) * z = 0) :
    x = 0 ∧ z = 0 := by
  have hdiff : (latitude d true : ℂ) - (latitude d false : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt (latitude_false_lt_true d))
  push_cast at hfalse htrue
  have heq : x = z := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show
      ((latitude d true : ℂ) - (latitude d false : ℂ)) * (x-z) = 0 by
        linear_combination htrue - hfalse)).resolve_left hdiff
  have hz : z = 0 := by rw [heq] at hfalse; linear_combination hfalse
  exact ⟨heq.trans hz, hz⟩

theorem quadratic_measurementVector_eq_zero_iff {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ o : Outcome d, quadratic A (measurementVector o) = 0) ↔ A = 0 := by
  constructor
  · intro h
    have hradial (b : Bool) (v : LibraryIndex d) :
        (latitude d b : ℂ) * A 0 0 + ((1-latitude d b : ℝ) : ℂ) *
          quadratic (tailBlock A) (libraryVector v) = 0 := by
      have hs := quadratic_phase_sum hd A b v
      have hz : (∑ s : Fin 4, quadratic A (measurementVector (b,s,v))) = 0 :=
        Finset.sum_eq_zero (fun s _ => h (b,s,v))
      rw [hz] at hs
      linear_combination (-1/4 : ℂ) * hs
    have hhead : A 0 0 = 0 :=
      (two_latitudes_detect _ _
        (hradial false (.inl ⟨0,hd⟩)) (hradial true (.inl ⟨0,hd⟩))).1
    have htail : tailBlock A = 0 := by
      apply (library_quadratic_eq_zero_iff _).mp
      intro v
      exact (two_latitudes_detect _ _ (hradial false v) (hradial true v)).2
    have hscale :
        ((Real.sqrt (latitude d false) * Real.sqrt (1-latitude d false) : ℝ) : ℂ) ≠ 0 := by
      have hp : 0 < Real.sqrt (latitude d false) * Real.sqrt (1-latitude d false) :=
        mul_pos (Real.sqrt_pos.mpr (latitude_pos d false))
          (Real.sqrt_pos.mpr (sub_pos.mpr (latitude_lt_one d hd false)))
      exact_mod_cast hp.ne'
    have hcross (v : LibraryIndex d) :
        headRow A (libraryVector v) = 0 ∧ headColumn A (libraryVector v) = 0 := by
      have h0 := h (false,0,v)
      have h1 := h (false,1,v)
      rw [quadratic_measurementVector hd, hhead, htail] at h0 h1
      simp only [quadratic, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
        zero_add, add_zero] at h0 h1
      have h0' := (mul_eq_zero.mp h0).resolve_left hscale
      have h1' := (mul_eq_zero.mp h1).resolve_left hscale
      simp only [phase4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        star_one, one_mul, Complex.star_def, Complex.conj_I] at h0' h1'
      have heq : headRow A (libraryVector v) = headColumn A (libraryVector v) := by
        apply sub_eq_zero.mp
        apply (mul_eq_zero.mp (show Complex.I *
          (headRow A (libraryVector v)-headColumn A (libraryVector v)) = 0 by
            linear_combination h1')).resolve_left Complex.I_ne_zero
      have hc : headColumn A (libraryVector v) = 0 := by
        rw [heq] at h0'
        linear_combination (1/2 : ℂ) * h0'
      exact ⟨heq.trans hc, hc⟩
    ext j k
    change A j k = 0
    refine Fin.cases ?_ (fun a => ?_) j <;> refine Fin.cases ?_ (fun b => ?_) k
    · exact hhead
    · simpa [headRow, libraryVector, coordinate, Pi.single_apply] using (hcross (.inl b)).1
    · simpa [headColumn, libraryVector, coordinate, Pi.single_apply] using (hcross (.inl a)).2
    · exact congrFun (congrFun htail a) b
  · rintro rfl o
    simp [quadratic]

/-- The concrete physical measurement determines every matrix globally. -/
theorem measurement_quadratic_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ =>
      fun o : Outcome d => quadratic A (measurementVector o)) := by
  intro A B h
  apply sub_eq_zero.mp
  apply (quadratic_measurementVector_eq_zero_iff hd (A-B)).mp
  intro o
  have ho := congrFun h o
  simpa [quadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    using sub_eq_zero.mpr ho

end

end QubitOracle.AdaptiveDesign.GlobalPFSIC
