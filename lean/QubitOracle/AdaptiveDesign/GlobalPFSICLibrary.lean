import Mathlib

/-!
# Explicit finite complement library for a globally identifying PFSIC

The construction uses a redundant ordered-pair library to avoid choosing an
ordering on unordered pairs.  In complex dimension `d`, the library contains
`d * (4*d+1)` labelled unit vectors and its rank-one projectors sum to
`(4*d+1) I`.  Labels with equal pair indices repeat a coordinate vector.
This redundancy does not affect informational completeness or Fisher symmetry.
-/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

open scoped BigOperators ComplexOrder

noncomputable section

/-- The four relative phases used for real and imaginary polarization. -/
def phase4 : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

@[simp] theorem phase4_normSq (s : Fin 4) : Complex.normSq (phase4 s) = 1 := by
  fin_cases s <;> norm_num [phase4]

@[simp] theorem sum_phase4 : (∑ s : Fin 4, phase4 s) = 0 := by
  norm_num [phase4, Fin.sum_univ_succ]

@[simp] theorem sum_phase4_sq : (∑ s : Fin 4, phase4 s ^ 2) = 0 := by
  norm_num [phase4, Fin.sum_univ_succ, Complex.I_sq]

/-- A coordinate vector in the complex complement. -/
def coordinate {d : ℕ} (j : Fin d) : Fin d → ℂ := Pi.single j 1

/-- The rank-one outer product, without any trace normalization. -/
def projector {d : ℕ} (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec v (star v)

@[simp] theorem projector_apply {d : ℕ} (v : Fin d → ℂ) (a b : Fin d) :
    projector v a b = v a * star (v b) := rfl

theorem projector_posSemidef {d : ℕ} (v : Fin d → ℂ) :
    (projector v).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v

/-- Normalized two-coordinate vector. Equal indices repeat the coordinate vector. -/
def pairVector {d : ℕ} (j k : Fin d) (s : Fin 4) : Fin d → ℂ :=
  if j = k then coordinate j
  else fun a => (coordinate j a + phase4 s * coordinate k a) / (Real.sqrt 2 : ℂ)

/-- Fully explicit labels; no unproved finite-frame certificate is supplied. -/
abbrev LibraryIndex (d : ℕ) := Fin d ⊕ (Fin d × Fin d × Fin 4)

def libraryVector {d : ℕ} : LibraryIndex d → Fin d → ℂ
  | .inl j => coordinate j
  | .inr (j, k, s) => pairVector j k s

theorem library_card (d : ℕ) : Fintype.card (LibraryIndex d) = d * (4*d+1) := by
  simp [LibraryIndex]
  ring

@[simp] theorem coordinate_normSq {d : ℕ} (j : Fin d) :
    (∑ a, Complex.normSq (coordinate j a)) = 1 := by
  classical
  simp [coordinate, Pi.single_apply]

theorem pairVector_normSq {d : ℕ} (j k : Fin d) (s : Fin 4) :
    (∑ a, Complex.normSq (pairVector j k s a)) = 1 := by
  classical
  by_cases hjk : j = k
  · simp [pairVector, hjk]
  · have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hn : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
      simpa [Complex.normSq_ofReal] using hsq
    simp only [pairVector, if_neg hjk]
    have hpoint (a : Fin d) :
        Complex.normSq ((coordinate j a + phase4 s * coordinate k a) /
          (Real.sqrt 2 : ℂ)) =
          (if a = j then (1/2 : ℝ) else 0) +
            (if a = k then (1/2 : ℝ) else 0) := by
      by_cases haj : a = j
      · subst a
        simp [coordinate, Pi.single_apply, hjk, hn]
      · by_cases hak : a = k
        · subst a
          simp [coordinate, Pi.single_apply, hjk, Ne.symm hjk, hn]
        · simp [coordinate, Pi.single_apply, haj, hak, Ne.symm haj, Ne.symm hak]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    norm_num

@[simp] theorem libraryVector_normSq {d : ℕ} (v : LibraryIndex d) :
    (∑ a, Complex.normSq (libraryVector v a)) = 1 := by
  rcases v with j | ⟨j, k, s⟩
  · exact coordinate_normSq j
  · exact pairVector_normSq j k s

theorem coordinate_projector_sum (d : ℕ) :
    (∑ j : Fin d, projector (coordinate j)) = 1 := by
  classical
  ext a b
  simp [Matrix.sum_apply, projector, Matrix.vecMulVec_apply, coordinate, Pi.single_apply,
    Matrix.one_apply]

theorem phase4_polarization (a b c e : ℂ) :
    (∑ s : Fin 4, (a + phase4 s * b) * star (c + phase4 s * e)) =
      4 * (a * star c + b * star e) := by
  simp [phase4, Fin.sum_univ_succ, map_add, map_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem pairVector_projector_phase_sum {d : ℕ} (j k : Fin d) (hjk : j ≠ k) :
    (∑ s : Fin 4, projector (pairVector j k s)) =
      (2 : ℂ) • (projector (coordinate j) + projector (coordinate k)) := by
  ext a b
  have hden : (Real.sqrt 2 : ℂ) * star (Real.sqrt 2 : ℂ) = 2 := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    norm_cast
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  simp only [Matrix.sum_apply, projector_apply, pairVector, if_neg hjk,
    star_div₀, div_mul_div_comm, hden, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul]
  rw [← Finset.sum_div, phase4_polarization]
  ring

theorem pairVector_projector_phase_sum_all {d : ℕ} (j k : Fin d) :
    (∑ s : Fin 4, projector (pairVector j k s)) =
      (2 : ℂ) • (projector (coordinate j) + projector (coordinate k)) := by
  by_cases hjk : j = k
  · subst k
    ext a b
    simp [pairVector, Fin.sum_univ_succ, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul]
    ring
  · exact pairVector_projector_phase_sum j k hjk

theorem library_projector_sum (d : ℕ) :
    (∑ v : LibraryIndex d, projector (libraryVector v)) =
      (4 * (d : ℂ) + 1) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  ext a b
  have hp (j k : Fin d) := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b)
    (pairVector_projector_phase_sum_all j k)
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hp
  have hc := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M a b)
    (coordinate_projector_sum d)
  simp only [Matrix.sum_apply] at hc
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, libraryVector]
  simp_rw [hp, mul_add, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum, hc]
  ring

/-- Complex quadratic measurement; real-valued on Hermitian matrices. -/
def quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : ℂ :=
  ∑ a, ∑ b, star (v a) * A a b * v b

@[simp] theorem quadratic_coordinate {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (j : Fin d) :
    quadratic A (coordinate j) = A j j := by
  classical
  simp [quadratic, coordinate, Pi.single_apply]

theorem quadratic_pairVector {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) (s : Fin 4) (hjk : j ≠ k) :
    quadratic A (pairVector j k s) =
      (A j j + phase4 s * A j k + star (phase4 s) * A k j + A k k)/2 := by
  classical
  have hr : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hz : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  simp only [quadratic, pairVector, if_neg hjk, star_div₀, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, coordinate, Pi.single_apply]
  simp_rw [div_eq_mul_inv, add_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, one_mul,
    apply_ite, map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases s <;> simp [phase4, hjk, Ne.symm hjk]
    <;> field_simp
    <;> ring_nf
    <;> simp [hr, Complex.I_sq]
    <;> ring

/-- The displayed finite library detects every matrix, not just tangent vectors. -/
theorem library_quadratic_eq_zero_iff {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (∀ v : LibraryIndex d, quadratic A (libraryVector v) = 0) ↔ A = 0 := by
  constructor
  · intro h
    have hd (j : Fin d) : A j j = 0 := by
      simpa [libraryVector] using h (.inl j)
    ext j k
    change A j k = 0
    by_cases hjk : j = k
    · subst k
      exact hd j
    · have h0 := h (.inr (j,k,0))
      have h1 := h (.inr (j,k,1))
      simp only [libraryVector, quadratic_pairVector A j k _ hjk] at h0 h1
      simp [phase4, hd] at h0 h1
      have heq : A j k = A k j := by
        apply sub_eq_zero.mp
        apply (mul_eq_zero.mp (show Complex.I * (A j k - A k j) = 0 by
          linear_combination h1)).resolve_left Complex.I_ne_zero
      rw [← heq] at h0
      linear_combination (1/2 : ℂ) * h0
  · rintro rfl v
    simp [quadratic]

/-- Global linear identification by the concrete library probabilities. -/
theorem library_quadratic_injective {d : ℕ} :
    Function.Injective (fun A : Matrix (Fin d) (Fin d) ℂ =>
      fun v : LibraryIndex d => quadratic A (libraryVector v)) := by
  intro A B h
  apply sub_eq_zero.mp
  apply (library_quadratic_eq_zero_iff (A-B)).mp
  intro v
  have hv := congrFun h v
  simpa [quadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
    using sub_eq_zero.mpr hv

end

end QubitOracle.AdaptiveDesign.GlobalPFSIC
