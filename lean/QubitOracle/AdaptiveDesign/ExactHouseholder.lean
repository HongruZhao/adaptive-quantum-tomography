import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import Mathlib

/-! A deterministic phase-adjusted Householder completion with a denominator
bounded below by two. No random unitary or arbitrary complement is selected. -/
namespace QubitOracle.AdaptiveDesign.ExactHouseholder
open GlobalPFSIC
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2000000

def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖:ℂ)
lemma phase_normSq (z : ℂ) : Complex.normSq (phase z) = 1 := by
  by_cases hz : z = 0
  · simp [phase,hz]
  · simp only [phase,if_neg hz,map_div₀,Complex.normSq_ofReal]
    rw [← pow_two,Complex.sq_norm]
    exact div_self (fun h => hz (Complex.normSq_eq_zero.mp h))
lemma phase_star_mul (z : ℂ) : (starRingEnd ℂ) (phase z) * phase z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, phase_normSq]
  rfl
lemma phase_mul_star (z : ℂ) : phase z * (starRingEnd ℂ) (phase z) = 1 := by
  rw [mul_comm, phase_star_mul]
lemma phase_align (z : ℂ) : (starRingEnd ℂ) (phase z) * z = (‖z‖:ℂ) := by
  by_cases hz : z = 0
  · simp [phase,hz]
  have hn : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  calc
    _ = (star z * z) / (‖z‖:ℂ) := by simp [phase,hz,star_div,div_mul_eq_mul_div]
    _ = (‖z‖:ℂ)^2 / (‖z‖:ℂ) := by
      simp only [Complex.star_def]
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
      push_cast
      rfl
    _ = _ := by field_simp

def vector {d : ℕ} (psi : Fin (d+1) → ℂ) : Fin (d+1) → ℂ :=
  fun i => coordinate 0 i + (starRingEnd ℂ) (phase (psi 0)) * psi i

def denominator {d : ℕ} (psi : Fin (d+1) → ℂ) : ℝ := 2*(1+‖psi 0‖)
lemma denominator_pos {d : ℕ} (psi : Fin (d+1) → ℂ) : 0 < denominator psi := by
  unfold denominator
  positivity
lemma denominator_lower {d : ℕ} (psi : Fin (d+1) → ℂ) : 2 ≤ denominator psi := by
  unfold denominator
  nlinarith [norm_nonneg (psi 0)]
lemma vector_zero {d : ℕ} (psi : Fin (d+1) → ℂ) :
    vector psi 0 = ((1+‖psi 0‖:ℝ):ℂ) := by simp [vector,coordinate,phase_align]
lemma vector_succ {d : ℕ} (psi : Fin (d+1) → ℂ) (i : Fin d) :
    vector psi i.succ = (starRingEnd ℂ) (phase (psi 0)) * psi i.succ := by simp [vector,coordinate]
lemma vector_normSq {d : ℕ} (psi : Fin (d+1) → ℂ)
    (hpsi : ∑ i, Complex.normSq (psi i) = 1) :
    ∑ i, Complex.normSq (vector psi i) = denominator psi := by
  rw [Fin.sum_univ_succ] at hpsi ⊢
  simp only [vector_zero,vector_succ,map_mul,Complex.normSq_conj,phase_normSq,one_mul,
    Complex.normSq_ofReal]
  unfold denominator
  nlinarith [Complex.sq_norm (psi 0)]
lemma denominator_upper {d : ℕ} (psi : Fin (d+1) → ℂ)
    (hpsi : ∑ i, Complex.normSq (psi i) = 1) : denominator psi ≤ 4 := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (fun i _ => Complex.normSq_nonneg (psi i)) (Finset.mem_univ (0 : Fin (d+1)))
  rw [hpsi, ← Complex.sq_norm] at h
  unfold denominator
  nlinarith [norm_nonneg (psi 0)]

lemma projector_square {n : ℕ} (v : Fin n → ℂ) :
    projector v * projector v = ((∑ i, Complex.normSq (v i):ℝ):ℂ) • projector v := by
  ext a b
  simp only [Matrix.mul_apply,projector_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ = (∑ i, star (v i)*v i) * (v a * star (v b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]

def lineProjector {d : ℕ} (psi : Fin (d+1) → ℂ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  ((denominator psi:ℂ)⁻¹) • projector (vector psi)
lemma lineProjector_selfadjoint {d : ℕ} (psi : Fin (d+1) → ℂ) :
    (lineProjector psi).conjTranspose = lineProjector psi := by
  simp only [lineProjector,Matrix.conjTranspose_smul,
    (projector_posSemidef (vector psi)).isHermitian.eq,Complex.star_def,map_inv₀,Complex.conj_ofReal]
lemma lineProjector_idempotent {d : ℕ} (psi : Fin (d+1) → ℂ)
    (hpsi : ∑ i, Complex.normSq (psi i) = 1) :
    lineProjector psi * lineProjector psi = lineProjector psi := by
  have hs : (denominator psi:ℂ) ≠ 0 := by exact_mod_cast (denominator_pos psi).ne'
  simp only [lineProjector,smul_mul_assoc,mul_smul_comm,smul_smul,projector_square,
    vector_normSq psi hpsi]
  congr 1
  field_simp

def matrix {d : ℕ} (psi : Fin (d+1) → ℂ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  phase (psi 0) • (lineProjector psi + lineProjector psi - 1)

lemma matrix_unitary {d : ℕ} (psi : Fin (d+1) → ℂ)
    (hpsi : ∑ i, Complex.normSq (psi i) = 1) :
    matrix psi ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
  let Q := lineProjector psi
  have hQ : Q*Q=Q := lineProjector_idempotent psi hpsi
  have hH : (Q+Q-1)*(Q+Q-1)=1 := by
    calc
      _ = Q*Q+Q*Q+Q*Q+Q*Q-(Q+Q+Q+Q)+1 := by noncomm_ring
      _ = _ := by rw [hQ]; abel
  rw [Matrix.mem_unitaryGroup_iff]
  change matrix psi * (matrix psi).conjTranspose = 1
  simp only [matrix,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_add,
    Matrix.conjTranspose_one,lineProjector_selfadjoint,smul_mul_assoc,mul_smul_comm,smul_smul,
    Complex.star_def,phase_mul_star,phase_star_mul,one_smul]
  exact hH

lemma matrix_firstColumn {d : ℕ} (psi : Fin (d+1) → ℂ) :
    (fun i => matrix psi i 0) = psi := by
  have hr : ((1+‖psi 0‖:ℝ):ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+‖psi 0‖:ℝ) ≠ 0)
  have hs : (denominator psi:ℂ) ≠ 0 := by exact_mod_cast (denominator_pos psi).ne'
  have hc : (denominator psi:ℂ)⁻¹ * (((1+‖psi 0‖:ℝ):ℂ)) +
      (denominator psi:ℂ)⁻¹ * (((1+‖psi 0‖:ℝ):ℂ)) = 1 := by
    unfold denominator
    push_cast
    field_simp
    ring
  funext i
  simp only [matrix,Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,lineProjector,
    projector_apply,smul_eq_mul,vector_zero,Complex.star_def,Complex.conj_ofReal]
  calc
    _ = phase (psi 0) * (vector psi i - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) i 0) := by
      have hh := congrArg (fun z : ℂ => z * vector psi i) hc
      linear_combination phase (psi 0) * hh
    _ = psi i := by
      simp only [vector,coordinate,Pi.single_apply,Matrix.one_apply]
      have heq : (if i=0 then (1:ℂ) else 0) = (if 0=i then 1 else 0) := by
        simp only [eq_comm]
      rw [heq]
      have hg := phase_mul_star (psi 0)
      linear_combination psi i * hg
end
end QubitOracle.AdaptiveDesign.ExactHouseholder
