import Mathlib

/-! Deterministic finite-dimensional least-squares continuity. No statistical
limit theorem or consistency statement is assumed in this file. -/
namespace QubitOracle.AdaptiveDesign

open Filter Matrix
open scoped Topology BigOperators
noncomputable section

theorem inverse_mulVec_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Nat → Matrix ι ι Real} {b : Nat → ι → Real}
    {A₀ : Matrix ι ι Real} {theta : ι → Real}
    (hA : Tendsto A atTop (nhds A₀)) (hdet : IsUnit A₀.det)
    (hb : Tendsto b atTop (nhds (A₀.mulVec theta))) :
    Tendsto (fun n => (A n)⁻¹.mulVec (b n)) atTop (nhds theta) := by
  have hinv : ContinuousAt (fun M : Matrix ι ι Real => M⁻¹) A₀ := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet.ne_zero)
  have hprod := (continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    ((hinv.tendsto.comp hA).prodMk_nhds hb)
  simpa only [Function.comp_def, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using hprod

theorem average_uncenter {a : Nat → Real} {c : Real}
    (h : Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), (a k - c)) atTop (nhds 0)) :
    Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), a k) atTop (nhds c) := by
  have hcount : Tendsto (fun N : Nat => (N : Real)⁻¹ * ((N : Real)+1))
      atTop (nhds 1) := by
    have hi : Tendsto (fun N : Nat => (N : Real)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h : Tendsto (fun N : Nat => 1 + (N : Real)⁻¹) atTop (nhds 1) := by
      simpa using hi.const_add 1
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
    have hne : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  have hc := hcount.mul_const c
  convert h.add hc using 1
  · ext N
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  · ring

def normalizedRidgeGram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ridge : Real) (a : Nat → ι → Real) (N : Nat) : Matrix ι ι Real :=
  (N : Real)⁻¹ • (ridge • (1 : Matrix ι ι Real) +
    ∑ k ∈ Finset.range (N+1), Matrix.vecMulVec (a k) (a k))

def normalizedRidgeResponse {ι : Type*} [Fintype ι]
    (a : Nat → ι → Real) (y : Nat → Real) (N : Nat) : ι → Real :=
  (N : Real)⁻¹ • ∑ k ∈ Finset.range (N+1), y k • a k

def normalizedRidgeEstimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ridge : Real) (a : Nat → ι → Real) (y : Nat → Real) (N : Nat) : ι → Real :=
  (normalizedRidgeGram ridge a N)⁻¹.mulVec (normalizedRidgeResponse a y N)

theorem inverse_smul_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Real) (k : Real) (hk : k ≠ 0) :
    (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · letI := invertibleOfNonzero hk
    simpa only [invOf_eq_inv] using Matrix.inv_smul A k hA
  · have hz : A.det = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hA
    have hscaled : ¬IsUnit (k • A).det := by
      simp [Matrix.det_smul, hz]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hA, smul_zero]

theorem normalizedRidgeEstimate_eq_raw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ridge : Real) (a : Nat → ι → Real) (y : Nat → Real)
    (N : Nat) (hN : N ≠ 0) :
    normalizedRidgeEstimate ridge a y N =
      (ridge • (1 : Matrix ι ι Real) +
        ∑ k ∈ Finset.range (N+1), Matrix.vecMulVec (a k) (a k))⁻¹.mulVec
        (∑ k ∈ Finset.range (N+1), y k • a k) := by
  have hn : (N : Real) ≠ 0 := by exact_mod_cast hN
  simp only [normalizedRidgeEstimate, normalizedRidgeGram, normalizedRidgeResponse,
    inverse_smul_real _ _ (inv_ne_zero hn), Matrix.smul_mulVec,
    Matrix.mulVec_smul, smul_smul, inv_inv, inv_mul_cancel₀ hn, one_smul]

/-- A constant positive limiting Gram matrix proves consistency of the literal
all-observation ridge formula. The hypotheses are centered scalar sums; the
adaptive Born model supplies them separately by a bounded martingale law. -/
theorem normalizedRidgeEstimate_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ridge : Real) (a : Nat → ι → Real) (y : Nat → Real)
    (theta : ι → Real) (c : Real) (hc : c ≠ 0)
    (hgram : ∀ i j, Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), (a k i * a k j - c * (if i=j then 1 else 0)))
      atTop (nhds 0))
    (hresponse : ∀ i, Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), (a k i * y k - c * theta i))
      atTop (nhds 0)) :
    Tendsto (normalizedRidgeEstimate ridge a y) atTop (nhds theta) := by
  have hG : Tendsto (normalizedRidgeGram ridge a) atTop
      (nhds (c • (1 : Matrix ι ι Real))) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    have h := average_uncenter (hgram i j)
    have hr : Tendsto (fun N : Nat => (N : Real)⁻¹ *
        (ridge * (if i=j then 1 else 0))) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
        (ridge * (if i=j then 1 else 0))
    convert hr.add h using 1
    · ext N
      simp [normalizedRidgeGram, Matrix.vecMulVec, Matrix.one_apply,
        Matrix.sum_apply, mul_add]
    · simp [Matrix.one_apply]
  have hb : Tendsto (normalizedRidgeResponse a y) atTop
      (nhds ((c • (1 : Matrix ι ι Real)).mulVec theta)) := by
    apply tendsto_pi_nhds.2
    intro i
    simpa [normalizedRidgeResponse, Finset.sum_apply, Matrix.smul_mulVec,
      mul_comm] using average_uncenter (hresponse i)
  have hdet : IsUnit (c • (1 : Matrix ι ι Real)).det := by
    simp only [Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.2 (pow_ne_zero _ hc)
  exact inverse_mulVec_tendsto hG hdet hb

end
end QubitOracle.AdaptiveDesign
