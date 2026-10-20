import QubitOracle.Paper.PureStateFoundations
/-! Algebraic projective-state assertions in Section 2.3.

The nonzero-vector quotient is Mathlib's actual `Projectivization`.
Unit vectors use the sum of squared complex moduli (the Euclidean norm
squared), not the max norm on the underlying function space.
No smooth-manifold assertion is assumed or claimed in this module.
-/
namespace QubitOracle.Paper.ProjectiveStateGeometry
open QubitOracle.Paper
open scoped BigOperators ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normSq_nonnegative (z : ι → ℂ) : 0 ≤ pureStateNormSq z :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (z i))

theorem normSq_eq_zero_iff (z : ι → ℂ) : pureStateNormSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : Complex.normSq (z i) ≤ pureStateNormSq z :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
    have hzero : Complex.normSq (z i) = 0 := le_antisymm (hz ▸ hi) (Complex.normSq_nonneg _)
    exact Complex.normSq_eq_zero.mp hzero
  · rintro rfl
    simp [pureStateNormSq]

theorem normSq_positive (z : ι → ℂ) (hz : z ≠ 0) : 0 < pureStateNormSq z :=
  lt_of_le_of_ne (normSq_nonnegative z) (Ne.symm (mt (normSq_eq_zero_iff z).mp hz))

theorem normSq_smul (c : ℂ) (z : ι → ℂ) :
    pureStateNormSq (c • z) = Complex.normSq c * pureStateNormSq z := by
  simp [pureStateNormSq, Complex.normSq_mul, Finset.mul_sum]

theorem density_smul (c : ℂ) (z : ι → ℂ) :
    rankOneDensity (c • z) = (Complex.normSq c : ℂ) • rankOneDensity z := by
  ext i j
  simp only [rankOneDensity, Pi.smul_apply, smul_eq_mul, star_mul, Matrix.smul_apply]
  rw [Complex.normSq_eq_conj_mul_self]
  change (c * z i) * (star (z j) * star c) = (star c * c) * (z i * star (z j))
  ring

theorem density_mulVec (z w : ι → ℂ) :
    (rankOneDensity z).mulVec w = basisBornAmplitude z w • z := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rankOneDensity, basisBornAmplitude,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem self_amplitude (z : ι → ℂ) :
    basisBornAmplitude z z = (pureStateNormSq z : ℂ) := by
  simp [basisBornAmplitude, pureStateNormSq, Complex.normSq_eq_conj_mul_self]

theorem density_square (z : ι → ℂ) :
    rankOneDensity z * rankOneDensity z =
      (pureStateNormSq z : ℂ) • rankOneDensity z := by
  ext i j
  simp only [Matrix.mul_apply, rankOneDensity, Matrix.smul_apply, smul_eq_mul]
  rw [show (pureStateNormSq z : ℂ) = ∑ k, star (z k) * z k by
    simp [pureStateNormSq, Complex.normSq_eq_conj_mul_self]]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem density_positive (z : ι → ℂ) : (rankOneDensity z).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star z

def rayProjector (z : ι → ℂ) : Matrix ι ι ℂ :=
  (pureStateNormSq z : ℂ)⁻¹ • rankOneDensity z

theorem rayProjector_trace (z : ι → ℂ) (hz : z ≠ 0) :
    Matrix.trace (rayProjector z) = 1 := by
  rw [rayProjector, Matrix.trace_smul, rankOneDensity_trace_eq_normSq]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z hz)))

theorem rayProjector_idempotent (z : ι → ℂ) (hz : z ≠ 0) :
    rayProjector z * rayProjector z = rayProjector z := by
  have hn : (pureStateNormSq z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z hz))
  simp only [rayProjector, Matrix.smul_mul, Matrix.mul_smul, smul_smul, density_square]
  congr 1
  field_simp

theorem rayProjector_scalar_invariant (z : ι → ℂ) (c : ℂ) (hc : c ≠ 0) :
    rayProjector (c • z) = rayProjector z := by
  have hn : (Complex.normSq c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mt Complex.normSq_eq_zero.mp hc)
  simp only [rayProjector, normSq_smul, Complex.ofReal_mul, density_smul,
    mul_inv_rev, smul_smul]
  congr 1
  field_simp

theorem rayProjector_mulVec_self (z : ι → ℂ) (hz : z ≠ 0) :
    (rayProjector z).mulVec z = z := by
  have hn : (pureStateNormSq z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z hz))
  rw [rayProjector, Matrix.smul_mulVec, density_mulVec, self_amplitude, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

theorem rayProjector_range (z : ι → ℂ) (hz : z ≠ 0) :
    (rayProjector z).mulVecLin.range = ℂ ∙ z := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [Matrix.mulVecLin_apply, rayProjector, Matrix.smul_mulVec, density_mulVec, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
  · apply (Submodule.span_singleton_le_iff_mem z _).mpr
    exact ⟨z, rayProjector_mulVec_self z hz⟩

theorem unit_density_eq_iff_phase (z w : ι → ℂ)
    (hz : pureStateNormSq z = 1) (hw : pureStateNormSq w = 1) :
    rankOneDensity z = rankOneDensity w ↔
      ∃ c : ℂ, Complex.normSq c = 1 ∧ w = c • z := by
  constructor
  · intro he
    have hv := congrArg (fun M : Matrix ι ι ℂ => M.mulVec w) he
    rw [density_mulVec, density_mulVec, self_amplitude, hw] at hv
    simp only [Complex.ofReal_one, one_smul] at hv
    refine ⟨basisBornAmplitude z w, ?_, hv.symm⟩
    have hn := congrArg pureStateNormSq hv
    rw [normSq_smul, hz, hw, mul_one] at hn
    exact hn
  · rintro ⟨c, hc, rfl⟩
    rw [density_smul, hc]
    simp

theorem phase_action_free (z : ι → ℂ) (hz : z ≠ 0) (c : ℂ)
    (hc : c • z = z) : c = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  have he := congrFun hc i
  change c * z i = z i at he
  exact (mul_right_cancel₀ hi (he.trans (one_mul (z i)).symm))

abbrev UnitVector (ι : Type*) [Fintype ι] := {z : ι → ℂ // pureStateNormSq z = 1}

theorem unitVector_ne_zero (z : UnitVector ι) : z.val ≠ 0 := by
  intro h
  have hn := z.property
  rw [h] at hn
  simp [pureStateNormSq] at hn

def unitRay (z : UnitVector ι) : Projectivization ℂ (ι → ℂ) :=
  Projectivization.mk ℂ z.val (unitVector_ne_zero z)

theorem unitRay_eq_iff_phase (z w : UnitVector ι) :
    unitRay z = unitRay w ↔ ∃ c : ℂ, Complex.normSq c = 1 ∧ w.val = c • z.val := by
  rw [unitRay, unitRay, eq_comm, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc.symm⟩
    have hn := congrArg pureStateNormSq hc
    rw [normSq_smul, z.property, w.property, mul_one] at hn
    exact hn
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc.symm⟩

/-- Mathlib identifies the nonzero-vector quotient with actual
one-dimensional complex subspaces, without assuming this bijection. -/
def raySubspaceEquiv : Projectivization ℂ (ι → ℂ) ≃
    {L : Submodule ℂ (ι → ℂ) // Module.finrank ℂ L = 1} :=
  Projectivization.equivSubmodule ℂ (ι → ℂ)

def normalize (z : ι → ℂ) : ι → ℂ :=
  ((Real.sqrt (pureStateNormSq z) : ℂ)⁻¹) • z

theorem normalize_normSq (z : ι → ℂ) (hz : z ≠ 0) :
    pureStateNormSq (normalize z) = 1 := by
  have hp := normSq_positive z hz
  simp only [normalize, normSq_smul, map_inv₀, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt hp.le]
  exact inv_mul_cancel₀ (ne_of_gt hp)

def normalizedUnit (z : ι → ℂ) (hz : z ≠ 0) : UnitVector ι :=
  ⟨normalize z, normalize_normSq z hz⟩

theorem normalize_density (z : ι → ℂ) : rankOneDensity (normalize z) = rayProjector z := by
  rw [normalize, density_smul]
  simp only [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (normSq_nonnegative z)]
  rw [Complex.ofReal_inv]
  rfl

theorem normalizedUnit_ray (z : ι → ℂ) (hz : z ≠ 0) :
    unitRay (normalizedUnit z hz) = Projectivization.mk ℂ z hz := by
  rw [unitRay, Projectivization.mk_eq_mk_iff']
  exact ⟨(Real.sqrt (pureStateNormSq z) : ℂ)⁻¹, rfl⟩

def unitPhaseSetoid : Setoid (UnitVector ι) := Setoid.ker unitRay
abbrev UnitPhaseQuotient := Quotient (unitPhaseSetoid (ι := ι))

theorem unitPhaseSetoid_iff (z w : UnitVector ι) :
    (unitPhaseSetoid (ι := ι)).r z w ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ w.val = c • z.val := by
  change unitRay z = unitRay w ↔ _
  rw [unitRay_eq_iff_phase]
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨c, ?_, he⟩
    have hs : ‖c‖ ^ 2 = 1 := by simpa only [Complex.sq_norm] using hc
    nlinarith [norm_nonneg c]
  · rintro ⟨c, hc, he⟩
    refine ⟨c, ?_, he⟩
    rw [← Complex.sq_norm, hc]
    norm_num

def quotientRay : UnitPhaseQuotient (ι := ι) → Projectivization ℂ (ι → ℂ) :=
  Quotient.lift unitRay (fun _ _ h => h)

theorem quotientRay_bijective : Function.Bijective (quotientRay (ι := ι)) := by
  constructor
  · intro z w h
    induction z using Quotient.inductionOn with | _ z =>
    induction w using Quotient.inductionOn with | _ w =>
    exact Quotient.sound h
  · intro p
    refine ⟨Quotient.mk _ (normalizedUnit p.rep p.rep_nonzero), ?_⟩
    change unitRay (normalizedUnit p.rep p.rep_nonzero) = p
    rw [normalizedUnit_ray, Projectivization.mk_rep]

/-- The sphere modulo the actual unit-modulus phase relation is the
nonzero-vector projectivization, as a set. Smoothness is a separate claim. -/
def spherePhaseEquivProjective : UnitPhaseQuotient (ι := ι) ≃
    Projectivization ℂ (ι → ℂ) := Equiv.ofBijective quotientRay quotientRay_bijective

def quotientProjector : UnitPhaseQuotient (ι := ι) → Matrix ι ι ℂ :=
  Quotient.lift (fun z : UnitVector ι => rankOneDensity z.val) (by
    intro z w h
    exact (unit_density_eq_iff_phase z.val w.val z.property w.property).mpr
      ((unitRay_eq_iff_phase z w).mp h))

theorem quotientProjector_injective : Function.Injective (quotientProjector (ι := ι)) := by
  intro z w h
  induction z using Quotient.inductionOn with | _ z =>
  induction w using Quotient.inductionOn with | _ w =>
  apply Quotient.sound
  exact (unitRay_eq_iff_phase z w).mpr
    ((unit_density_eq_iff_phase z.val w.val z.property w.property).mp h)

theorem quotientProjector_normalized (z : ι → ℂ) (hz : z ≠ 0) :
    quotientProjector (Quotient.mk _ (normalizedUnit z hz)) = rayProjector z :=
  normalize_density z

theorem normalized_range_is_ray (z : ι → ℂ) (hz : z ≠ 0) :
    (Projectivization.mk ℂ (normalize z)
      (unitVector_ne_zero (normalizedUnit z hz))).submodule =
      (Projectivization.mk ℂ z hz).submodule := by
  exact congrArg Projectivization.submodule (normalizedUnit_ray z hz)

def horizontalSpace {d : ℕ} (h : EuclideanSpace ℂ (Fin (d+1))) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (d+1))) := (ℂ ∙ h)ᗮ

theorem horizontalSpace_mem {d : ℕ} (h v : EuclideanSpace ℂ (Fin (d+1))) :
    v ∈ horizontalSpace h ↔ inner ℂ h v = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

theorem horizontalSpace_complex_dimension {d : ℕ}
    (h : EuclideanSpace ℂ (Fin (d+1))) (hh : h ≠ 0) :
    Module.finrank ℂ (horizontalSpace h) = d := by
  letI : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin (d+1))) = d+1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton hh

theorem horizontalSpace_real_dimension {d : ℕ}
    (h : EuclideanSpace ℂ (Fin (d+1))) (hh : h ≠ 0) :
    Module.finrank ℝ (horizontalSpace h) = 2*d := by
  rw [finrank_real_of_complex, horizontalSpace_complex_dimension h hh]

end
end QubitOracle.Paper.ProjectiveStateGeometry
