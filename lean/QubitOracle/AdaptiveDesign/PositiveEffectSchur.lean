import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.TangentGLSRetraction

/-! A positive effect's Schur remainder. The proof uses an explicit
congruence, so it also applies when the effect is singular. -/
namespace QubitOracle.AdaptiveDesign.PositiveEffectSchur
open QubitOracle GlobalPFSIC Matrix
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ} {O : Type} [Fintype O]

def remainder (E : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  E - (E 0 0).re⁻¹ • projector (fun i => E i 0)

theorem remainder_positive (E : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hE : E.PosSemidef) (hp : 0 < (E 0 0).re) : (remainder E).PosSemidef := by
  let p : ℂ := ((E 0 0).re:ℝ)
  have hp0 : p ≠ 0 := by dsimp [p]; exact_mod_cast hp.ne'
  have h00 : E 0 0=p := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hE.diag_nonneg (i:=0))).2.symm
  let T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
    1-p⁻¹ • Matrix.vecMulVec (fun i => E i 0) (Pi.single 0 1)
  have hleft : T*E=remainder E := by
    ext i j
    have hh : E 0 j=star (E j 0) := (hE.isHermitian.apply 0 j).symm
    simp [T,Matrix.sub_mul,Matrix.smul_mul,Matrix.vecMulVec_mul,
      Matrix.vecMul, dotProduct, Pi.single_apply, remainder,projector_apply,
      Matrix.smul_apply,Matrix.vecMulVec_apply,Matrix.row,smul_eq_mul,hh,p,mul_assoc]
  have hz : remainder E *ᵥ (Pi.single 0 1) = 0 := by
    ext i
    calc
      (remainder E *ᵥ (Pi.single 0 1)) i = remainder E i 0 := by
        simp [Matrix.mulVec,dotProduct,Pi.single_apply]
      _ = E i 0 - p⁻¹ * (E i 0*p) := by
        change E i 0 - (((E 0 0).re⁻¹:ℝ):ℂ) * (E i 0 * star (E 0 0)) = _
        rw [h00]
        simp [p]
      _ = 0 := by field_simp; ring
  have hc : T*E*T.conjTranspose=remainder E := by
    rw [hleft]
    simp only [T,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul,Matrix.conjTranspose_vecMulVec,Matrix.mul_sub,
      Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec]
    have he : star (Pi.single 0 (1:ℂ) : Fin (d+1)→ℂ)=Pi.single 0 1 := by
      ext i
      simp [Pi.single_apply]
    rw [he,hz]
    simp
  rw [← hc]
  exact hE.mul_mul_conjTranspose_same T

theorem remainder_diagonal (E : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (i : Fin (d+1)) :
    ((remainder E) i i).re=(E i i).re-Complex.normSq (E i 0)/(E 0 0).re := by
  change (E i i - (((E 0 0).re⁻¹:ℝ):ℂ) * (E i 0 * (starRingEnd ℂ) (E i 0))).re = _
  rw [Complex.mul_conj,Complex.sub_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [div_eq_mul_inv,mul_comm]

theorem trace_saturation_remainder_zero (P : FinitePOVM (Fin (d+1)) O)
    (hp : GeneralPOVM.Regular P)
    (ht : (referenceFisher P).trace=(d:ℝ)) (y : O) : remainder (P.effect y)=0 := by
  have hs : ∑ o, (tangentDiagonalMass P o-
      safeRatio (referenceProbability P o) (referenceOffdiagEnergy P o))=0 := by
    rw [Finset.sum_sub_distrib,sum_tangentDiagonalMass,← referenceFisher_trace,ht,sub_self]
  have hn (o : O) : 0 ≤ tangentDiagonalMass P o-
      safeRatio (referenceProbability P o) (referenceOffdiagEnergy P o) :=
    sub_nonneg.mpr (referenceOutcomeRatio_le_diagonalMass P o)
  have hy := (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => hn o)).mp hs y (Finset.mem_univ y)
  have hpos := remainder_positive (P.effect y) (P.positive y) (hp y)
  apply hpos.trace_eq_zero_iff.mp
  apply Complex.ext
  · change (∑ i, (remainder (P.effect y)) i i).re=0
    rw [Complex.re_sum,Fin.sum_univ_succ]
    simp only [remainder_diagonal]
    have hd : Complex.normSq (P.effect y 0 0)=(referenceProbability P y)^2 := by
      have hi := (Complex.nonneg_iff.mp ((P.positive y).diag_nonneg (i:=0))).2
      simp [Complex.normSq_apply,hi.symm,referenceProbability,pow_two]
    have hstar (i : Fin d) : Complex.normSq (P.effect y i.succ 0)=
      Complex.normSq (P.effect y 0 i.succ) := by
      have hh : P.effect y 0 i.succ=(starRingEnd ℂ) (P.effect y i.succ 0) :=
        ((P.positive y).isHermitian.apply 0 i.succ).symm
      rw [hh,Complex.normSq_conj]
    simp only [hstar,Finset.sum_sub_distrib,← Finset.sum_div]
    change (referenceProbability P y-Complex.normSq (P.effect y 0 0)/referenceProbability P y)+
      (tangentDiagonalMass P y-referenceOffdiagEnergy P y/referenceProbability P y)=0
    rw [hd,pow_two,mul_div_cancel_right₀ _ (hp y).ne',sub_self,zero_add]
    simpa only [safeRatio,if_neg (hp y).ne'] using hy
  · exact (Complex.nonneg_iff.mp hpos.trace_nonneg).2.symm

/-- Equality of the regular pure-state trace budget forces rank-one effects.
The vector factor is explicit; it is not introduced as an assumption. -/
theorem trace_saturation_rankOne (P : FinitePOVM (Fin (d+1)) O)
    (hp : GeneralPOVM.Regular P)
    (ht : (referenceFisher P).trace=(d:ℝ)) : PhasePair.RankOne P := by
  intro y
  let v : Fin (d+1) → ℂ := fun i => P.effect y i 0
  let a : ℝ := Real.sqrt ((referenceProbability P y)⁻¹)
  refine ⟨a • v, ?_⟩
  have hs : a^2=(referenceProbability P y)⁻¹ :=
    Real.sq_sqrt (inv_nonneg.mpr (hp y).le)
  change P.effect y=QubitOracle.Paper.rankOneDensity (a • v)
  rw [TangentGLS.projector_real_smul,hs]
  exact sub_eq_zero.mp (trace_saturation_remainder_zero P hp ht y)

end
end QubitOracle.AdaptiveDesign.PositiveEffectSchur
