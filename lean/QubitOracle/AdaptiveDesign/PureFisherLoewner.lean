import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import Mathlib.Analysis.Matrix.PosDef

/-! The full pure-state information bound, including zero Born probabilities.
The proof applies Cauchy--Schwarz in the seminorm induced by each effect. -/
namespace QubitOracle.AdaptiveDesign.PureFisherLoewner
open QubitOracle Matrix
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Cauchy--Schwarz remains valid for singular positive effects. -/
theorem effect_cauchy_schwarz {I : Type*} [Fintype I]
    (E : Matrix I I ℂ) (hE : E.PosSemidef) (x v : I → ℂ) :
    Complex.normSq (star x ⬝ᵥ (E *ᵥ v)) ≤
      (star x ⬝ᵥ (E *ᵥ x)).re * (star v ⬝ᵥ (E *ᵥ v)).re := by
  let M : Matrix I (Fin 2) ℂ := fun i j => ![x i,v i] j
  have hB := hE.conjTranspose_mul_mul_same M
  have hc := psd_entry_normSq_le_diag_mul_diag _ hB (0:Fin 2) 1
  simp only [Matrix.mul_assoc] at hc
  simpa only [M,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct,
    Pi.star_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using hc

theorem scalar_effect_bound {I : Type*} [Fintype I]
    (E : Matrix I I ℂ) (hE : E.PosSemidef) (x v : I → ℂ) :
    safeRatio (star x ⬝ᵥ (E *ᵥ x)).re ((star x ⬝ᵥ (E *ᵥ v)).re^2) ≤
      (star v ⬝ᵥ (E *ᵥ v)).re := by
  have hp := hE.re_dotProduct_nonneg x
  have hv := hE.re_dotProduct_nonneg v
  have hc := effect_cauchy_schwarz E hE x v
  by_cases hz : (star x ⬝ᵥ (E *ᵥ x)).re=0
  · simpa [safeRatio,hz] using hv
  · rw [safeRatio,if_neg hz]
    apply (div_le_iff₀ (lt_of_le_of_ne hp (Ne.symm hz))).mpr
    have hn : (star x ⬝ᵥ (E *ᵥ v)).re^2 ≤ Complex.normSq (star x ⬝ᵥ (E *ᵥ v)) := by
      simp only [Complex.normSq_apply]
      nlinarith [sq_nonneg (star x ⬝ᵥ (E *ᵥ v)).im]
    exact (hn.trans hc).trans_eq (mul_comm _ _)

theorem directional_information_bound {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (P : FinitePOVM I O) (x v : I → ℂ) :
    (∑ y, safeRatio (star x ⬝ᵥ (P.effect y *ᵥ x)).re
      ((star x ⬝ᵥ (P.effect y *ᵥ v)).re^2)) ≤ ∑ i, Complex.normSq (v i) := by
  calc
    _ ≤ ∑ y, (star v ⬝ᵥ (P.effect y *ᵥ v)).re :=
      Finset.sum_le_sum (fun y _ => scalar_effect_bound _ (P.positive y) x v)
    _ = (star v ⬝ᵥ ((∑ y, P.effect y) *ᵥ v)).re := by
      simp [Matrix.sum_mulVec,dotProduct_sum,Complex.re_sum]
    _ = _ := by
      rw [P.complete,Matrix.one_mulVec]
      simp only [dotProduct,Complex.re_sum,Pi.star_apply]
      apply Finset.sum_congr rfl
      intro i _
      change ((starRingEnd ℂ) (v i)*v i).re = _
      rw [mul_comm,Complex.mul_conj]
      rfl


def complexDirection {d : ℕ} (u : TangentIndex d → ℝ) : Fin (d+1) → ℂ :=
  Fin.cases 0 (fun r => (u (Sum.inl r):ℂ)+(u (Sum.inr r):ℂ)*Complex.I)

theorem direction_normSq {d : ℕ} (u : TangentIndex d → ℝ) :
    (∑ i, Complex.normSq (complexDirection u i))=u ⬝ᵥ u := by
  simp [complexDirection,Fin.sum_univ_succ,dotProduct,Fintype.sum_sum_type,
    Complex.normSq_apply,Finset.sum_add_distrib,pow_two]

theorem direction_gradient {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (y : O) (u : TangentIndex d → ℝ) :
    (star (Pi.single 0 (1:ℂ)) ⬝ᵥ (P.effect y *ᵥ complexDirection u)).re =
      referenceGradient P y ⬝ᵥ u := by
  simp [complexDirection,referenceGradient,Pi.single_apply,dotProduct,Matrix.mulVec,
    Fin.sum_univ_succ,Fintype.sum_sum_type,Complex.mul_re,Complex.mul_im,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,sub_eq_add_neg]

theorem weightedGram_quadratic {I O : Type} [Fintype I] [Fintype O]
    (p : O → ℝ) (g : O → I → ℝ) (u : I → ℝ) :
    u ⬝ᵥ (GeneralPOVM.weightedGram p g *ᵥ u) = ∑ y, (g y ⬝ᵥ u)^2/p y := by
  simp only [GeneralPOVM.weightedGram,Matrix.sum_mulVec,dotProduct_sum,
    Matrix.smul_mulVec,dotProduct_smul,Matrix.vecMulVec_mulVec]
  apply Finset.sum_congr rfl
  intro y _
  simp [dotProduct_smul,smul_eq_mul,dotProduct_comm,div_eq_mul_inv,pow_two,mul_comm,mul_left_comm]

theorem reference_quadratic {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (u : TangentIndex d → ℝ) :
    u ⬝ᵥ (referenceFisher P *ᵥ u) =
      ∑ y, safeRatio (referenceProbability P y) ((referenceGradient P y ⬝ᵥ u)^2) := by
  have he : referenceFisher P=GeneralPOVM.weightedGram
      (referenceProbability P) (referenceGradient P) := by
    ext i j
    exact (GeneralPOVM.weightedGram_apply _ _ i j).symm
  rw [he,weightedGram_quadratic]
  simp only [GeneralPOVM.safeRatio_eq_div]

theorem reference_information_le_identity {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (u : TangentIndex d → ℝ) :
    u ⬝ᵥ (referenceFisher P *ᵥ u) ≤ u ⬝ᵥ u := by
  have h := directional_information_bound P (Pi.single 0 (1:ℂ)) (complexDirection u)
  rw [direction_normSq] at h
  simp only [direction_gradient] at h
  rw [reference_quadratic]
  convert h using 1
  congr 1
  funext y
  congr 1
  simp [referenceProbability,Matrix.mulVec,dotProduct,Pi.single_apply]

theorem reference_fisher_positive {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) : (referenceFisher P).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [referenceFisher,mul_comm]
  · intro u
    simp only [star_trivial,reference_quadratic,GeneralPOVM.safeRatio_eq_div]
    exact Finset.sum_nonneg (fun y _ => div_nonneg (sq_nonneg _) (referenceProbability_nonneg P y))

theorem reference_fisher_loewner {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) :
    (1-referenceFisher P).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_one.sub (reference_fisher_positive P).isHermitian
  · intro u
    simpa only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,
      sub_nonneg] using reference_information_le_identity P u


/-- The actual rotated apparatus is itself a complete finite POVM. -/
def rotated {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) : FinitePOVM (Fin (d+1)) O where
  effect := GeneralPOVM.effect P U
  positive := GeneralPOVM.effect_positive P U
  complete := GeneralPOVM.effect_complete P U hU

theorem actual_fisher_loewner {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) :
    (1-GeneralPOVM.fisher P U).PosSemidef :=
  reference_fisher_loewner (rotated P U hU)

/-- Pullback preserves the information inequality under any coordinate Jacobian. -/
theorem information_gap_congruence {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O)
    (J : Matrix (TangentIndex d) (TangentIndex d) ℝ) :
    (J.transpose*J-J.transpose*referenceFisher P*J).PosSemidef := by
  have h := (reference_fisher_loewner P).conjTranspose_mul_mul_same J
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one] using h

end
end QubitOracle.AdaptiveDesign.PureFisherLoewner
