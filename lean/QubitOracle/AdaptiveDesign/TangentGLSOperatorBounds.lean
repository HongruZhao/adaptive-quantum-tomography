import QubitOracle.AdaptiveDesign.TangentGLSInformation

/-! Quantitative stability of the protected information operator. All
bounds hold for arbitrary finite records and the actual fitted probabilities. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Operators
variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype R]

theorem gramCLM_sub (f : R → E) (w v : R → ℝ) :
    gramCLM f w - gramCLM f v = gramCLM f (fun r => w r-v r) := by
  simp [gramCLM, sub_smul, Finset.sum_sub_distrib]

theorem gramCLM_bound_constant (f : R → E) (w : R → ℝ) (C B : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hf : ∀ r, ‖f r‖ ≤ C) (hw : ∀ r, |w r| ≤ B) :
    ‖gramCLM f w‖ ≤ (Fintype.card R : ℝ)*B*C^2 := by
  apply (gramCLM_norm_bound f w).trans
  calc
    _ ≤ ∑ r : R, B*C^2 := Finset.sum_le_sum (fun r _ => by
      apply mul_le_mul (hw r) _ (sq_nonneg _) hB
      nlinarith [hf r,norm_nonneg (f r)])
    _ = _ := by simp [mul_assoc]

theorem projected_operator_difference
    (Q P K L : E →L[ℝ] E) (hQ : ‖Q‖ ≤ 1) (hP : ‖P‖ ≤ 1) :
    ‖Q.comp (K.comp Q) - P.comp (L.comp P)‖ ≤
      ‖K-L‖ + 2*‖Q-P‖*‖L‖ := by
  have he : Q.comp (K.comp Q) - P.comp (L.comp P) =
      Q.comp ((K-L).comp Q) + (Q-P).comp (L.comp Q) + P.comp (L.comp (Q-P)) := by
    ext x
    simp [map_sub, map_add]
  rw [he]
  have h1 : ‖Q.comp ((K-L).comp Q)‖ ≤ ‖K-L‖ := by
    calc
      _ ≤ ‖Q‖ * (‖K-L‖*‖Q‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖K-L‖*1) := mul_le_mul hQ
        (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (by positivity) (by norm_num)
      _ = _ := by ring
  have h2 : ‖(Q-P).comp (L.comp Q)‖ ≤ ‖Q-P‖*‖L‖ := by
    calc
      _ ≤ ‖Q-P‖*(‖L‖*‖Q‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖Q-P‖*(‖L‖*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have h3 : ‖P.comp (L.comp (Q-P))‖ ≤ ‖Q-P‖*‖L‖ := by
    calc
      _ ≤ ‖P‖*(‖L‖*‖Q-P‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1*(‖L‖*‖Q-P‖) := mul_le_mul_of_nonneg_right hP (by positivity)
      _ = _ := by ring
  exact (norm_add_le _ _).trans (by linarith [norm_add_le (Q.comp ((K-L).comp Q)) ((Q-P).comp (L.comp Q))])
end Operators

variable {d n : ℕ} {O : Type} [Fintype O]

def recordInformation (h : PureVector d) (data : Fin n → Record d O) (floor : ℝ) :
    HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  (tangentProjector h).comp ((gramCLM (recordFeature data)
    (fun r => (denominator floor (fittedProbability h data r))⁻¹)).comp (tangentProjector h))

theorem record_gram_norm (h : PureVector d) (data : Fin n → Record d O) (floor C : ℝ)
    (hf : 0 < floor) (hC : 0 ≤ C) (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖gramCLM (recordFeature data) (fun r => (denominator floor (fittedProbability h data r))⁻¹)‖ ≤
      (n : ℝ)*(Fintype.card O : ℝ)*floor⁻¹*C^2 := by
  have h := gramCLM_bound_constant (recordFeature data)
    (fun r => (denominator floor (fittedProbability h data r))⁻¹) C floor⁻¹ hC (by positivity) hb
    (fun r => by
      rw [abs_of_nonneg (by exact inv_nonneg.mpr (denominator_pos hf _).le)]
      exact inv_anti₀ hf (le_max_right _ _))
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using h

theorem record_gram_difference (h truth : PureVector d) (data : Fin n → Record d O)
    (floor C : ℝ) (hf : 0 < floor) (hC : 0 ≤ C) (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖gramCLM (recordFeature data) (fun r => (denominator floor (fittedProbability h data r))⁻¹) -
      gramCLM (recordFeature data) (fun r => (denominator floor (fittedProbability truth data r))⁻¹)‖ ≤
      (n : ℝ)*(Fintype.card O : ℝ)*(C^3/floor^2)*
        ‖(P2Adaptive.pureParameter d h).val-(P2Adaptive.pureParameter d truth).val‖ := by
  rw [gramCLM_sub]
  have h := gramCLM_bound_constant (recordFeature data) _ C
    (C*‖(P2Adaptive.pureParameter d h).val-(P2Adaptive.pureParameter d truth).val‖/floor^2)
    hC (by positivity) hb (fun r =>
      (protected_inverse_lipschitz floor _ _ hf).trans
        (div_le_div_of_nonneg_right (record_increment_bound h truth data r C (hb r)) (sq_nonneg floor)))
  apply h.trans_eq
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  ring

theorem recordInformation_difference (h truth : PureVector d) (data : Fin n → Record d O)
    (floor C : ℝ) (hf : 0 < floor) (hC : 0 ≤ C) (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖recordInformation h data floor - recordInformation truth data floor‖ ≤
      (n : ℝ)*(Fintype.card O : ℝ)*(C^3/floor^2+12*C^2/floor)*
        ‖(P2Adaptive.pureParameter d h).val-(P2Adaptive.pureParameter d truth).val‖ := by
  apply (projected_operator_difference _ _ _ _ (tangentProjector_norm_le h)
    (tangentProjector_norm_le truth)).trans
  have hproj := tangentProjector_lipschitz h truth
  have hg := record_gram_norm truth data floor C hf hC hb
  have hd := record_gram_difference h truth data floor C hf hC hb
  calc
    _ ≤ (n : ℝ)*(Fintype.card O : ℝ)*(C^3/floor^2)*
        ‖(P2Adaptive.pureParameter d h).val-(P2Adaptive.pureParameter d truth).val‖ +
      2*(6*‖(P2Adaptive.pureParameter d h).val-(P2Adaptive.pureParameter d truth).val‖)*
        ((n : ℝ)*(Fintype.card O : ℝ)*floor⁻¹*C^2) := by
      apply add_le_add hd
      exact mul_le_mul (mul_le_mul_of_nonneg_left hproj (by norm_num)) hg (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end QubitOracle.AdaptiveDesign.TangentGLS
