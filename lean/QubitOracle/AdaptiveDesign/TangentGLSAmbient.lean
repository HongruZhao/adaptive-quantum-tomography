import QubitOracle.AdaptiveDesign.TangentGLSRecordBounds
import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates

/-! Fixed ambient score and noise-derivative operators. These responses are
centered at the true state before the data-dependent tangent projection is
applied, so the martingale rate theorem is used only on predictable inputs. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ComplexOrder Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

section Hilbert
variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype R]

def rankOneCLM (f : E) : E →L[ℝ] E := (innerSL ℝ f).smulRight f

@[simp] theorem rankOneCLM_apply (f x : E) : rankOneCLM f x = ⟪f,x⟫_ℝ • f := rfl

theorem rankOneCLM_norm (f : E) : ‖rankOneCLM f‖ ≤ ‖f‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro x
  rw [rankOneCLM_apply, norm_smul]
  have hb := mul_le_mul_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) f x) (norm_nonneg f)
  nlinarith

def gramCLM (f : R → E) (w : R → ℝ) : E →L[ℝ] E := ∑ r, w r • rankOneCLM (f r)

@[simp] theorem gramCLM_apply (f : R → E) (w : R → ℝ) (x : E) :
    gramCLM f w x = ∑ r, (w r*⟪f r,x⟫_ℝ) • f r := by
  simp [gramCLM, mul_smul]

theorem gramCLM_norm_bound (f : R → E) (w : R → ℝ) :
    ‖gramCLM f w‖ ≤ ∑ r, |w r| *‖f r‖^2 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (rankOneCLM_norm _) (abs_nonneg _)

end Hilbert

section Centering
variable {O E : Type*} [Fintype O] [NormedAddCommGroup E] [NormedSpace ℝ E]

def centeredLookup (p : O → ℝ) (v : O → E) (y : O) : E := v y - ∑ z, p z • v z

theorem centeredLookup_sum (p : O → ℝ) (hp : ∑ y, p y = 1) (v : O → E) :
    ∑ y, p y • centeredLookup p v y = 0 := by
  simp only [centeredLookup, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp, one_smul, sub_self]

theorem centeredLookup_norm_bound (p : O → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (v : O → E) (B : ℝ) (hb : ∀ y, ‖v y‖ ≤ B) (y : O) :
    ‖centeredLookup p v y‖ ≤ 2*B := by
  have hm : ‖∑ z, p z • v z‖ ≤ B := by
    calc
      _ ≤ ∑ z, ‖p z • v z‖ := norm_sum_le _ _
      _ ≤ ∑ z, p z * B := Finset.sum_le_sum (fun z _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp0 z)]
        exact mul_le_mul_of_nonneg_left (hb z) (hp0 z))
      _ = B := by rw [← Finset.sum_mul, hp1, one_mul]
  exact (norm_sub_le _ _).trans (by linarith [hb y])

theorem centeredLookup_eq_residual_sum [DecidableEq O] (p : O → ℝ) (v : O → E) (o : O) :
    centeredLookup p v o = ∑ y, ((if o=y then 1 else 0)-p y) • v y := by
  classical
  simp [centeredLookup, sub_smul, Finset.sum_sub_distrib, eq_comm]

theorem centeredLookup_integral [CompleteSpace E] [MeasurableSpace O] [MeasurableSingletonClass O]
    (p : O → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (v : O → E) :
    ∫ y, centeredLookup p v y ∂finiteMassMeasure p hp0 hp1 = 0 := by
  rw [integral_finiteMassMeasure]
  exact centeredLookup_sum p hp1 v

end Centering

variable {d n : ℕ} {O : Type} [Fintype O]

theorem score_tangent_val (h : PureVector d) (data : Fin n → Record d O) (w r : Fin n × O → ℝ) :
    (score (tangentFeature h data) w r).val = tangentProjector h (score (recordFeature data) w r) := by
  change _ = ((tangentSpace h).orthogonalProjectionOnto (score (recordFeature data) w r)).val
  congr 1
  simp [score, tangentFeature]

theorem gram_tangent_val (h : PureVector d) (data : Fin n → Record d O)
    (w : Fin n × O → ℝ) (x : tangentSpace h) :
    (gram (tangentFeature h data) w x).val =
      tangentProjector h (gramCLM (recordFeature data) w x.val) := by
  change _ = ((tangentSpace h).orthogonalProjectionOnto (gramCLM (recordFeature data) w x.val)).val
  congr 1
  simp [gram_apply, gramCLM_apply, tangentFeature,
    Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr x.property]

def ambientScoreResponse (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) : O → HermitianSpace (d+1) :=
  centeredLookup (GeneralPOVM.bornProbability P truth U)
    (fun y => (denominator floor (GeneralPOVM.bornProbability P truth U y))⁻¹ •
      GeneralPOVM.responseVector P U y)

def ambientDerivativeResponse (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) :
    O → (HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1)) :=
  centeredLookup (GeneralPOVM.bornProbability P truth U)
    (fun y => -(denominator floor (GeneralPOVM.bornProbability P truth U y)^2)⁻¹ •
      rankOneCLM (GeneralPOVM.responseVector P U y))

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem ambientScoreResponse_mean (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) :
    ∫ y, ambientScoreResponse P truth floor U y ∂GeneralPOVM.bornKernel P truth U = 0 :=
  centeredLookup_integral _ (GeneralPOVM.bornProbability_nonnegative P truth U)
    (GeneralPOVM.bornProbability_sum P truth U) _

theorem ambientDerivativeResponse_mean (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) :
    ∫ y, ambientDerivativeResponse P truth floor U y ∂GeneralPOVM.bornKernel P truth U = 0 :=
  centeredLookup_integral _ (GeneralPOVM.bornProbability_nonnegative P truth U)
    (GeneralPOVM.bornProbability_sum P truth U) _

theorem ambientScoreResponse_bound (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (hf : 0 < floor) (U : GlobalPFSICBorn.Action d) (y : O) :
    ‖ambientScoreResponse P truth floor U y‖ ≤ 2*(floor⁻¹*GeneralPOVM.responseBound P) := by
  apply centeredLookup_norm_bound _ (GeneralPOVM.bornProbability_nonnegative P truth U)
    (GeneralPOVM.bornProbability_sum P truth U)
  intro z
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (denominator_pos hf _).le)]
  exact mul_le_mul (inv_anti₀ hf (le_max_right _ _))
    (GeneralPOVM.responseVector_norm_le P U z) (norm_nonneg _)
    (inv_nonneg.mpr hf.le)

theorem ambientDerivativeResponse_bound (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (hf : 0 < floor) (U : GlobalPFSICBorn.Action d) (y : O) :
    ‖ambientDerivativeResponse P truth floor U y‖ ≤ 2*((floor^2)⁻¹*(GeneralPOVM.responseBound P)^2) := by
  apply centeredLookup_norm_bound _ (GeneralPOVM.bornProbability_nonnegative P truth U)
    (GeneralPOVM.bornProbability_sum P truth U)
  intro z
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
  have hsq : floor^2 ≤ denominator floor (GeneralPOVM.bornProbability P truth U z)^2 := by
    have hb : floor ≤ denominator floor (GeneralPOVM.bornProbability P truth U z) := le_max_right _ _
    nlinarith
  have hv : ‖rankOneCLM (GeneralPOVM.responseVector P U z)‖ ≤ (GeneralPOVM.responseBound P)^2 := by
    apply (rankOneCLM_norm _).trans
    have hb := GeneralPOVM.responseVector_norm_le P U z
    nlinarith [norm_nonneg (GeneralPOVM.responseVector P U z)]
  exact mul_le_mul (inv_anti₀ (sq_pos_of_pos hf) hsq) hv (norm_nonneg _) (by positivity)

end
end QubitOracle.AdaptiveDesign.TangentGLS
