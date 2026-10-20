-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGramGoodEvent
import QubitOracle.AdaptiveDesign.PVMFinalLinearization

/-! A finite-sample bound for the actual corrected PVM estimator on a
well-conditioned recorded Gram matrix. The leading pilot error cancels. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open TangentGLS PVMGeometry PVMPilotAdaptive CoerciveLeastSquares
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem scoreSum_bound (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖scoreSum truth batchSize n path‖ ≤ (n:ℝ)*(2*basisBound d) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, 2*basisBound d := by
      apply Finset.sum_le_sum
      intro k _
      change ‖scoreResponse truth _ _‖ ≤ _
      simpa only [floor,inv_one,one_mul] using scoreResponse_bound truth _ _
    _ = _ := by simp

theorem corrected_error_of_coercive (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (batchSize : ℕ → ℕ) (n : ℕ), 0 < n →
      ∀ path : AdaptiveInfinitePath (PVMOutcome d),
      Coercive (normalMap (tangentFeature (actualPreliminary batchSize path n)
        (actualRecords batchSize path n)) (fun _ => 1) ridge) (κ*(n:ℝ)) →
      ‖projectorError truth ridge hr batchSize n path‖ ≤ C*
        (‖scoreSum truth batchSize n path‖/(n:ℝ)+
          ‖actualPreliminaryError batchSize truth n path‖^2+1/(n:ℝ)) := by
  let R := 3*(d+1:ℝ)*(basisBound d)^2
  let S := 2*basisBound d
  let K := (1+R+2*|ridge|)/κ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (basisBound_nonnegative d)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K+9+6*K^2*(S+5),by positivity,fun batchSize n hn path hG => ?_⟩
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  let h := actualPreliminary batchSize path n
  let e := actualPreliminaryError batchSize truth n path
  let a := preliminaryTangentError h truth
  let Δ := actualDelta ridge hr batchSize path n
  let p := ‖scoreSum truth batchSize n path‖/(n:ℝ)+‖e‖^2+1/(n:ℝ)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have he : ‖e‖ ≤ 2 := preliminaryError_norm_le_two h truth
  have ha : ‖a‖ ≤ ‖e‖ := preliminaryTangentError_norm_le h truth
  have hscore := scoreSum_bound truth batchSize n path
  have hpB : p ≤ S+5 := by
    have hs : ‖scoreSum truth batchSize n path‖/(n:ℝ) ≤ S :=
      (div_le_iff₀ hn').mpr (by simpa [S,mul_comm] using hscore)
    have hi : 1/(n:ℝ) ≤ 1 := (div_le_one hn').mpr hn1
    dsimp only [p]
    nlinarith [norm_nonneg e]
  have hu : ‖Δ+a‖ ≤ K*p := by
    let G := normalMap (tangentFeature h (actualRecords batchSize path n)) (fun _ => 1) ridge
    have hg := norm_le_residual_div G (κ*(n:ℝ)) (mul_pos hκ hn') hG (Δ+a) (G (Δ+a)) rfl
    have heq := actual_normal_equation truth ridge hr batchSize n path
    have hval : (G (Δ+a)).val =
        tangentProjector h (scoreSum truth batchSize n path)+
          normalRemainder h truth (actualRecords batchSize path n) ridge := by
      rw [← recordOperator_tangent]
      exact heq
    have hb := normalRemainder_bound h truth (actualRecords batchSize path n) ridge
      (basisBound d) (basisBound_nonnegative d)
      (fun r => by rw [recordFeature_eq]; exact basisEffect_bound _ _)
    have hb' : ‖normalRemainder h truth (actualRecords batchSize path n) ridge‖ ≤
        R*(n:ℝ)*‖e‖^2+2*|ridge| := by
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,R,e,
        actualPreliminaryError,h,mul_assoc,mul_left_comm,mul_comm] using hb
    have hgn : ‖G (Δ+a)‖ ≤ ‖scoreSum truth batchSize n path‖+R*(n:ℝ)*‖e‖^2+2*|ridge| := by
      change ‖(G (Δ+a)).val‖ ≤ _
      rw [hval]
      exact (norm_add_le _ _).trans (by
        have hq := (tangentProjector h).le_opNorm (scoreSum truth batchSize n path)
        have hq' := mul_le_mul_of_nonneg_right (tangentProjector_norm_le h)
          (norm_nonneg (scoreSum truth batchSize n path))
        simp only [one_mul] at hq'
        linarith only [hq,hq',hb'])
    apply hg.trans
    apply (div_le_div_of_nonneg_right hgn (mul_pos hκ hn').le).trans
    apply (div_le_iff₀ (mul_pos hκ hn')).mpr
    dsimp only [K,p]
    field_simp
    nlinarith [mul_nonneg hR (norm_nonneg (scoreSum truth batchSize n path)),
      mul_nonneg (abs_nonneg ridge) (norm_nonneg (scoreSum truth batchSize n path)),
      mul_nonneg hR (sq_nonneg ‖e‖),mul_nonneg (abs_nonneg ridge) (sq_nonneg ‖e‖)]
  have hd : ‖Δ‖ ≤ K*p+‖e‖ := by
    have hh := norm_sub_le (Δ+a) a
    rw [add_sub_cancel_right] at hh
    linarith only [hh,hu,ha]
  have hds : ‖Δ‖^2 ≤ 2*K^2*(S+5)*p+2*p := by
    have h0 : 0 ≤ K*p := mul_nonneg hK.le hp
    have hh := pow_le_pow_left₀ (norm_nonneg Δ) hd 2
    have hpp := mul_le_mul_of_nonneg_left hpB hp
    have hep : ‖e‖^2 ≤ p := by
      dsimp only [p]
      linarith [div_nonneg (norm_nonneg (scoreSum truth batchSize n path)) hn'.le,
        div_nonneg (by norm_num : (0:ℝ)≤1) hn'.le]
    have hc := mul_le_mul_of_nonneg_left hpp (by positivity : 0 ≤ 2*K^2)
    nlinarith [sq_nonneg (K*p-‖e‖)]
  have hnormal : ‖e-a.val‖ ≤ 3*‖e‖^2 := preliminaryError_normal_bound h truth
  have hrem := updated_error_bound h truth (actualRecords batchSize path n) ridge hr
  change ‖projectorError truth ridge hr batchSize n path-(e+Δ.val)‖ ≤ 3*‖Δ‖^2 at hrem
  have hid : e+Δ.val = (Δ+a).val+(e-a.val) := by simp only [Submodule.coe_add]; abel
  have hlinear : ‖e+Δ.val‖ ≤ K*p+3*‖e‖^2 := by
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add hu hnormal)
  have ht := norm_sub_le (projectorError truth ridge hr batchSize n path-(e+Δ.val)) (-(e+Δ.val))
  simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
  have hep : ‖e‖^2 ≤ p := by
    dsimp only [p]
    linarith [div_nonneg (norm_nonneg (scoreSum truth batchSize n path)) hn'.le,
      div_nonneg (by norm_num : (0:ℝ)≤1) hn'.le]
  change ‖projectorError truth ridge hr batchSize n path‖ ≤ (K+9+6*K^2*(S+5))*p
  nlinarith only [ht,hrem,hlinear,hds,hep]

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
