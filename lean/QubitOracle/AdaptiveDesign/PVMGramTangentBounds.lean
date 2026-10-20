-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGramLocalCoercivity

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMPilotBorn
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem quadratic_opNorm_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (x : E) : |⟪x,B x⟫_ℝ| ≤ ‖B‖*‖x‖^2 := by
  calc
    _ ≤ ‖x‖*‖B x‖ := by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) x (B x)
    _ ≤ ‖x‖*(‖B‖*‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

theorem compress_tangent_inner (truth : PureVector d) (G : Operator d) (A : tangentSpace truth) :
    ⟪A.val,compress truth G A.val⟫_ℝ = ⟪A.val,G A.val⟫_ℝ := by
  change ⟪A.val,tangentProjector truth (G (tangentProjector truth A.val))⟫_ℝ = _
  rw [tangentProjector_self,tangentProjector_apply]
  simpa only [real_inner_comm] using tangentProjectionVector_inner truth (G A.val) A

theorem local_meanGram_coercive (truth : PureVector d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : Action d) (n : ℕ),
      ‖frameParameter U.matrix-(pureParameter d truth).val‖ < δ →
      PVMPilotSchedule.epsilon n ≤ 1/2 → ∀ A : tangentSpace truth,
      (1/(4*(d+1:ℝ)))*‖A‖^2 ≤ ⟪A.val,meanGram (n,U) A.val⟫_ℝ := by
  obtain ⟨δ,hδ,hlocal⟩ := local_exploitationGram truth
  refine ⟨δ,hδ,fun U n hU hn A => ?_⟩
  have hquad := quadratic_opNorm_bound
    (compress truth (exploitationGram U)-(1/(d+1:ℝ)) • tangentProjector truth) A.val
  have hh := (hlocal U hU).le
  have hb : |⟪A.val,exploitationGram U A.val⟫_ℝ-(1/(d+1:ℝ))*‖A‖^2| ≤
      (1/(2*(d+1:ℝ)))*‖A‖^2 := by
    have he : ⟪A.val,(compress truth (exploitationGram U)-
        (1/(d+1:ℝ)) • tangentProjector truth) A.val⟫_ℝ =
        ⟪A.val,exploitationGram U A.val⟫_ℝ-(1/(d+1:ℝ))*‖A‖^2 := by
      rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
        inner_sub_right,inner_smul_right,compress_tangent_inner,tangentProjector_self,
        real_inner_self_eq_norm_sq]
      rfl
    rw [he] at hquad
    exact hquad.trans (mul_le_mul_of_nonneg_right hh (sq_nonneg _))
  have he : (1/(2*(d+1:ℝ)))*‖A‖^2 ≤ ⟪A.val,exploitationGram U A.val⟫_ℝ := by
    have hi := neg_le_of_abs_le hb
    have hid : (1/(d+1:ℝ)-1/(2*(d+1:ℝ)))*‖A‖^2 = (1/(2*(d+1:ℝ)))*‖A‖^2 := by
      field_simp
      ring
    nlinarith only [hi,hid]
  have hl := meanGram_exploitation_lower (n,U) A.val
  have hwt : 0 ≤ 1-PVMPilotSchedule.epsilon n := by linarith
  have hx := mul_le_mul_of_nonneg_left he hwt
  have hy := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-PVMPilotSchedule.epsilon n by linarith)
    (show 0 ≤ (1/(2*(d+1:ℝ)))*‖A‖^2 by positivity)
  have hid : (1/2:ℝ)*((1/(2*(d+1:ℝ)))*‖A‖^2) = (1/(4*(d+1:ℝ)))*‖A‖^2 := by
    field_simp
    ring
  nlinarith only [hl,hx,hy,hid]

theorem quadratic_difference_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E) (x y : E) (hy : ‖y‖ ≤ ‖x‖) :
    |⟪x,G x⟫_ℝ-⟪y,G y⟫_ℝ| ≤ 2*‖G‖*‖x-y‖*‖x‖ := by
  have he : ⟪x,G x⟫_ℝ-⟪y,G y⟫_ℝ = ⟪x-y,G x⟫_ℝ+⟪y,G (x-y)⟫_ℝ := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |⟪x-y,G x⟫_ℝ|+|⟪y,G (x-y)⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖x-y‖*‖G x‖+‖y‖*‖G (x-y)‖ := by
      simpa only [Real.norm_eq_abs] using add_le_add
        (norm_inner_le_norm (𝕜:=ℝ) (x-y) (G x)) (norm_inner_le_norm (𝕜:=ℝ) y (G (x-y)))
    _ ≤ ‖x-y‖*(‖G‖*‖x‖)+‖x‖*(‖G‖*‖x-y‖) := by
      gcongr
      · exact G.le_opNorm x
      · exact G.le_opNorm (x-y)
    _ = _ := by ring

/-- A deterministic transfer from the true tangent space to the fitted
tangent space. It applies pathwise to the realized all-record Gram. -/
theorem nearby_tangent_coercivity (h truth : PureVector d) (G : Operator d)
    (N C κ δ : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1/12) (hsmall' : 96*C*δ ≤ κ)
    (hclose : ‖(pureParameter d h).val-(pureParameter d truth).val‖ ≤ δ)
    (hG : ‖G‖ ≤ N*C)
    (hcoerc : ∀ A : tangentSpace truth, κ*N*‖A‖^2 ≤ ⟪A.val,G A.val⟫_ℝ)
    (A : tangentSpace h) :
    (κ/8)*N*‖A‖^2 ≤ ⟪A.val,G A.val⟫_ℝ := by
  let B := tangentProjector truth A.val
  have hB : ‖B‖ ≤ ‖A‖ := (tangentSpace truth).norm_starProjection_apply_le A.val
  have hdiff : ‖A.val-B‖ ≤ 6*δ*‖A‖ := by
    have hh := tangentProjector_difference_bound h truth A.val
    rw [tangentProjector_self] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hclose (by norm_num)) (norm_nonneg _))
  have hBbelow : ‖A‖/2 ≤ ‖B‖ := by
    have hx := norm_sub_le (A.val-B) (-B)
    rw [sub_neg_eq_add,sub_add_cancel,norm_neg] at hx
    change ‖A‖ ≤ ‖A.val-B‖+‖B‖ at hx
    nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg A)]
  have hc := hcoerc ⟨B,(tangentSpace truth).starProjection_apply_mem _⟩
  have hd := quadratic_difference_bound G A.val B hB
  have hd' : |⟪A.val,G A.val⟫_ℝ-⟪B,G B⟫_ℝ| ≤ 12*N*C*δ*‖A‖^2 := by
    apply hd.trans
    calc
      _ ≤ 2*(N*C)*(6*δ*‖A‖)*‖A‖ := by gcongr; rfl
      _ = _ := by ring
  have hl : κ*N*(‖A‖^2/4) ≤ κ*N*‖B‖^2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg A,norm_nonneg B]) (mul_nonneg hκ.le hN)
  have hm := mul_le_mul_of_nonneg_right hsmall' (mul_nonneg hN (sq_nonneg ‖A‖))
  have hh := neg_le_of_abs_le hd'
  change κ*N*‖B‖^2 ≤ _ at hc
  nlinarith only [hc,hl,hm,hh]

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
