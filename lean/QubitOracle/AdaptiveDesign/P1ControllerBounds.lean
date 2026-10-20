import QubitOracle.AdaptiveDesign.P1FiniteSampleBounds

namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem radial_projection_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x θ : E) (R : ℝ) (hR : 0 ≤ R) (hθ : ‖θ‖ ≤ R) (hx : R ≤ ‖x‖) :
    ‖(R/‖x‖) • x-θ‖ ≤ ‖x-θ‖ := by
  by_cases hz : ‖x‖=0
  · have hzero : x=0 := norm_eq_zero.mp hz
    simp [hzero]
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hz)
  let a := R/‖x‖
  have ha : 0 ≤ a := div_nonneg hR hxpos.le
  have ha1 : a ≤ 1 := (div_le_one hxpos).mpr hx
  have han : a*‖x‖=R := by dsimp [a]; field_simp
  have hi : ⟪x,θ⟫_ℝ ≤ a*‖x‖^2 := by
    calc
      _ ≤ ‖x‖*‖θ‖ := real_inner_le_norm x θ
      _ ≤ ‖x‖*R := mul_le_mul_of_nonneg_left hθ hxpos.le
      _ = _ := by rw [← han]; ring
  have hh : 0 ≤ (1+a)*‖x‖^2-2*⟪x,θ⟫_ℝ := by
    nlinarith only [hi,mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg ‖x‖)]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖a • x-θ‖^2 ≤ ‖x-θ‖^2
  rw [norm_sub_sq_real,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,
    real_inner_smul_left,mul_pow]
  nlinarith only [mul_nonneg (sub_nonneg.mpr ha1) hh]

theorem bloch_norm_sq (x : Fin 3 → ℝ) : ‖WithLp.toLp 2 x‖^2 = blochNormSq x := by
  simp [EuclideanSpace.real_norm_sq_eq,blochNormSq]

theorem clip_error_bound (n : ℕ) (x θ : Fin 3 → ℝ)
    (hθ : blochNormSq θ ≤ 1-ExplorationRidge.epsilon n^2) :
    ‖WithLp.toLp 2 (clip n x-θ)‖ ≤ ‖WithLp.toLp 2 (x-θ)‖ := by
  unfold clip
  split_ifs with hx
  · exact le_refl _
  have hR : 0 ≤ radius n := Real.sqrt_nonneg _
  have ht : ‖WithLp.toLp 2 θ‖ ≤ radius n := by
    apply (sq_le_sq₀ (norm_nonneg _) hR).mp
    simpa only [bloch_norm_sq,radius_sq] using hθ
  have hxr : radius n ≤ ‖WithLp.toLp 2 x‖ := by
    apply (sq_le_sq₀ hR (norm_nonneg _)).mp
    simpa only [bloch_norm_sq,radius_sq] using (not_le.mp hx).le
  have he : Real.sqrt (blochNormSq x) = ‖WithLp.toLp 2 x‖ := by
    rw [← bloch_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]
  rw [he]
  exact radial_projection_error (WithLp.toLp 2 x) (WithLp.toLp 2 θ) (radius n) hR ht hxr

theorem controller_norm_le_one (loss : Loss) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖WithLp.toLp 2 (controller loss n x)‖ ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [bloch_norm_sq,one_pow]
  exact (controller_interior loss n x).le

theorem bures_controller_error_bound (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n x,
      ‖WithLp.toLp 2 (controller .bures n x-θ)‖ ≤ C*‖WithLp.toLp 2 (x-θ)‖ := by
  have ht : ‖WithLp.toLp 2 θ‖ < 1 := by
    have hh := bloch_norm_sq θ
    nlinarith [norm_nonneg (WithLp.toLp 2 θ)]
  let C := (1-‖WithLp.toLp 2 θ‖)⁻¹
  have hC : 0 < C := inv_pos.mpr (sub_pos.mpr ht)
  have hC1 : 1 ≤ C := (one_le_inv₀ (sub_pos.mpr ht)).mpr (by linarith [norm_nonneg (WithLp.toLp 2 θ)])
  refine ⟨C,hC,fun n x => ?_⟩
  change ‖WithLp.toLp 2 (P1.interiorize x-θ)‖ ≤ _
  unfold P1.interiorize
  split_ifs with hx
  · exact le_mul_of_one_le_left (norm_nonneg _) hC1
  · have hx1 : 1 ≤ ‖WithLp.toLp 2 x‖ := by
      have hh := bloch_norm_sq x
      nlinarith [not_lt.mp hx,norm_nonneg (WithLp.toLp 2 x)]
    have htri := norm_sub_le (WithLp.toLp 2 (x-θ)) (-WithLp.toLp 2 θ)
    have hid : WithLp.toLp 2 (x-θ)-(-WithLp.toLp 2 θ) = WithLp.toLp 2 x := by ext i; simp
    rw [hid,norm_neg] at htri
    have hd : 1-‖WithLp.toLp 2 θ‖ ≤ ‖WithLp.toLp 2 (x-θ)‖ := by linarith only [hx1,htri]
    have hc := mul_le_mul_of_nonneg_left hd hC.le
    have hidC : C*(1-‖WithLp.toLp 2 θ‖)=1 := inv_mul_cancel₀ (sub_pos.mpr ht).ne'
    rw [hidC] at hc
    rw [zero_sub]
    change ‖-WithLp.toLp 2 θ‖ ≤ _
    rw [norm_neg]
    exact ht.le.trans hc

end
end QubitOracle.AdaptiveDesign.P1Weighted
