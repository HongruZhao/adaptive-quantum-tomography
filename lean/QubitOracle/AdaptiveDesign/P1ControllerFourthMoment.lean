import QubitOracle.AdaptiveDesign.P1BuresFourthMoment
import QubitOracle.AdaptiveDesign.P1FrobeniusFourthMoment

/-! The physical mixed-qubit outputs inherit the proved fourth moments
of the actual raw ridge fits, including the finite initial horizons. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local instance P1ControllerFourthMoment_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1ControllerFourthMoment_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem controller_error_bound (loss : Loss) (θ : OneQubitPhysicalParameter)
    (n : ℕ) (x : Fin 3 → ℝ) : ‖WithLp.toLp 2 (controller loss n x-θ.1)‖ ≤ 2 := by
  have ht : ‖WithLp.toLp 2 θ.1‖ ≤ 1 := by
    apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [bloch_norm_sq,one_pow]
    exact θ.property
  have he : WithLp.toLp 2 (controller loss n x-θ.1) =
      WithLp.toLp 2 (controller loss n x)-WithLp.toLp 2 θ.1 := by ext i; rfl
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [controller_norm_le_one loss n x,ht])

theorem controller_fourthMoment (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (fun n => controllerError loss ridge refresh θ.1 (n+1)) 4 := by
  cases loss with
  | bures =>
    obtain ⟨C,hC,hbound⟩ := bures_controller_error_bound θ.1 hθ
    apply (bures_raw_fourthMoment ridge hr refresh θ).of_dominated _
      (fun _ => (controllerError_measurable .bures ridge refresh θ.1 _).aestronglyMeasurable) C hC.le
    intro n path
    simp only [controllerError,normalizedError,norm_smul]
    have hh := mul_le_mul_of_nonneg_left (hbound (n+1) (estimate .bures ridge refresh (n+1) path))
      (norm_nonneg (Real.sqrt ((n+1:ℕ):ℝ)))
    nlinarith only [hh]
  | frobenius =>
    obtain ⟨T,hT⟩ := eventually_atTop.mp (truth_eventually_in_clip_ball θ.1 hθ)
    let B := 2*Real.sqrt ((T+1:ℕ):ℝ)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hraw := (frobenius_raw_fourthMoment ridge hr refresh θ hθ).norm
    have hconst := uniformMoment_of_bound
      (μ:=adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
      (fun _ (_ : Path) => B)
      (fun _ => aestronglyMeasurable_const) B hB (fun _ _ => by simp [Real.norm_eq_abs,abs_of_nonneg hB]) 4
    apply (hraw.add hconst).of_dominated _
      (fun _ => (controllerError_measurable .frobenius ridge refresh θ.1 _).aestronglyMeasurable) 1 (by norm_num)
    intro n path
    rw [one_mul,Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hB)]
    by_cases hn : T ≤ n
    · apply le_trans ?_ (le_add_of_nonneg_right hB)
      simp only [controllerError,normalizedError,norm_smul]
      exact mul_le_mul_of_nonneg_left (clip_error_bound (n+1) _ θ.1 (hT n hn)) (norm_nonneg _)
    · apply le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _))
      · simp only [controllerError,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
        have hs : Real.sqrt ((n+1:ℕ):ℝ) ≤ Real.sqrt ((T+1:ℕ):ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast (show n+1 ≤ T+1 by omega))
        calc
          _ ≤ Real.sqrt ((T+1:ℕ):ℝ)*2 := mul_le_mul hs (controller_error_bound .frobenius θ _ _) (norm_nonneg _) (by positivity)
          _ = B := by dsimp [B]; ring

end
end QubitOracle.AdaptiveDesign.P1Weighted
