import QubitOracle.AdaptiveDesign.P1InverseGramMoments
import QubitOracle.AdaptiveDesign.P1ControllerFourthMoment
import QubitOracle.AdaptiveDesign.UniformProductMoments
import QubitOracle.AdaptiveDesign.POVMEstimatorMoments

/-! Explicit higher-moment consequences used in Proposition S7.2. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
local instance supplement_moments_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance supplement_moments_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem normalizedError_inverseGram_bound (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (θ : OneQubitPhysicalParameter) (n : ℕ) (path : Path) :
    ‖normalizedError loss ridge refresh θ.1 (n+1) path‖ ≤
      inverseGramNorm loss ridge refresh (n+1) path *
      ‖(Real.sqrt ((n+1:ℕ):ℝ))⁻¹ •
        (residualSum (policy loss ridge refresh) θ.1 (n+1) path-ridge • WithLp.toLp 2 θ.1)‖ := by
  let G := (pathState loss ridge refresh (n+1) path).gram
  let z := residualSum (policy loss ridge refresh) θ.1 (n+1) path-ridge • WithLp.toLp 2 θ.1
  have hpd : G.PosDef := by
    dsimp [G]
    rw [pathState_gram]
    exact ridge_posDef ridge hr _ _
  have hmul : G⁻¹*G=1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
  have he : matrixMap G⁻¹ z=rawError loss ridge refresh θ.1 (n+1) path := by
    rw [show z=G.toEuclideanLin (rawError loss ridge refresh θ.1 (n+1) path) from
      (normal_error loss ridge hr refresh θ.1 (n+1) path).symm]
    change matrixMap G⁻¹ (matrixMap G (rawError loss ridge refresh θ.1 (n+1) path)) = _
    rw [← matrixMap_mul,hmul,matrixMap_one]
  have hN : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have hs : 0<Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr hN
  have hn : ((n+1:ℕ):ℝ)*(Real.sqrt ((n+1:ℕ):ℝ))⁻¹=Real.sqrt ((n+1:ℕ):ℝ) := by
    apply (mul_inv_eq_iff_eq_mul₀ hs.ne').mpr
    simpa only [pow_two] using (Real.sq_sqrt hN.le).symm
  have hsolve : (((n+1:ℕ):ℝ) • matrixMap G⁻¹)
      ((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • z) = normalizedError loss ridge refresh θ.1 (n+1) path := by
    rw [ContinuousLinearMap.smul_apply,map_smul,smul_smul,hn,he]
    rfl
  rw [← hsolve]
  exact ContinuousLinearMap.le_opNorm _ _

theorem raw_uniformMoment (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (p : ℕ) (hp : 0 < p) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (fun n => normalizedError loss ridge refresh θ.1 (n+1)) p := by
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ
  let Z := fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ •
    (residualSum (policy loss ridge refresh) θ.1 (n+1) path-ridge • WithLp.toLp 2 θ.1)
  have hInv : UniformMoment μ (fun n => inverseGramNorm loss ridge refresh (n+1)) (2*p) := by
    cases loss
    · exact bures_inverseGram_moments ridge hr refresh θ (2*p) (by omega)
    · exact frobenius_inverseGram_moments ridge hr refresh θ hθ (2*p) (by omega)
  have hZ : UniformMoment μ Z (2*p) := by
    have hS := residualSum_moments (policy loss ridge refresh) θ (2*p)
    have hB : UniformMoment μ (fun n (_ : Path) =>
        (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (-ridge • WithLp.toLp 2 θ.1)) (2*p) := by
      apply uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const)
        ‖-ridge • WithLp.toLp 2 θ.1‖ (norm_nonneg _)
      intro n path
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
      apply mul_le_of_le_one_left (norm_nonneg _)
      apply (inv_le_one₀ (by positivity)).mpr
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
    simpa only [Z,smul_add,smul_neg,neg_smul,sub_eq_add_neg] using hS.add hB
  apply (hInv.mul hZ.norm).of_dominated _
    (fun n => (normalizedError_measurable loss ridge refresh θ.1 (n+1)).aestronglyMeasurable)
    1 (by norm_num)
  intro n path
  simp only [one_mul,norm_mul,norm_norm,Real.norm_of_nonneg (show 0 ≤ inverseGramNorm loss ridge refresh (n+1) path from norm_nonneg _)]
  exact normalizedError_inverseGram_bound loss ridge hr refresh θ n path

theorem controller_uniformMoment (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (p : ℕ) (hp : 0 < p) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (fun n => controllerError loss ridge refresh θ.1 (n+1)) p := by
  cases loss with
  | bures =>
    obtain ⟨C,hC,hbound⟩ := bures_controller_error_bound θ.1 hθ
    apply (raw_uniformMoment .bures ridge hr refresh θ hθ p hp).of_dominated _
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
    have hraw := (raw_uniformMoment .frobenius ridge hr refresh θ hθ p hp).norm
    have hconst := uniformMoment_of_bound
      (μ:=adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
      (fun _ (_ : Path) => B)
      (fun _ => aestronglyMeasurable_const) B hB (fun _ _ => by simp [Real.norm_eq_abs,abs_of_nonneg hB]) p
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


theorem raw_real_moments (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (r : ℝ) (hr0 : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun path => ‖normalizedError loss ridge refresh θ.1 (n+1) path‖^r)
        (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ∧
      (∫ path, ‖normalizedError loss ridge refresh θ.1 (n+1) path‖^r
        ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ≤ K :=
  real_moments_of_all_integer (raw_uniformMoment loss ridge hr refresh θ hθ) r hr0

theorem controller_real_moments (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (r : ℝ) (hr0 : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun path => ‖controllerError loss ridge refresh θ.1 (n+1) path‖^r)
        (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ∧
      (∫ path, ‖controllerError loss ridge refresh θ.1 (n+1) path‖^r
        ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ≤ K :=
  real_moments_of_all_integer (controller_uniformMoment loss ridge hr refresh θ hθ) r hr0

end
end QubitOracle.AdaptiveDesign.P1Weighted
