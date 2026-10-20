import QubitOracle.AdaptiveDesign.P1FrobeniusFourthMoment
import QubitOracle.AdaptiveDesign.RealMomentBounds

/-! Uniform higher moments of the literal normalized inverse ridge Gram.
The all-history allocation envelope and Gram fluctuations may be dependent. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
local instance inverseGram_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance inverseGram_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

def inverseGramNorm (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) : ℝ :=
  ‖(n:ℝ) • matrixMap (pathState loss ridge refresh n path).gram⁻¹‖

theorem inverseGramNorm_of_lower (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (n : ℕ) (path : Path) (c : ℝ) (hc : 0 < c)
    (hG : Lower (pathState loss ridge refresh n path).gram c) :
    inverseGramNorm loss ridge refresh n path ≤ (n:ℝ)/c := by
  have hpd : (pathState loss ridge refresh n path).gram.PosDef := by
    rw [pathState_gram]
    exact ridge_posDef ridge hr _ n
  have hmul := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hpd.det_pos.ne')
  unfold inverseGramNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hs : (pathState loss ridge refresh n path).gram.toEuclideanLin
      (matrixMap (pathState loss ridge refresh n path).gram⁻¹ x) = x := by
    change matrixMap _ (matrixMap _ x) = x
    rw [← matrixMap_mul,hmul,matrixMap_one]
  have he := CoerciveLeastSquares.norm_le_residual_div _ c hc
    (lower_to_coercive _ _ hG) _ _ hs
  change ‖(n:ℝ) • matrixMap (pathState loss ridge refresh n path).gram⁻¹ x‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ))]
  calc
    _ ≤ (n:ℝ)*(‖x‖/c) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem inverseGramNorm_measurable (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) :
    Measurable (inverseGramNorm loss ridge refresh n) :=
  historyStatistic_measurable loss ridge refresh n (fun state => ‖(n:ℝ) • matrixMap state.gram⁻¹‖)

theorem inverseGram_moments_of_envelope (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (θ : OneQubitPhysicalParameter)
    (R : ℕ → Path → ℝ) (hRp : ∀ n path, 0 < R n path)
    (hRm : ∀ p : ℕ, UniformMoment
      (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) R p)
    (hpred : ∀ n path, Lower (predictedGram (policy loss ridge refresh) (n+1) path)
      (((n+1:ℕ):ℝ)/R n path)) (p : ℕ) (hp : 0 < p) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (fun n => inverseGramNorm loss ridge refresh (n+1)) p := by
  let policy' := policy loss ridge refresh
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol policy') θ
  let W := fun n path => 2*R n path*((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ *
    entrySize (gramDeviation policy' (n+1) path))
  have hW : UniformMoment μ W (2*p) := by
    simpa only [W,mul_assoc] using
      ((hRm (2*(2*p))).mul (p:=2*p) (gramDeviation_moments policy' θ (2*(2*p)))).const_mul 2
  let bad := fun n => {path | Real.sqrt ((n+1:ℕ):ℝ) ≤ W n path}
  apply moment_of_good_event p hp _ (fun n path => 2*R n path) ((hRm p).const_mul 2)
    (fun n path => mul_nonneg (by norm_num) (hRp n path).le)
    (fun n => (inverseGramNorm_measurable loss ridge refresh (n+1)).aestronglyMeasurable)
    bad (fun n => ((n+1:ℕ):ℝ)/ridge) (fun _ => by positivity)
  · intro n path
    rw [Real.norm_of_nonneg (show 0 ≤ inverseGramNorm loss ridge refresh (n+1) path from norm_nonneg _)]
    exact inverseGramNorm_of_lower loss ridge hr refresh (n+1) path ridge hr
      (ridge_lower loss ridge refresh (n+1) path)
  · intro n path hx
    have hRnp := hRp n path
    let N : ℝ := ((n+1:ℕ):ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have hsq := Real.sq_sqrt hN.le
    have hnoise : entrySize (gramDeviation policy' (n+1) path) < N/(2*R n path) := by
      have hh : 2*R n path*((Real.sqrt N)⁻¹*entrySize (gramDeviation policy' (n+1) path)) <
          Real.sqrt N := not_le.mp hx
      have hh' := mul_lt_mul_of_pos_right hh hs
      have hid : 2*R n path*((Real.sqrt N)⁻¹*entrySize (gramDeviation policy' (n+1) path))*
          Real.sqrt N = 2*R n path*entrySize (gramDeviation policy' (n+1) path) := by field_simp
      rw [hid] at hh'
      apply (lt_div_iff₀ (show 0 < 2*R n path by positivity)).mpr
      nlinarith only [hh',hsq]
    have hG := gram_lower_from_predicted loss ridge hr.le refresh (n+1) path _ (hpred n path)
    have hG' : Lower (pathState loss ridge refresh (n+1) path).gram (N/(2*R n path)) := by
      apply lower_mono _ _ _ _ hG
      change N/(2*R n path) ≤ N/R n path-entrySize (gramDeviation policy' (n+1) path)
      have hid : N/R n path = 2*(N/(2*R n path)) := by ring
      rw [hid]
      linarith
    rw [Real.norm_of_nonneg (show 0 ≤ inverseGramNorm loss ridge refresh (n+1) path from norm_nonneg _)]
    apply (inverseGramNorm_of_lower loss ridge hr refresh (n+1) path _ (by positivity) hG').trans_eq
    change N/(N/(2*R n path)) = 2*R n path
    field_simp
  · obtain ⟨K,hK,hKt⟩ := hW.weighted_tail (fun n => ((n+1:ℕ):ℝ)^p)
      (fun _ => by positivity) bad (by
        intro n path hx
        have hh : Real.sqrt ((n+1:ℕ):ℝ) ≤ W n path := hx
        have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hh.trans (le_abs_self _)) (2*p)
        rw [pow_mul,Real.sq_sqrt (by positivity)] at hpow
        simpa only [Real.norm_eq_abs] using hpow)
    refine ⟨ridge⁻¹^p*K,by positivity,fun n => ?_⟩
    calc
      _ = ridge⁻¹^p*(((n+1:ℕ):ℝ)^p*μ.real (bad n)) := by rw [div_eq_mul_inv,mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hKt n) (by positivity)

theorem frobenius_inverseGram_moments (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (p : ℕ) (hp : 0 < p) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
      (fun n => inverseGramNorm .frobenius ridge refresh (n+1)) p := by
  obtain ⟨C,hC,hR⟩ := allocationEnvelope_moments ridge hr refresh θ hθ
  apply inverseGram_moments_of_envelope .frobenius ridge hr refresh θ
    (fun n => allocationEnvelope C ridge refresh (n+1))
    (fun n path => allocationEnvelope_positive C ridge refresh hC _ _) _
    (fun n path => predictedGram_lower_envelope C ridge refresh hC (n+1) path) p hp
  intro r
  obtain ⟨K,hK,hK'⟩ := hR r
  exact ⟨K,hK,fun n => hK' (n+1)⟩

theorem bures_inverseGram_moments (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (p : ℕ) (hp : 0 < p) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge refresh)) θ)
      (fun n => inverseGramNorm .bures ridge refresh (n+1)) p := by
  apply inverseGram_moments_of_envelope .bures ridge hr refresh θ (fun _ _ => 3)
    (fun _ _ => by norm_num) _ _ p hp
  · intro r
    exact uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const) 3
      (by norm_num) (fun _ _ => by norm_num) r
  · intro n path x
    rw [predictedGram,quadratic_sum]
    have he (k : ℕ) : gram (actualAction (policy .bures ridge refresh) k path) =
        (1/3:ℝ) • (1:Mat) := by
      rw [action_eq_reference,gram_reference]
      rfl
    simp only [he,quadratic_smul,quadratic_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring_nf
    rfl

/-- The exact real-order assertion in the supplement; the operator norm
is the Euclidean operator norm of the actual inverse ridge Gram. -/
theorem inverseGram_real_moments (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1)
    (r : ℝ) (hr0 : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun path => (inverseGramNorm loss ridge refresh (n+1) path)^r)
        (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ∧
      (∫ path, (inverseGramNorm loss ridge refresh (n+1) path)^r
        ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ) ≤ K := by
  have hm (p : ℕ) (hp : 0 < p) :
      UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
        (fun n => inverseGramNorm loss ridge refresh (n+1)) p := by
    cases loss
    · exact bures_inverseGram_moments ridge hr refresh θ p hp
    · exact frobenius_inverseGram_moments ridge hr refresh θ hθ p hp
  simpa only [inverseGramNorm,norm_norm] using real_moments_of_all_integer hm r hr0

end
end QubitOracle.AdaptiveDesign.P1Weighted
