import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments

/-! Products and tail weights for uniform moments. No independence is
needed: the elementary inequality 2ab ≤ a²+b² suffices. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ}
set_option backward.isDefEq.respectTransparency.types false

theorem UniformMoment.norm_sq {X : ℕ → Ω → E} (hX : UniformMoment μ X (2*p)) :
    UniformMoment μ (fun n ω => ‖X n ω‖^2) p := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨K,hK,fun n => ⟨?_,?_⟩⟩
  · have ht := (hX n).1.norm_rpow_div 2
    norm_num only [Real.rpow_two,ENNReal.ofReal_ofNat] at ht
    have hdiv : ((2*p:ℕ):ENNReal)/2 = (p:ENNReal) := by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
      simp only [Nat.cast_mul,Nat.cast_ofNat,mul_comm]
    rw [hdiv] at ht
    norm_num at ht
    exact ht
  · simpa only [norm_pow,norm_norm,← pow_mul] using (hX n).2

theorem UniformMoment.mul {X Y : ℕ → Ω → ℝ}
    (hX : UniformMoment μ X (2*p)) (hY : UniformMoment μ Y (2*p)) :
    UniformMoment μ (fun n ω => X n ω*Y n ω) p := by
  apply (hX.norm_sq.add hY.norm_sq).of_dominated _
    (fun n => ((Classical.choose_spec hX).2 n).1.1.mul
      ((Classical.choose_spec hY).2 n).1.1) (1/2) (by norm_num)
  intro n ω
  change ‖X n ω*Y n ω‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ ‖X n ω‖^2+‖Y n ω‖^2)]
  nlinarith only [sq_nonneg (‖X n ω‖-‖Y n ω‖)]

theorem UniformMoment.weighted_tail {X : ℕ → Ω → E} (hX : UniformMoment μ X p)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (bad : ℕ → Set Ω)
    (hbad : ∀ n ω, ω ∈ bad n → w n ≤ ‖X n ω‖^p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, w n*μ.real (bad n) ≤ K := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨K,hK,fun n => ?_⟩
  calc
    _ ≤ w n*μ.real {ω | w n ≤ ‖X n ω‖^p} :=
      mul_le_mul_of_nonneg_left (measureReal_mono (hbad n)) (hw n)
    _ ≤ ∫ ω, ‖X n ω‖^p ∂μ :=
      mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (fun _ => by positivity))
        (hX n).1.integrable_norm_pow' _
    _ ≤ K := (hX n).2

end
end QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
