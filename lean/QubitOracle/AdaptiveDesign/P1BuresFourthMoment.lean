import QubitOracle.AdaptiveDesign.P1FiniteSampleBounds
import QubitOracle.AdaptiveDesign.GoodEventMoments

/-! A proved fourth moment for the literal all-record mixed-qubit
Bures ridge estimator, for every deterministic refresh schedule. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance P1BuresFourthMoment_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1BuresFourthMoment_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem bures_raw_fourthMoment (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge refresh)) θ)
      (fun n => normalizedError .bures ridge refresh θ.1 (n+1)) 4 := by
  let p := policy .bures ridge refresh
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol p) θ
  let Z := fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • residualSum p θ.1 (n+1) path
  let v := ‖WithLp.toLp 2 θ.1‖
  let A := 6/ridge+v
  have hv : 0 ≤ v := norm_nonneg _
  have hA : 0 < A := add_pos_of_pos_of_nonneg (div_pos (by norm_num) hr) hv
  let bad := fun n => {path | ((n+1:ℕ):ℝ)/6 ≤ entrySize (gramDeviation p (n+1) path)}
  have hX : UniformMoment μ (fun n path => 6*(‖Z n path‖+ridge*v)) 4 :=
    ((residualSum_moments p θ 4).norm.add
      (uniformMoment_of_bound (fun _ (_ : Path) => ridge*v) (fun _ => aestronglyMeasurable_const)
        (ridge*v) (mul_nonneg hr.le hv) (fun _ _ => by
          rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hv)]) 4)).const_mul 6
  apply fourthMoment_of_good_event _ _ hX
    (fun _ _ => by positivity) (fun n => (normalizedError_measurable .bures ridge refresh θ.1 (n+1)).aestronglyMeasurable)
    bad (fun n => A*((n+1:ℕ):ℝ)^2) (fun _ => by positivity)
  · intro n path
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hs : Real.sqrt ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity,by nlinarith⟩
    have he := rawError_global_bound .bures ridge hr refresh θ (n+1) path
    change ‖Real.sqrt ((n+1:ℕ):ℝ) • rawError .bures ridge refresh θ.1 (n+1) path‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have he' : ‖rawError .bures ridge refresh θ.1 (n+1) path‖ ≤ A*((n+1:ℕ):ℝ) := by
      change ‖rawError .bures ridge refresh θ.1 (n+1) path‖ ≤ ((n+1:ℕ):ℝ)*6/ridge+v at he
      dsimp only [A]
      simp only [div_eq_mul_inv] at he ⊢
      nlinarith only [he,mul_le_mul_of_nonneg_left hn hv]
    calc
      _ ≤ ((n+1:ℕ):ℝ)*(A*((n+1:ℕ):ℝ)) :=
        mul_le_mul hs he' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro n path hx
    have hn : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hs : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr hn
    have hG := bures_lower_of_noise ridge hr.le refresh (n+1) path (not_le.mp hx).le
    have he := rawError_of_lower .bures ridge hr refresh θ.1 (n+1) path _ (by positivity) hG
    have hi : (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ ≤ 1 := by
      apply (inv_le_one₀ hs).mpr
      rw [Real.le_sqrt (by norm_num) hn.le]
      norm_num
    have hsq := Real.sq_sqrt hn.le
    have hid : Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ) = (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ := by
      field_simp
      exact hsq
    change ‖Real.sqrt ((n+1:ℕ):ℝ) • rawError .bures ridge refresh θ.1 (n+1) path‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.le]
    apply (mul_le_mul_of_nonneg_left he hs.le).trans
    dsimp only [Z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
    have heq : Real.sqrt ((n+1:ℕ):ℝ)*
        ((‖residualSum p θ.1 (n+1) path‖+ridge*v)/(((n+1:ℕ):ℝ)/6)) =
        6*((Real.sqrt ((n+1:ℕ):ℝ))⁻¹*‖residualSum p θ.1 (n+1) path‖+
          (Real.sqrt ((n+1:ℕ):ℝ))⁻¹*(ridge*v)) := by
      calc
        _ = 6*((Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ))*‖residualSum p θ.1 (n+1) path‖+
          (Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ))*(ridge*v)) := by ring
        _ = _ := by rw [hid]
    change Real.sqrt ((n+1:ℕ):ℝ)*
      ((‖residualSum p θ.1 (n+1) path‖+ridge*v)/(((n+1:ℕ):ℝ)/6)) ≤ _
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg hr.le hv)]
  · obtain ⟨B,c,hB,hc,ht⟩ := gramDeviation_tail p θ
    have htail (n : ℕ) : μ.real (bad n) ≤ B*Real.exp (-(c/36)*((n+1:ℕ):ℝ)) := by
      have hh := ht n (((n+1:ℕ):ℝ)/6) (by positivity)
      convert hh using 1
      congr 2
      field_simp
      ring
    have hnat : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hexp := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((8:ℕ):ℝ) (c/36) (by positivity)).comp hnat).const_mul B
    simp only [Real.rpow_natCast,Real.rpow_ofNat,mul_zero] at hexp
    dsimp only [Function.comp_def] at hexp
    have htend : Tendsto (fun n => ((n+1:ℕ):ℝ)^8*μ.real (bad n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => by positivity) _ hexp
      intro n
      have hh := mul_le_mul_of_nonneg_left (htail n) (show (0:ℝ)≤((n+1:ℕ):ℝ)^8 by positivity)
      calc
        _ ≤ ((n+1:ℕ):ℝ)^8*(B*Real.exp (-(c/36)*((n+1:ℕ):ℝ))) := hh
        _ = B*(((n+1:ℕ):ℝ)^8*Real.exp (-(c/36)*((n+1:ℕ):ℝ))) := by ring
        _ ≤ _ := le_rfl
    obtain ⟨K,hK⟩ := htend.bddAbove_range
    refine ⟨A^4*max K 0,by positivity,fun n => ?_⟩
    have hh := mul_le_mul_of_nonneg_left ((hK (Set.mem_range_self n)).trans (le_max_left K 0))
      (show 0 ≤ A^4 by positivity)
    calc
      _ = A^4*(((n+1:ℕ):ℝ)^8*μ.real (bad n)) := by ring
      _ ≤ _ := hh

end
end QubitOracle.AdaptiveDesign.P1Weighted
