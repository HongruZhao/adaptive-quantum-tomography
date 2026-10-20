import QubitOracle.AdaptiveDesign.P1InverseAllocationMoments
import QubitOracle.AdaptiveDesign.P1GramMoments
import QubitOracle.AdaptiveDesign.UniformProductMoments
import QubitOracle.AdaptiveDesign.GoodEventMoments

/-! Fourth moments of the literal Frobenius adaptive ridge estimator.
Random inverse-allocation bounds and Gram noise need not be independent. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
local instance P1FrobeniusFourthMoment_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1FrobeniusFourthMoment_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem predictedGram_lower_envelope (C ridge : ℝ) (refresh : ℕ → Bool) (hC : 3 ≤ C)
    (n : ℕ) (path : Path) :
    Lower (predictedGram (policy .frobenius ridge refresh) n path)
      ((n:ℝ)/(allocationEnvelope C ridge refresh n path)) := by
  intro x
  rw [predictedGram,quadratic_sum]
  calc
    _ = ∑ t ∈ Finset.range n, (allocationEnvelope C ridge refresh n path)⁻¹*blochNormSq x := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,div_eq_mul_inv]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun t ht => gram_lower _ _
      (fun i => allocationEnvelope_controls C ridge refresh hC n t (Finset.mem_range.mp ht) path i) x)

theorem frobenius_raw_fourthMoment (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
      (fun n => normalizedError .frobenius ridge refresh θ.1 (n+1)) 4 := by
  let p := policy .frobenius ridge refresh
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol p) θ
  obtain ⟨C,hC,hR⟩ := allocationEnvelope_moments ridge hr refresh θ hθ
  let R := fun n => allocationEnvelope C ridge refresh (n+1)
  have hRm (r : ℕ) : UniformMoment μ R r := by
    obtain ⟨K,hK,hK'⟩ := hR r
    exact ⟨K,hK,fun n => hK' (n+1)⟩
  have hRp (n : ℕ) (path : Path) : 0 < R n path := allocationEnvelope_positive C ridge refresh hC _ _
  let Z := fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • residualSum p θ.1 (n+1) path
  let D := fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * entrySize (gramDeviation p (n+1) path)
  let W := fun n path => 2*R n path*D n path
  have hW : UniformMoment μ W 16 := by
    simpa only [W,D,mul_assoc] using ((hRm 32).mul (gramDeviation_moments p θ 32)).const_mul 2
  let v := ‖WithLp.toLp 2 θ.1‖
  let A := 6/ridge+v
  have hv : 0 ≤ v := norm_nonneg _
  have hA : 0 < A := add_pos_of_pos_of_nonneg (div_pos (by norm_num) hr) hv
  let bad := fun n => {path | Real.sqrt ((n+1:ℕ):ℝ) ≤ W n path}
  have hX : UniformMoment μ (fun n path => 2*R n path*(‖Z n path‖+ridge*v)) 4 := by
    have hh := (hRm 8).mul (p:=4) ((residualSum_moments p θ 8).norm.add
      (uniformMoment_of_bound (fun _ (_ : Path) => ridge*v) (fun _ => aestronglyMeasurable_const)
        (ridge*v) (mul_nonneg hr.le hv) (fun _ _ => by
          rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hv)]) 8))
    simpa only [mul_assoc] using hh.const_mul 2
  apply fourthMoment_of_good_event _ _ hX
    (fun n path => mul_nonneg (mul_nonneg (by norm_num) (hRp n path).le) (by positivity))
    (fun _ => (normalizedError_measurable .frobenius ridge refresh θ.1 _).aestronglyMeasurable)
    bad (fun n => A*((n+1:ℕ):ℝ)^2) (fun _ => by positivity)
  · intro n path
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hs : Real.sqrt ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity,by nlinarith⟩
    have he := rawError_global_bound .frobenius ridge hr refresh θ (n+1) path
    change ‖Real.sqrt ((n+1:ℕ):ℝ) • rawError .frobenius ridge refresh θ.1 (n+1) path‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have he' : ‖rawError .frobenius ridge refresh θ.1 (n+1) path‖ ≤ A*((n+1:ℕ):ℝ) := by
      change ‖rawError .frobenius ridge refresh θ.1 (n+1) path‖ ≤ ((n+1:ℕ):ℝ)*6/ridge+v at he
      dsimp only [A]
      simp only [div_eq_mul_inv] at he ⊢
      nlinarith only [he,mul_le_mul_of_nonneg_left hn hv]
    calc
      _ ≤ ((n+1:ℕ):ℝ)*(A*((n+1:ℕ):ℝ)) := mul_le_mul hs he' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro n path hx
    have hRnp := hRp n path
    let N : ℝ := ((n+1:ℕ):ℝ)
    have hN : 0 < N := by dsimp [N]; positivity
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
    have hsq := Real.sq_sqrt hN.le
    have hnoise : entrySize (gramDeviation p (n+1) path) < N/(2*R n path) := by
      have hh : 2*R n path*((Real.sqrt N)⁻¹*entrySize (gramDeviation p (n+1) path)) < Real.sqrt N := not_le.mp hx
      have hh' := mul_lt_mul_of_pos_right hh hs
      have hid : 2*R n path*((Real.sqrt N)⁻¹*entrySize (gramDeviation p (n+1) path))*Real.sqrt N =
          2*R n path*entrySize (gramDeviation p (n+1) path) := by field_simp <;> ring
      rw [hid] at hh'
      apply (lt_div_iff₀ (show 0 < 2*R n path by positivity)).mpr
      nlinarith only [hh',hsq]
    have hG := gram_lower_from_predicted .frobenius ridge hr.le refresh (n+1) path _
      (predictedGram_lower_envelope C ridge refresh hC (n+1) path)
    have hG' : Lower (pathState .frobenius ridge refresh (n+1) path).gram (N/(2*R n path)) := by
      apply lower_mono _ _ _ _ hG
      change N/(2*R n path) ≤ N/R n path-entrySize (gramDeviation p (n+1) path)
      have hid : N/R n path = 2*(N/(2*R n path)) := by ring
      rw [hid]
      linarith only [hnoise]
    have he := rawError_of_lower .frobenius ridge hr refresh θ.1 (n+1) path _ (by positivity) hG'
    have hi : (Real.sqrt N)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ hs).mpr
      rw [Real.le_sqrt (by norm_num) hN.le]
      dsimp [N]
      norm_num
    have hid : Real.sqrt N/N = (Real.sqrt N)⁻¹ := by field_simp; exact hsq
    change ‖Real.sqrt N • rawError .frobenius ridge refresh θ.1 (n+1) path‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.le]
    apply (mul_le_mul_of_nonneg_left he hs.le).trans
    change Real.sqrt N*((‖residualSum p θ.1 (n+1) path‖+ridge*v)/(N/(2*R n path))) ≤ _
    have heq : Real.sqrt N*((‖residualSum p θ.1 (n+1) path‖+ridge*v)/(N/(2*R n path))) =
        2*R n path*((Real.sqrt N)⁻¹*‖residualSum p θ.1 (n+1) path‖+(Real.sqrt N)⁻¹*(ridge*v)) := by
      calc
        _ = 2*R n path*((Real.sqrt N/N)*‖residualSum p θ.1 (n+1) path‖+(Real.sqrt N/N)*(ridge*v)) := by field_simp <;> ring
        _ = _ := by rw [hid]
    rw [heq]
    dsimp only [Z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (mul_le_of_le_one_left (by positivity) hi)) (by positivity)
  · obtain ⟨K,hK,hKt⟩ := hW.weighted_tail (fun n => ((n+1:ℕ):ℝ)^8) (fun _ => by positivity) bad (by
      intro n path hx
      have hh : Real.sqrt ((n+1:ℕ):ℝ) ≤ W n path := hx
      have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hh.trans (le_abs_self _)) 16
      have he : Real.sqrt ((n+1:ℕ):ℝ)^16 = ((n+1:ℕ):ℝ)^8 := by
        rw [show (16:ℕ)=2*8 from rfl, pow_mul,Real.sq_sqrt (by positivity)]
      simpa only [he,Real.norm_eq_abs] using hp)
    refine ⟨A^4*K,by positivity,fun n => ?_⟩
    calc
      _ = A^4*(((n+1:ℕ):ℝ)^8*μ.real (bad n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hKt n) (by positivity)

end
end QubitOracle.AdaptiveDesign.P1Weighted
