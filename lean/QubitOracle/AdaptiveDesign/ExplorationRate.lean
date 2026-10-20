import QubitOracle.Paper.BoundedMartingaleAzumaStrongLaw
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative bounded-martingale law used by the PVM exploration route.
Every probability estimate is derived from conditional Hoeffding and
Borel--Cantelli; no external statistical axiom is introduced. -/

noncomputable section
namespace QubitOracle.AdaptiveDesign.ExplorationRate
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open scoped BigOperators ENNReal NNReal Topology
set_option maxHeartbeats 2000000

lemma summable_exp_neg_sqrt (K : ℝ) (hK : 0 < K) :
    Summable (fun n : ℕ => Real.exp (-K * ((n : ℝ) + 1) ^ (1/2 : ℝ))) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hp := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp ht
  have ho := (isLittleO_exp_neg_mul_rpow_atTop hK (-4)).isBigO.comp_tendsto hp
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have h := (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ) < -1)).comp_injective
      (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  apply summable_of_isBigO_nat hs
  change (fun n : ℕ => Real.exp (-K * ((n:ℝ)+1)^(1/2:ℝ))) =O[atTop]
    (fun n : ℕ => ((n:ℝ)+1)^(-2:ℝ))
  convert ho using 1
  · rfl
  · funext n
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
    norm_num

/-- A bounded martingale sum divided by `(N+1)^(3/4)` tends to zero a.s. -/
theorem bounded_sum_threeQuarter_ae
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration ℕ mOmega) (X : ℕ → Omega → ℝ)
    (h_adapted : StronglyAdapted F X) (hzero : X 0 = 0)
    (hcenter : ∀ n, mu[X (n+1) | F n] =ᵐ[mu] 0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n omega, ‖X n omega‖ ≤ C) :
    ∀ᵐ omega ∂mu, Tendsto
      (fun N : ℕ => ((N:ℝ)+1) ^ (-3/4 : ℝ) *
        ∑ i ∈ Finset.range (N+1), X i omega) atTop (𝓝 0) := by
  let B : Real := C + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let c : NNReal := ((‖B - (-B)‖₊ / 2) ^ 2)
  have hc : 0 < (c : Real) := by
    have hdiff : B - (-B) ≠ 0 := by linarith
    change 0 < (‖B - (-B)‖ / 2 : Real) ^ 2
    positivity
  let cX : Nat -> NNReal := fun n => if n = 0 then 0 else c
  have hcX_sum (N : Nat) :
      ∑ i ∈ Finset.range (N + 1), cX i = (N : NNReal) * c := by
    induction N with
    | zero => simp [cX]
    | succ N ih =>
        rw [show Nat.succ N + 1 = (N + 1) + 1 by omega,
          Finset.sum_range_succ, ih]
        simp [cX, Nat.cast_succ]
        ring
  have hsub_zero : HasSubgaussianMGF (X 0) (cX 0) mu := by
    simpa [cX, hzero] using
      (HasSubgaussianMGF.fun_zero (mu := mu))
  have hsub_cond (n : Nat) :
      HasCondSubgaussianMGF (F n) (F.le n) (X (n + 1)) (cX (n + 1)) mu := by
    have hmeas : StronglyMeasurable (X (n + 1)) :=
      (h_adapted (n + 1)).mono (F.le (n + 1))
    have hinterval (omega : Omega) : X (n + 1) omega ∈ Set.Icc (-B) B := by
      have habsC : |X (n + 1) omega| <= C := by
        simpa [Real.norm_eq_abs] using hbound (n + 1) omega
      have habsB : |X (n + 1) omega| <= B := habsC.trans (by dsimp [B]; linarith)
      exact ⟨neg_le_of_abs_le habsB, (le_abs_self _).trans habsB⟩
    simpa [cX, c] using
      hasCondSubgaussianMGF_of_mem_Icc_of_condExp_zero
        (F.le n) hmeas hinterval (hcenter n)
  have hsum (N : Nat) :
      HasSubgaussianMGF
        (fun omega => ∑ i ∈ Finset.range (N + 1), X i omega)
        ((N : NNReal) * c) mu := by
    have h := HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      h_adapted hsub_zero (N + 1)
      (fun i _ => hsub_cond i)
    rw [hcX_sum N] at h
    exact h
  let weight : ℕ → ℝ := fun N => ((N:ℝ)+1) ^ (-3/4 : ℝ)
  let average : ℕ → Omega → ℝ := fun N omega =>
    weight N * ∑ i ∈ Finset.range (N+1), X i omega
  let cAverage : ℕ → NNReal := fun N =>
    ⟨(weight N)^2, sq_nonneg _⟩ * ((N:NNReal)*c)
  have hav (N : ℕ) : HasSubgaussianMGF (average N) (cAverage N) mu := by
    simpa [average, cAverage] using (hsum N).const_mul (weight N)
  have hparam (N : ℕ) :
      (cAverage N : ℝ) ≤ (c:ℝ) * ((N:ℝ)+1)^(-1/2:ℝ) := by
    have hb : (0:ℝ) < (N:ℝ)+1 := by positivity
    have hp : (weight N)^2 = ((N:ℝ)+1)^(-3/2:ℝ) := by
      dsimp [weight]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      norm_num
    change (weight N)^2 * ((N:ℝ)*(c:ℝ)) ≤ _
    rw [hp]
    calc
      _ ≤ ((N:ℝ)+1)^(-3/2:ℝ) * (((N:ℝ)+1)*(c:ℝ)) := by gcongr; linarith
      _ = (c:ℝ) * ((N:ℝ)+1)^(-1/2:ℝ) := by
        have hh : ((N:ℝ)+1)^(-3/2:ℝ) * ((N:ℝ)+1) =
            ((N:ℝ)+1)^(-1/2:ℝ) := by
          calc
            _ = ((N:ℝ)+1)^(-3/2:ℝ) * ((N:ℝ)+1)^(1:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hb]; norm_num
        calc
          _ = (c:ℝ) * (((N:ℝ)+1)^(-3/2:ℝ) * ((N:ℝ)+1)) := by ring
          _ = _ := by rw [hh]
  have htail (delta : ℝ) (hd : 0 < delta) (N : ℕ) (hN : 0 < N) :
      mu.real {omega | delta ≤ ‖average N omega‖} ≤
        2 * Real.exp (-(delta^2 / (2*(c:ℝ))) * ((N:ℝ)+1)^(1/2:ℝ)) := by
    have hp : (0:ℝ) < cAverage N := by
      change 0 < (weight N)^2 * ((N:ℝ)*(c:ℝ))
      have hn : (0:ℝ) < N := by exact_mod_cast hN
      dsimp [weight]
      positivity
    have hden : -delta^2 / (2*(cAverage N:ℝ)) ≤
        -(delta^2 / (2*(c:ℝ))) * ((N:ℝ)+1)^(1/2:ℝ) := by
      have hb : (0:ℝ) < (N:ℝ)+1 := by positivity
      have hr : ((N:ℝ)+1)^(-1/2:ℝ) * ((N:ℝ)+1)^(1/2:ℝ) = 1 := by
        rw [← Real.rpow_add hb]; norm_num
      have hm := mul_le_mul_of_nonneg_right (hparam N)
        (Real.rpow_nonneg hb.le (1/2:ℝ))
      have hprod : (cAverage N:ℝ) * ((N:ℝ)+1)^(1/2:ℝ) ≤ (c:ℝ) := by
        simpa only [mul_assoc, hr, mul_one] using hm
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(cAverage N:ℝ))).2
      have hh := neg_le_neg (mul_le_mul_of_nonneg_left hprod
        (div_nonneg (sq_nonneg delta) hc.le))
      calc
        -delta^2 = -(delta^2/(c:ℝ) * (c:ℝ)) := by field_simp
        _ ≤ -(delta^2/(c:ℝ) * ((cAverage N:ℝ) * ((N:ℝ)+1)^(1/2:ℝ))) := hh
        _ = _ := by ring
    have hplus := (hav N).measure_ge_le hd.le
    have hminus := (hav N).neg.measure_ge_le hd.le
    have hsub : {omega | delta ≤ ‖average N omega‖} ⊆
        {omega | delta ≤ average N omega} ∪ {omega | delta ≤ -average N omega} := by
      intro omega hh
      simpa only [Set.mem_union, Set.mem_setOf_eq, Real.norm_eq_abs, le_abs] using hh
    calc
      _ ≤ mu.real ({omega | delta ≤ average N omega} ∪
          {omega | delta ≤ -average N omega}) := measureReal_mono hsub (by finiteness)
      _ ≤ mu.real {omega | delta ≤ average N omega} +
          mu.real {omega | delta ≤ -average N omega} := measureReal_union_le _ _
      _ ≤ Real.exp (-delta^2 / (2*(cAverage N:ℝ))) +
          Real.exp (-delta^2 / (2*(cAverage N:ℝ))) := by
        exact add_le_add hplus (by simpa only [Pi.neg_apply] using hminus)
      _ ≤ _ := by nlinarith [Real.exp_le_exp.mpr hden]
  have hBC (delta : ℝ) (hd : 0 < delta) :
      ∀ᵐ omega ∂mu, ∀ᶠ N in atTop, omega ∉ {omega | delta ≤ ‖average N omega‖} := by
    have hs := (summable_exp_neg_sqrt (delta^2/(2*(c:ℝ))) (by positivity)).mul_left 2
    have hm : Summable (fun N : ℕ => mu.real {omega | delta ≤ ‖average N omega‖}) := by
      apply hs.of_nonneg_of_le (fun _ => measureReal_nonneg)
      intro N
      by_cases hn : N = 0
      · subst N
        simp [average, hzero, not_le.mpr hd]
        positivity
      · exact htail delta hd N (Nat.pos_of_ne_zero hn)
    apply ae_eventually_notMem
    have hh := hm.tsum_ofReal_lt_top
    convert hh.ne using 1
    congr 1
    funext N
    exact (ofReal_measureReal (μ := mu)
      (s := {omega | delta ≤ ‖average N omega‖})).symm
  obtain ⟨v, -, hvpos, hvlim⟩ : ∃ v : ℕ → ℝ, StrictAnti v ∧
      (∀ n, 0 < v n) ∧ Tendsto v atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0:ℝ)
  have hall := ae_all_iff.2 (fun i => hBC (v i) (hvpos i))
  filter_upwards [hall] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨i, hi⟩ := ((tendsto_order.1 hvlim).2 epsilon hepsilon).exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 (homega i)
  refine ⟨N, fun n hn => ?_⟩
  have hnorm : ‖average n omega‖ < v i := by
    simpa only [Set.mem_setOf_eq, not_le] using hN n hn
  simpa [average, weight, Real.dist_eq] using hnorm.trans hi

end QubitOracle.AdaptiveDesign.ExplorationRate
