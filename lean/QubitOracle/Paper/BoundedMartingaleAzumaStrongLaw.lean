import QubitOracle.Paper.BoundedConditionalSubGaussian
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A source-free bounded martingale-difference strong law

Mathlib's conditional Hoeffding lemma and Azuma inequality give exponentially
summable tails.  The first Borel--Cantelli lemma then gives the normalized
martingale-difference strong law without an external Hall--Heyde contract.
-/

noncomputable section

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

/-- Uniformly bounded, conditionally centered, strongly adapted real
increments have almost-surely vanishing empirical average.  The convention
`X 0 = 0` aligns increment `k` with filtration time `k + 1`. -/
theorem boundedMartingaleDifference_average_ae_tendsto_zero
    {Omega : Type*} {mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (X : Nat -> Omega -> Real)
    (h_adapted : StronglyAdapted F X)
    (hzero : X 0 = 0)
    (hcenter : forall n, mu[X (n + 1) | F n] =ᵐ[mu] 0)
    (C : Real) (hC : 0 <= C)
    (hbound : forall n omega, ‖X n omega‖ <= C) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun N : Nat => (N : Real)⁻¹ *
          ∑ i ∈ Finset.range (N + 1), X i omega)
        atTop (nhds 0) := by
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
  let average : Nat -> Omega -> Real := fun N omega =>
    (N : Real)⁻¹ * ∑ i ∈ Finset.range (N + 1), X i omega
  let cAverage : Nat -> NNReal := fun N =>
    ⟨((N : Real)⁻¹) ^ 2, sq_nonneg _⟩ * ((N : NNReal) * c)
  have haverage_subGaussian (N : Nat) :
      HasSubgaussianMGF (average N) (cAverage N) mu := by
    simpa [average, cAverage] using (hsum N).const_mul ((N : Real)⁻¹)
  have hcAverage (N : Nat) (hN : 0 < N) :
      (cAverage N : Real) = (c : Real) / (N : Real) := by
    have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    change ((N : Real)⁻¹) ^ 2 * ((N : Real) * (c : Real)) =
      (c : Real) / (N : Real)
    field_simp [hN0]
  have htail (delta : Real) (hdelta : 0 <= delta) (N : Nat) (hN : 0 < N) :
      mu.real {omega | delta <= ‖average N omega‖} <=
        2 * Real.exp (-(N : Real) * (delta ^ 2 / (2 * (c : Real)))) := by
    have hsubset :
        {omega | delta <= ‖average N omega‖} ⊆
          {omega | delta <= average N omega} ∪
            {omega | delta <= -(average N omega)} := by
      intro omega homega
      change delta <= ‖average N omega‖ at homega
      change delta <= average N omega ∨ delta <= -(average N omega)
      rw [Real.norm_eq_abs] at homega
      rcases le_total 0 (average N omega) with hnonneg | hnonpos
      · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using homega)
      · exact Or.inr (by simpa [abs_of_nonpos hnonpos] using homega)
    have hplus :
        mu.real {omega | delta <= average N omega} <=
          Real.exp (-delta ^ 2 / (2 * (cAverage N : Real))) :=
      (haverage_subGaussian N).measure_ge_le hdelta
    have hminus :
        mu.real {omega | delta <= -(average N omega)} <=
          Real.exp (-delta ^ 2 / (2 * (cAverage N : Real))) := by
      simpa only [Pi.neg_apply] using
        (haverage_subGaussian N).neg.measure_ge_le hdelta
    have hexponent :
        -delta ^ 2 / (2 * (cAverage N : Real)) =
          -(N : Real) * (delta ^ 2 / (2 * (c : Real))) := by
      rw [hcAverage N hN]
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      have hc0 : (c : Real) ≠ 0 := ne_of_gt hc
      field_simp [hN0, hc0]
    calc
      mu.real {omega | delta <= ‖average N omega‖} <=
          mu.real ({omega | delta <= average N omega} ∪
            {omega | delta <= -(average N omega)}) :=
        measureReal_mono hsubset (by finiteness)
      _ <= mu.real {omega | delta <= average N omega} +
          mu.real {omega | delta <= -(average N omega)} :=
        measureReal_union_le _ _
      _ <= Real.exp (-delta ^ 2 / (2 * (cAverage N : Real))) +
          Real.exp (-delta ^ 2 / (2 * (cAverage N : Real))) :=
        add_le_add hplus hminus
      _ = 2 * Real.exp (-(N : Real) *
          (delta ^ 2 / (2 * (c : Real)))) := by
        rw [hexponent]
        ring
  have hBC (delta : Real) (hdelta : 0 < delta) :
      ∀ᵐ omega ∂mu, ∀ᶠ N in atTop, omega ∉
        {omega | delta <= ‖average N omega‖} := by
    let K : Real := delta ^ 2 / (2 * (c : Real))
    have hK : 0 < K := by
      dsimp [K]
      exact div_pos (sq_pos_of_pos hdelta) (mul_pos two_pos hc)
    have hexp_summable :
        Summable (fun N : Nat =>
          2 * Real.exp (-(N : Real) * K)) := by
      have hbase : Summable (fun N : Nat => Real.exp ((N : Real) * (-K))) :=
        Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hK)
      have hbase' : Summable (fun N : Nat => Real.exp (-(N : Real) * K)) := by
        simpa [mul_neg, neg_mul] using hbase
      exact hbase'.mul_left 2
    have hmeasureReal_summable :
        Summable (fun N : Nat =>
          mu.real {omega | delta <= ‖average N omega‖}) := by
      refine hexp_summable.of_nonneg_of_le
        (fun _ => measureReal_nonneg) ?_
      intro N
      by_cases hN : N = 0
      · subst N
        have hempty : {omega : Omega | delta <= (0 : Real)} = ∅ := by
          simp [not_le.mpr hdelta]
        simp [average, hzero, hempty, not_le.mpr hdelta]
      · simpa [K] using htail delta hdelta.le N (Nat.pos_of_ne_zero hN)
    have hmeasure_tsum :
        (∑' N : Nat, mu {omega | delta <= ‖average N omega‖}) ≠ ∞ := by
      have hlt := hmeasureReal_summable.tsum_ofReal_lt_top
      rw [show
        (∑' N : Nat, mu {omega | delta <= ‖average N omega‖}) =
          ∑' N : Nat,
            ENNReal.ofReal (mu.real {omega | delta <= ‖average N omega‖}) by
          apply tsum_congr
          intro N
          exact (ofReal_measureReal
            (μ := mu)
            (s := {omega | delta <= ‖average N omega‖})).symm]
      exact hlt.ne
    exact ae_eventually_notMem hmeasure_tsum
  obtain ⟨v, -, hvpos, hvlim⟩ :
      ∃ v : Nat -> Real, StrictAnti v ∧ (forall n, 0 < v n) ∧
        Tendsto v atTop (nhds 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have hall : ∀ᵐ omega ∂mu, forall i, ∀ᶠ N in atTop,
      omega ∉ {omega | v i <= ‖average N omega‖} :=
    ae_all_iff.2 (fun i => hBC (v i) (hvpos i))
  filter_upwards [hall] with omega homega
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨i, hi⟩ : ∃ i, v i < epsilon :=
    ((tendsto_order.1 hvlim).2 epsilon hepsilon).exists
  obtain ⟨N, hN⟩ := eventually_atTop.1 (homega i)
  refine ⟨N, fun n hn => ?_⟩
  have hnorm : ‖average n omega‖ < v i := by
    simpa only [Set.mem_setOf_eq, not_le] using hN n hn
  change dist (average n omega) 0 < epsilon
  simpa [Real.dist_eq] using hnorm.trans hi

end QubitOracle.Paper
