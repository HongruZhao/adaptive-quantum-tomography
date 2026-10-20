import Mathlib

/-!
# Deterministic estimates for adaptive LAN conditions

This module isolates the elementary estimates used when checking the adaptive
LAN sufficient conditions.  It contains no probabilistic assumptions: the
results concern finite sums, threshold indicators, exceptional-round counts,
and finite collections of uniform bounds.
-/

namespace QubitOracle.Paper

open scoped BigOperators

/-! ## Summed DQM defects -/

/-- If there are at most `n` rounds and every DQM defect is at most
`B / n^2`, then the total defect is at most `B / n`. -/
theorem sum_per_round_dqm_defect_le
    {ι : Type*} (rounds : Finset ι) (defect : ι → ℝ)
    (n : ℕ) (B : ℝ) (hn : 0 < n) (hrounds : rounds.card ≤ n)
    (hB : 0 ≤ B)
    (hdefect : ∀ t ∈ rounds, defect t ≤ B / (n : ℝ) ^ 2) :
    ∑ t ∈ rounds, defect t ≤ B / (n : ℝ) := by
  have hperRound : 0 ≤ B / (n : ℝ) ^ 2 :=
    div_nonneg hB (sq_nonneg (n : ℝ))
  have hcard : (rounds.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hrounds
  calc
    ∑ t ∈ rounds, defect t
        ≤ ∑ _t ∈ rounds, B / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t ht => hdefect t ht
    _ = (rounds.card : ℝ) * (B / (n : ℝ) ^ 2) := by simp
    _ ≤ (n : ℝ) * (B / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hperRound
    _ = B / (n : ℝ) := by
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hn0] <;> ring

/-! ## Bounded scores and Lindeberg indicators -/

/-- The real-valued strict-threshold indicator used in Lindeberg sums. -/
noncomputable def lindebergIndicator (threshold size : ℝ) : ℝ :=
  if threshold < size then 1 else 0

@[simp]
theorem lindebergIndicator_eq_zero_of_le
    {threshold size : ℝ} (hsize : size ≤ threshold) :
    lindebergIndicator threshold size = 0 := by
  simp [lindebergIndicator, not_lt.mpr hsize]

/-- A score bounded by `C` cannot cross the Lindeberg threshold once
`C ≤ epsilon * sqrt n`. -/
theorem bounded_score_lindebergIndicator_eq_zero
    {E : Type*} [Norm E] (score : E) {C epsilon : ℝ} {n : ℕ}
    (hscore : ‖score‖ ≤ C)
    (hthreshold : C ≤ epsilon * Real.sqrt (n : ℝ)) :
    lindebergIndicator (epsilon * Real.sqrt (n : ℝ)) ‖score‖ = 0 :=
  lindebergIndicator_eq_zero_of_le (hscore.trans hthreshold)

/-- Uniformly bounded scores make the entire finite Lindeberg sum identically
zero after the threshold exceeds the common bound. -/
theorem bounded_scores_lindeberg_sum_eq_zero
    {ι E : Type*} [Norm E] (rounds : Finset ι) (score : ι → E)
    {C epsilon : ℝ} {n : ℕ}
    (hscore : ∀ t ∈ rounds, ‖score t‖ ≤ C)
    (hthreshold : C ≤ epsilon * Real.sqrt (n : ℝ)) :
    ∑ t ∈ rounds,
        ‖score t‖ ^ 2 *
          lindebergIndicator (epsilon * Real.sqrt (n : ℝ)) ‖score t‖ = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  rw [bounded_score_lindebergIndicator_eq_zero
    (score := score t) (hscore := hscore t ht) (hthreshold := hthreshold)]
  simp

/-! ## Sublinear exceptional counts -/

/-- An elementary epsilon formulation of a natural-valued count being
sublinear.  It is convenient when no asymptotic filter machinery is needed. -/
def SublinearCount (count : ℕ → ℕ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n, N ≤ n →
    (count n : ℝ) ≤ delta * (n : ℝ)

/-- A pointwise smaller count inherits sublinearity. -/
theorem sublinearCount_mono
    {exceptional budget : ℕ → ℕ} (hbudget : SublinearCount budget)
    (hcount : ∀ n, exceptional n ≤ budget n) :
    SublinearCount exceptional := by
  intro delta hdelta
  obtain ⟨N, hN⟩ := hbudget delta hdelta
  refine ⟨N, ?_⟩
  intro n hn
  calc
    (exceptional n : ℝ) ≤ (budget n : ℝ) := by
      exact_mod_cast (hcount n)
    _ ≤ delta * (n : ℝ) := hN n hn

/-- A count dominated by `delta * n` has normalized size at most `delta`. -/
theorem exceptional_count_ratio_le
    {exceptional budget n : ℕ} {delta : ℝ} (hn : 0 < n)
    (hcount : exceptional ≤ budget)
    (hbudget : (budget : ℝ) ≤ delta * (n : ℝ)) :
    (exceptional : ℝ) / (n : ℝ) ≤ delta := by
  have hnReal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  apply (div_le_iff₀ hnReal).2
  calc
    (exceptional : ℝ) ≤ (budget : ℝ) := by
      exact_mod_cast hcount
    _ ≤ delta * (n : ℝ) := hbudget

/-- The normalized form of `SublinearCount`: every positive tolerance
eventually bounds `count n / n`. -/
theorem sublinearCount_ratio_eventually_le
    {count : ℕ → ℕ} (hcount : SublinearCount count)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n, N ≤ n → (count n : ℝ) / (n : ℝ) ≤ delta := by
  obtain ⟨N, hN⟩ := hcount delta hdelta
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hNn : N ≤ n := (Nat.le_max_left N 1).trans hn
  have hOneN : 1 ≤ n := (Nat.le_max_right N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hOneN
  exact exceptional_count_ratio_le hnpos le_rfl (hN n hNn)

/-- Removing an exceptional count from `n` changes the normalized regular
count by exactly the exceptional fraction. -/
theorem regular_count_ratio_eq_one_sub_exceptional
    {exceptional n : ℕ} (hcount : exceptional ≤ n) (hn : 0 < n) :
    ((n - exceptional : ℕ) : ℝ) / (n : ℝ) =
      1 - (exceptional : ℝ) / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [Nat.cast_sub hcount]
  field_simp [hn0] <;> ring

/-- If exceptional-round costs are bounded by `C` and the exceptional count
is at most `delta * n`, their normalized total is at most `delta * C`. -/
theorem exceptional_average_le
    {ι : Type*} (exceptional : Finset ι) (cost : ι → ℝ)
    (n : ℕ) (delta C : ℝ) (hn : 0 < n) (hC : 0 ≤ C)
    (hcard : (exceptional.card : ℝ) ≤ delta * (n : ℝ))
    (hcost : ∀ i ∈ exceptional, cost i ≤ C) :
    (∑ i ∈ exceptional, cost i) / (n : ℝ) ≤ delta * C := by
  have hsum :
      (∑ i ∈ exceptional, cost i) ≤ (exceptional.card : ℝ) * C := by
    calc
      ∑ i ∈ exceptional, cost i ≤ ∑ _i ∈ exceptional, C :=
        Finset.sum_le_sum fun i hi => hcost i hi
      _ = (exceptional.card : ℝ) * C := by simp
  have hscaled :
      (exceptional.card : ℝ) * C ≤ (delta * (n : ℝ)) * C :=
    mul_le_mul_of_nonneg_right hcard hC
  have hnReal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  apply (div_le_iff₀ hnReal).2
  calc
    ∑ i ∈ exceptional, cost i ≤ (exceptional.card : ℝ) * C := hsum
    _ ≤ (delta * (n : ℝ)) * C := hscaled
    _ = (delta * C) * (n : ℝ) := by ring

/-! ## Common constants for compact-uniform estimates -/

/-- Every finite family of real constants is bounded above by one
nonnegative constant. -/
theorem finite_bounds_have_common_nonnegative_bound
    {ι : Type*} [Fintype ι] (bound : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, bound i ≤ C := by
  classical
  refine ⟨∑ i, |bound i|, Finset.sum_nonneg (fun i _ => abs_nonneg (bound i)), ?_⟩
  intro i
  calc
    bound i ≤ |bound i| := le_abs_self (bound i)
    _ ≤ ∑ j, |bound j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (bound j)) (Finset.mem_univ i)

/-- Finitely many bounds that are individually uniform on a compact set can
be replaced by one common nonnegative constant.  Compactness is used upstream
to produce each individual bound; this deterministic lemma only combines
them. -/
theorem compact_uniform_bounds_to_common_constant
    {ι Θ E : Type*} [Fintype ι] [Norm E]
    (K : Set Θ) (quantity : ι → Θ → E)
    (hbound : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ K, ‖quantity i θ‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i θ, θ ∈ K → ‖quantity i θ‖ ≤ C := by
  classical
  let bound : ι → ℝ := fun i => Classical.choose (hbound i)
  have hchosen :
      ∀ i, 0 ≤ bound i ∧ ∀ θ ∈ K, ‖quantity i θ‖ ≤ bound i := by
    intro i
    exact Classical.choose_spec (hbound i)
  obtain ⟨C, hC, hcommon⟩ := finite_bounds_have_common_nonnegative_bound bound
  refine ⟨C, hC, ?_⟩
  intro i θ hθ
  exact ((hchosen i).2 θ hθ).trans (hcommon i)

end QubitOracle.Paper
