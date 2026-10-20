import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.P1ControllerLocalization
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedNormality
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.AdaptiveDesign.PolynomialSqrtExponential
import QubitOracle.AdaptiveDesign.RunningMaximumMoments
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1AdaptiveRidgePolicy
/-! Uniform moments of a bound on all inverse Frobenius allocation
weights used so far. Only the concrete localization theorem is used. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
local instance P1InverseAllocationMoments_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1InverseAllocationMoments_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

def inverseAllocationSum (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) : ℝ :=
  ∑ i : Fin 3, (weight .frobenius (controller .frobenius (n+1)
    (estimate .frobenius ridge refresh (n+1) path)) i)⁻¹

theorem reporting_weight_pos (loss : Loss) (k : ℕ) (x : Fin 3 → ℝ) (i : Fin 3) :
    0 < weight loss (controller loss k x) i :=
  (div_pos (ExplorationRidge.epsilon_pos k) (by norm_num)).trans_le (weight_floor loss k x i)

theorem inverseAllocationSum_nonneg (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    0 ≤ inverseAllocationSum ridge refresh n path :=
  Finset.sum_nonneg (fun i _ => (inv_pos.mpr (reporting_weight_pos _ _ _ i)).le)

theorem inverseAllocationSum_bound (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    inverseAllocationSum ridge refresh n path ≤ 18*((n:ℝ)+1) := by
  calc
    _ ≤ ∑ _i : Fin 3, 3*(((n+1:ℕ):ℝ)+1) :=
      Finset.sum_le_sum (fun i _ => inverse_weight_bound .frobenius (n+1) _ i)
    _ ≤ _ := by simp; linarith [Nat.cast_nonneg (α:=ℝ) n]

theorem inverseAllocationSum_measurable (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) :
    Measurable (inverseAllocationSum ridge refresh n) :=
  historyStatistic_measurable .frobenius ridge refresh (n+1) (fun s =>
    ∑ i : Fin 3, (weight .frobenius (controller .frobenius (n+1) (s.gram⁻¹.mulVec s.rhs)) i)⁻¹)

def allocationEnvelope (C ridge : ℝ) (refresh : ℕ → Bool) : ℕ → Path → ℝ :=
  RunningMaximumMoments.running C (inverseAllocationSum ridge refresh)

theorem allocationEnvelope_moments (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∃ C : ℝ, 3 ≤ C ∧ ∀ p : ℕ,
      UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
        (allocationEnvelope C ridge refresh) p := by
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ
  obtain ⟨δ,κ,hδ,hκ,hnear⟩ := frobenius_weight_local_lower θ.1 hθ
  let C := max 3 (3/κ)
  have hC : 0 ≤ C := (by norm_num : (0:ℝ)≤3).trans (le_max_left _ _)
  let bad := fun n => {path | δ ≤ ‖reportedError .frobenius ridge refresh θ.1 (n+1) path‖}
  have hgood (n : ℕ) (path : Path) (hx : path ∉ bad n) : inverseAllocationSum ridge refresh n path ≤ C := by
    have hh := hnear (controller .frobenius (n+1) (estimate .frobenius ridge refresh (n+1) path)) (not_le.mp hx)
    calc
      _ ≤ ∑ _i : Fin 3, κ⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [one_div] using one_div_le_one_div_of_le hκ (hh i)
      _ = 3/κ := by simp; ring
      _ ≤ C := le_max_right _ _
  obtain ⟨B,c,hB,hc,ht⟩ := frobenius_controller_localization ridge hr refresh θ hθ δ hδ
  refine ⟨C,le_max_left _ _,fun p => ?_⟩
  apply RunningMaximumMoments.moment C hC _ (inverseAllocationSum_measurable ridge refresh)
    (inverseAllocationSum_nonneg ridge refresh) (fun n => 18*((n:ℝ)+1)) (fun _ => by positivity)
    (inverseAllocationSum_bound ridge refresh) bad hgood p
  have hs := PolynomialSqrtExponential.summable_of_tail (fun n => μ.real (bad n))
    (fun _ => measureReal_nonneg) B c hB.le hc (by simpa only [Nat.cast_add,Nat.cast_one] using ht) p
  simpa only [mul_pow,mul_assoc] using hs.mul_left ((18:ℝ)^p)

theorem allocationEnvelope_positive (C ridge : ℝ) (refresh : ℕ → Bool) (hC : 3 ≤ C)
    (n : ℕ) (path : Path) : 0 < allocationEnvelope C ridge refresh n path :=
  (show (0:ℝ)<3 by norm_num).trans_le (hC.trans (RunningMaximumMoments.base_le _ _ _ _))

theorem allocationEnvelope_controls (C ridge : ℝ) (refresh : ℕ → Bool) (hC : 3 ≤ C)
    (n t : ℕ) (ht : t<n) (path : Path) (i : Fin 3) :
    (allocationEnvelope C ridge refresh n path)⁻¹ ≤
      (actualAction (policy .frobenius ridge refresh) t path).weight i := by
  rw [action_eq_lastRefresh]
  let k := P1.lastRefresh refresh t
  have hk : k ≤ t := P1.lastRefresh_le refresh t
  have hw := reporting_weight_pos .frobenius k (estimate .frobenius ridge refresh k path) i
  have hinv : (weight .frobenius (controller .frobenius k (estimate .frobenius ridge refresh k path)) i)⁻¹ ≤
      allocationEnvelope C ridge refresh n path := by
    cases hkn : k with
    | zero =>
      have hh := inverse_weight_bound .frobenius k (estimate .frobenius ridge refresh k path) i
      rw [hkn] at hh
      norm_num at hh
      exact hh.trans (hC.trans (RunningMaximumMoments.base_le _ _ _ _))
    | succ j =>
      have hh : (weight .frobenius (controller .frobenius (j+1)
          (estimate .frobenius ridge refresh (j+1) path)) i)⁻¹ ≤ inverseAllocationSum ridge refresh j path :=
        Finset.single_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 3))) =>
          (inv_pos.mpr (reporting_weight_pos _ _ _ l)).le) (Finset.mem_univ i)
      exact hh.trans (RunningMaximumMoments.term_le C (inverseAllocationSum ridge refresh) n j (by omega) path)
  have hh := one_div_le_one_div_of_le (inv_pos.mpr hw) hinv
  simpa only [one_div,inv_inv,controllerAction,referenceAction,k] using hh

end
end QubitOracle.AdaptiveDesign.P1Weighted
