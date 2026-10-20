import QubitOracle.Paper.P1AdaptiveRidgePolicy
import QubitOracle.AdaptiveDesign.RidgeConsistency

/-! # P1: all-observation consistency and optimal information
No consistency, information convergence, martingale CLT, APS concentration or
LAN assumption appears in the theorem premises. The experiment is the
explicit labeled Born protocol reconstructed from its finite histories.
-/
namespace QubitOracle.AdaptiveDesign.P1
open QubitOracle.Paper QubitOracle.AdaptiveDesign Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤

/-- The actual ridge estimator from the complete observed history is strongly
consistent under its own adaptive Born law. Refresh times may be arbitrary. -/
theorem pathRidgeEstimator_tendsto_ae (ridge : Real) (refresh : Nat → Bool)
    (theta : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂pathMeasure (adaptiveRidgePolicy ridge refresh) theta,
      Tendsto (fun n => pathRidgeEstimator ridge refresh n path) atTop (nhds theta.1) := by
  filter_upwards [sufficientStatistics_centered_ae
    (adaptiveRidgePolicy ridge refresh) theta] with path hp
  let a : Nat → Fin 3 → Real := fun n => actualAxis (adaptiveRidgePolicy ridge refresh) n path
  let y : Nat → Real := fun n => (path n).2.sign
  have hlim := normalizedRidgeEstimate_tendsto ridge a y theta.1 (1/3) (by norm_num)
    (fun i j => by simpa only [a, div_eq_mul_inv, mul_comm, one_mul] using hp.1 i j)
    (fun i => by simpa only [a, y, div_eq_mul_inv, mul_comm, one_mul] using hp.2 i)
  have heq : normalizedRidgeEstimate ridge a y =ᶠ[atTop]
      fun N => pathRidgeEstimator ridge refresh (N+1) path := by
    filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
    rw [normalizedRidgeEstimate_eq_raw ridge a y N (Nat.ne_of_gt hN),
      pathRidgeEstimator, pathRidgeState_gram, pathRidgeState_rhs]
    rfl
  exact (tendsto_add_atTop_iff_nat
    (f := fun n => pathRidgeEstimator ridge refresh n path) 1).1 (hlim.congr' heq)

/-- Frequent enough means only that prescribed refresh times are unbounded.
No upper bound on the gap or batch growth is needed. -/
theorem actualFrame_information_tendsto_ae (ridge : Real) (refresh : Nat → Bool)
    (hrefresh : ∀ K : Nat, ∃ n, K ≤ n ∧ refresh n = true)
    (theta : OneQubitPhysicalParameter)
    (ht : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂pathMeasure (adaptiveRidgePolicy ridge refresh) theta,
      Tendsto (fun n => frameFisher theta.1
        (actualFrame (adaptiveRidgePolicy ridge refresh) n path))
        atTop (nhds (mixedBuresTarget theta.1)) := by
  filter_upwards [pathRidgeEstimator_tendsto_ae ridge refresh theta] with path hp
  have hcontroller := (interiorize_tendsto ht hp).comp (lastRefresh_tendsto refresh hrefresh)
  have hinfo := canonicalUniformFrame_information_tendsto theta.1 ht
    (fun n => interiorize (pathRidgeEstimator ridge refresh (lastRefresh refresh n) path))
    hcontroller (fun n => interiorize_interior _)
  simpa only [actualFrame_eq_lastRefresh] using hinfo

private theorem fullAverage_zero {a : Nat → Real}
    (h : Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), a k) atTop (nhds 0)) :
    Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range N, a k) atTop (nhds 0) := by
  have hr : Tendsto (fun N : Nat => (N : Real) / ((N : Real)+1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : Real)
  have hscaled := hr.mul h
  simp only [mul_zero] at hscaled
  have ht : Tendsto (fun N : Nat => ((N+1 : Nat) : Real)⁻¹ *
      ∑ k ∈ Finset.range (N+1), a k) atTop (nhds 0) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
    have hn : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hn1 : (N : Real)+1 ≠ 0 := by positivity
    push_cast
    field_simp
  exact (tendsto_add_atTop_iff_nat
    (f := fun N : Nat => (N : Real)⁻¹ * ∑ k ∈ Finset.range N, a k) 1).1 ht

/-- Final P1 result: the literal estimator is consistent, the currently used
frame has oracle information, and both predictable and realized empirical
Fisher matrices converge to the Bures target. The zero Bloch vector is included. -/
theorem mixed_qubit_consistency_and_optimal_information
    (ridge : Real) (refresh : Nat → Bool)
    (hrefresh : ∀ K : Nat, ∃ n, K ≤ n ∧ refresh n = true)
    (theta : OneQubitPhysicalParameter)
    (ht : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂pathMeasure (adaptiveRidgePolicy ridge refresh) theta,
      Tendsto (fun n => pathRidgeEstimator ridge refresh n path) atTop (nhds theta.1) ∧
      Tendsto (fun n => frameFisher theta.1
        (actualFrame (adaptiveRidgePolicy ridge refresh) n path))
        atTop (nhds (mixedBuresTarget theta.1)) ∧
      (∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range N, frameFisher theta.1
          (actualFrame (adaptiveRidgePolicy ridge refresh) k path) i j)
        atTop (nhds (mixedBuresTarget theta.1 i j))) ∧
      (∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range N,
          QubitOracle.mixedAxisFisher theta.1
            (actualAxis (adaptiveRidgePolicy ridge refresh) k path) i j)
        atTop (nhds (mixedBuresTarget theta.1 i j))) := by
  filter_upwards [pathRidgeEstimator_tendsto_ae ridge refresh theta,
    actualFrame_information_tendsto_ae ridge refresh hrefresh theta ht,
    fisherInnovation_average_ae (adaptiveRidgePolicy ridge refresh) theta ht]
      with path hest hframe hinnov
  have hpred : ∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ k ∈ Finset.range N, frameFisher theta.1
        (actualFrame (adaptiveRidgePolicy ridge refresh) k path) i j)
      atTop (nhds (mixedBuresTarget theta.1 i j)) := by
    intro i j
    exact ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hframe i) j).cesaro_smul)
  refine ⟨hest, hframe, hpred, ?_⟩
  intro i j
  have hnoise := fullAverage_zero (hinnov i j)
  convert (hpred i j).add hnoise using 1
  · ext N
    rw [Finset.sum_sub_distrib]
    ring
  · ring

end
end QubitOracle.AdaptiveDesign.P1
