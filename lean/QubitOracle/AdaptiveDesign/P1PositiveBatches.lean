import QubitOracle.Paper.P1AdaptiveRidgeConsistency

/-! P1 for every prescribed sequence of positive finite batch sizes.
The refresh indicator is explicitly the set of cumulative batch endpoints.
It is false strictly inside every batch, so the recursive policy really
holds its selected frame fixed until the next batch starts. -/
namespace QubitOracle.AdaptiveDesign.P1
open QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

def batchEndpoint (m : Nat → Nat) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range j, m k

def batchRefresh (m : Nat → Nat) (n : Nat) : Bool := by
  classical
  exact decide (∃ j, batchEndpoint m j = n)

theorem batchEndpoint_ge_index (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    ∀ j, j ≤ batchEndpoint m j := by
  intro j
  induction j with
  | zero => simp [batchEndpoint]
  | succ j ih =>
    simp only [batchEndpoint, Finset.sum_range_succ] at *
    have h := hm j
    omega

theorem batchEndpoint_strictMono (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    StrictMono (batchEndpoint m) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [batchEndpoint, Finset.sum_range_succ]
  exact Nat.lt_add_of_pos_right (hm j)

theorem batchRefresh_unbounded (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    ∀ K, ∃ n, K ≤ n ∧ batchRefresh m n = true := by
  intro K
  refine ⟨batchEndpoint m K, batchEndpoint_ge_index m hm K, ?_⟩
  simp only [batchRefresh, decide_eq_true_eq]
  exact ⟨K, rfl⟩

theorem batchRefresh_at_endpoint (m : Nat → Nat) (j : Nat) :
    batchRefresh m (batchEndpoint m j) = true := by
  simp only [batchRefresh, decide_eq_true_eq]
  exact ⟨j, rfl⟩

theorem batchRefresh_false_inside (m : Nat → Nat) (hm : ∀ j, 0 < m j)
    (j n : Nat) (hl : batchEndpoint m j < n)
    (hu : n < batchEndpoint m (j+1)) : batchRefresh m n = false := by
  simp only [batchRefresh, decide_eq_false_iff_not]
  rintro ⟨k, hk⟩
  have hmono := batchEndpoint_strictMono m hm
  have hlow : j < k := hmono.lt_iff_lt.mp (hk ▸ hl)
  have hhigh : k < j+1 := hmono.lt_iff_lt.mp (hk ▸ hu)
  omega

/-- Every finite positive batch schedule, including unit-shot updates, has
strongly consistent all-data ridge estimates and the optimal Bures information
limit on its actual adaptive Born path measure. No external scientific axiom
or assumption of estimator consistency occurs. -/
theorem mixed_qubit_positive_batches
    (m : Nat → Nat) (hm : ∀ j, 0 < m j)
    (ridge : Real) (_hridge : 0 < ridge)
    (theta : OneQubitPhysicalParameter)
    (ht : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂pathMeasure (adaptiveRidgePolicy ridge (batchRefresh m)) theta,
      Tendsto (fun n => pathRidgeEstimator ridge (batchRefresh m) n path)
        atTop (nhds theta.1) ∧
      Tendsto (fun n => frameFisher theta.1
        (actualFrame (adaptiveRidgePolicy ridge (batchRefresh m)) n path))
        atTop (nhds (mixedBuresTarget theta.1)) ∧
      (∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range N, frameFisher theta.1
          (actualFrame (adaptiveRidgePolicy ridge (batchRefresh m)) k path) i j)
        atTop (nhds (mixedBuresTarget theta.1 i j))) ∧
      (∀ i j : Fin 3, Tendsto (fun N : Nat => (N : Real)⁻¹ *
        ∑ k ∈ Finset.range N,
          QubitOracle.mixedAxisFisher theta.1
            (actualAxis (adaptiveRidgePolicy ridge (batchRefresh m)) k path) i j)
        atTop (nhds (mixedBuresTarget theta.1 i j))) :=
  mixed_qubit_consistency_and_optimal_information ridge (batchRefresh m)
    (batchRefresh_unbounded m hm) theta ht


/-- The physical controller sequence itself is consistent at every interior
truth, because its fallback to the center becomes inactive eventually. -/
theorem mixed_qubit_controller_positive_batches
    (m : Nat → Nat) (ridge : Real) (theta : OneQubitPhysicalParameter)
    (ht : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂pathMeasure (adaptiveRidgePolicy ridge (batchRefresh m)) theta,
      Tendsto (fun n => interiorize (pathRidgeEstimator ridge (batchRefresh m) n path))
        atTop (nhds theta.1) := by
  filter_upwards [pathRidgeEstimator_tendsto_ae ridge (batchRefresh m) theta] with path hp
  exact interiorize_tendsto ht hp

end
end QubitOracle.AdaptiveDesign.P1
