import QubitOracle.AdaptiveDesign.P1WeightedEndpoints

/-! Combined Theorem 3.1 and explicit axis/batch correspondence.
Paper copy t corresponds to Lean shot n=t-1. Lean axis labels 0,1,2
are the paper's tangent-first, tangent-second, radial labels 2,3,1.
The bridge lemmas identify the paper’s axes and frozen batch updates with the implemented process. -/
namespace QubitOracle.Paper.MainPaperTheorem31
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open QubitOracle.AdaptiveDesign
open P1Weighted
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

/-- At the same design estimate, both loss rules use the same axis construction. -/
theorem shared_axis_construction (r : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    (k : Fin 3) :
    axis (referenceAction .bures r hr) k = axis (referenceAction .frobenius r hr) k := rfl

/-- The actual axes are evaluated at the safeguarded estimate from the last update. -/
theorem axes_use_held_estimate (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (k : Fin 3) :
    axis (actualAction (policy loss ridge refresh) n path) k =
      ((P1.canonicalUniformFrame (heldController loss ridge refresh n path)).axis k).1 := by
  rw [action_eq_reference]
  rfl

theorem axes_at_refresh (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (k : Fin 3) (hn : refresh (n+1) = true) :
    axis (actualAction (policy loss ridge refresh) (n+1) path) k =
      ((P1.canonicalUniformFrame
        (controller loss (n+1) (estimate loss ridge refresh (n+1) path))).axis k).1 := by
  rw [action_at_refresh loss ridge refresh n path hn]
  rfl

theorem axes_between_refresh (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (k : Fin 3) (hn : refresh (n+1) = false) :
    axis (actualAction (policy loss ridge refresh) (n+1) path) k =
      axis (actualAction (policy loss ridge refresh) n path) k := by
  rw [action_between_refresh loss ridge refresh n path hn]

theorem last_refresh_at_batch_endpoint (m : ℕ → ℕ) (j : ℕ) :
    P1.lastRefresh (P1.batchRefresh m) (P1.batchEndpoint m j) = P1.batchEndpoint m j := by
  cases he : P1.batchEndpoint m j with
  | zero => rfl
  | succ n =>
    have hr := P1.batchRefresh_at_endpoint m j
    rw [he] at hr
    simp [P1.lastRefresh,hr]

/-- The entire pre-shot interval for one batch has the same last update. -/
theorem last_refresh_in_batch (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (j n : ℕ) :
    P1.batchEndpoint m j ≤ n → n < P1.batchEndpoint m (j+1) →
    P1.lastRefresh (P1.batchRefresh m) n = P1.batchEndpoint m j := by
  induction n with
  | zero =>
    intro hlo _
    have hz : P1.batchEndpoint m j = 0 := by omega
    simp [P1.lastRefresh,hz]
  | succ n ih =>
    intro hlo hhi
    by_cases he : P1.batchEndpoint m j = n+1
    · rw [← he]
      exact last_refresh_at_batch_endpoint m j
    · have hr := P1.batchRefresh_false_inside m hm j (n+1) (by omega) hhi
      simp only [P1.lastRefresh,hr,Bool.false_eq_true,↓reduceIte]
      exact ih (by omega) (by omega)

/-- The full action, comprising axes and probabilities, is selected at batch start. -/
theorem action_in_batch (loss : Loss) (ridge : ℝ) (m : ℕ → ℕ)
    (hm : ∀ j, 0 < m j) (j n : ℕ) (path : Path)
    (hlo : P1.batchEndpoint m j ≤ n) (hhi : n < P1.batchEndpoint m (j+1)) :
    actualAction (policy loss ridge (P1.batchRefresh m)) n path =
      controllerAction loss (P1.batchEndpoint m j)
        (estimate loss ridge (P1.batchRefresh m) (P1.batchEndpoint m j) path) := by
  rw [action_eq_lastRefresh,last_refresh_in_batch m hm j n hlo hhi]

/-- Every available axis is held fixed within a batch for either algorithm. -/
theorem axes_in_batch (loss : Loss) (ridge : ℝ) (m : ℕ → ℕ)
    (hm : ∀ j, 0 < m j) (j n : ℕ) (path : Path) (k : Fin 3)
    (hlo : P1.batchEndpoint m j ≤ n) (hhi : n < P1.batchEndpoint m (j+1)) :
    axis (actualAction (policy loss ridge (P1.batchRefresh m)) n path) k =
      ((P1.canonicalUniformFrame
        (controller loss (P1.batchEndpoint m j)
          (estimate loss ridge (P1.batchRefresh m) (P1.batchEndpoint m j) path))).axis k).1 := by
  rw [action_in_batch loss ridge m hm j n path hlo hhi]
  rfl

/-- Selection probabilities use the same held design estimate as the axes. -/
theorem weights_in_batch (loss : Loss) (ridge : ℝ) (m : ℕ → ℕ)
    (hm : ∀ j, 0 < m j) (j n : ℕ) (path : Path) (k : Fin 3)
    (hlo : P1.batchEndpoint m j ≤ n) (hhi : n < P1.batchEndpoint m (j+1)) :
    (actualAction (policy loss ridge (P1.batchRefresh m)) n path).weight k =
      weight loss (controller loss (P1.batchEndpoint m j)
        (estimate loss ridge (P1.batchRefresh m) (P1.batchEndpoint m j) path)) k := by
  rw [action_in_batch loss ridge m hm j n path hlo hhi]
  rfl

/-- The internal label order is tangent, tangent, radial. -/
theorem label_order (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    axis (referenceAction loss r hr) 0 = (mixedCanonicalRadialTangentFrame r).tangentFirst ∧
    axis (referenceAction loss r hr) 1 = (mixedCanonicalRadialTangentFrame r).tangentSecond ∧
    axis (referenceAction loss r hr) 2 = (mixedCanonicalRadialTangentFrame r).radial := by
  exact ⟨rfl,rfl,rfl⟩

/-- Combine the existing endpoints into the paper's consistency, information,
raw/physical Gaussian limits, and eventual-inactive-safeguard statement.
Only the paper's positive ridge, positive finite prescribed batches and
interior truth are assumed. -/
theorem theorem_3_1 (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter)
    (hθ : blochNormSq θ.1 < 1) :
    (∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
        (protocol (policy loss ridge (P1.batchRefresh m))) θ,
      Tendsto (fun n => estimate loss ridge (P1.batchRefresh m) n path) atTop (𝓝 θ.1) ∧
      Tendsto (fun n => controller loss n (estimate loss ridge (P1.batchRefresh m) n path)) atTop (𝓝 θ.1) ∧
      Tendsto (fun n => fisher θ.1 (actualAction (policy loss ridge (P1.batchRefresh m)) n path))
        atTop (𝓝 (informationTarget loss θ.1)) ∧
      (∀ i j, Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        fisher θ.1 (actualAction (policy loss ridge (P1.batchRefresh m)) t path) i j)
        atTop (𝓝 (informationTarget loss θ.1 i j))) ∧
      (∀ i j, Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        mixedAxisFisher θ.1 (actualAxis (policy loss ridge (P1.batchRefresh m)) t path) i j)
        atTop (𝓝 (informationTarget loss θ.1 i j)))) ∧
    TendstoInDistribution (normalizedError loss ridge (P1.batchRefresh m) θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ)
      (multivariateGaussian 0 (informationTarget loss θ.1)⁻¹) ∧
    TendstoInDistribution (controllerError loss ridge (P1.batchRefresh m) θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ)
      (multivariateGaussian 0 (informationTarget loss θ.1)⁻¹) ∧
    (∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
        (protocol (policy loss ridge (P1.batchRefresh m))) θ,
      (fun n => controller loss n (estimate loss ridge (P1.batchRefresh m) n path))
        =ᶠ[atTop] (fun n => estimate loss ridge (P1.batchRefresh m) n path)) := by
  refine ⟨positive_batches_consistency_information loss ridge hr m hm θ hθ,
    positive_batches_normal loss ridge hr m hm θ hθ,?_,?_⟩
  · rw [← covariance_eq_information_inv loss θ.1 hθ]
    exact controller_normal loss ridge hr (P1.batchRefresh m) (P1.batchRefresh_unbounded m hm) θ hθ
  · filter_upwards [estimate_consistent loss ridge hr (P1.batchRefresh m) θ] with path hp
    exact controller_eventually_eq hθ loss hp

#check @theorem_3_1
#check @P1Weighted.p1_main
#check @P1Weighted.completed_batches_normal
#check @P1Weighted.covariance_eq_information_inv
#print axioms shared_axis_construction
#print axioms axes_use_held_estimate
#print axioms axes_at_refresh
#print axioms axes_between_refresh
#print axioms last_refresh_at_batch_endpoint
#print axioms last_refresh_in_batch
#print axioms action_in_batch
#print axioms axes_in_batch
#print axioms weights_in_batch
#print axioms label_order
#print axioms theorem_3_1
#print axioms P1Weighted.p1_main
#print axioms P1Weighted.completed_batches_normal
#print axioms P1Weighted.covariance_eq_information_inv
end
end QubitOracle.Paper.MainPaperTheorem31
