import QubitOracle.AdaptiveDesign.TangentGLSActualRates
import QubitOracle.AdaptiveDesign.FiniteHistoryStatistics
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn

/-! True probabilities become uniformly separated from the known clipping
floor along the actual adaptive protocol. No convergence of the chosen
unitary complement is required. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory
open scoped BigOperators Topology ComplexOrder Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {d : ℕ} {O : Type} [Fintype O]

theorem mass_tendsto_reference
    (P : FinitePOVM (Fin (d+1)) O)
    (controller : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => controllerTrueOverlapSq (controller n)) atTop (𝓝 1)) (y : O) :
    Tendsto (fun n => mass P (controller n) y) atTop (𝓝 (referenceProbability P y)) := by
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ}
    isCompact_unitaryMatrices controller hU
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h
    (fun U => mass P U y) (referenceProbability P y) ?_
  intro U hU hoverlap
  exact ⟨(mass_continuous P y).continuousAt, mass_of_overlap_one P U hU hoverlap y⟩

theorem four_referenceFloor_le [Nonempty O] (P : FinitePOVM (Fin (d+1)) O) (y : O) :
    4*referenceFloor P ≤ referenceProbability P y := by
  classical
  have hb := Finset.inf'_le (s := Finset.univ) (f := referenceProbability P) (Finset.mem_univ y)
  unfold referenceFloor
  linarith

theorem referenceFloor_le_one [Nonempty O] (P : FinitePOVM (Fin (d+1)) O)
    (hp : Regular P) : referenceFloor P ≤ 1 := by
  let y : O := Classical.choice inferInstance
  have hb := four_referenceFloor_le P y
  have hf := referenceFloor_pos P hp
  have hm : referenceProbability P y ≤ 1 := by
    have hs : ∑ z, referenceProbability P z = 1 := by
      have heq := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (A 0 0).re) P.complete
      simpa [referenceProbability, Matrix.sum_apply, Complex.re_sum] using heq
    have he := Finset.single_le_sum (fun z _ => (hp z).le) (Finset.mem_univ y)
    exact he.trans_eq hs
  linarith

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actual_probabilities_tendsto
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      ∀ y, Tendsto (fun n => bornProbability P truth
        (actualState P hI regularization hr batchSize path n).action y)
        atTop (𝓝 (referenceProbability P y)) := by
  filter_upwards [adaptive_consistency P hI regularization hr truth batchSize hpositive] with path hp
  have hproj : Tendsto (fun n => GlobalPFSIC.frameProjector
      (measurementFrame P hI regularization hr batchSize path n)) atTop
      (𝓝 (GlobalPFSIC.frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    exact hp.2.2
  have hrel := GlobalPFSIC.relative_overlap_tendsto (trueFrame d truth)
    (trueFrame_unitary d truth) (measurementFrame P hI regularization hr batchSize path) hproj
  intro y
  simp only [bornProbability_pure_eq_mass]
  exact mass_tendsto_reference P
    (fun n => (trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path n)
    (fun n => GlobalPFSIC.relative_unitary _ _ (trueFrame_unitary d truth)
      (measurementFrame_unitary P hI regularization hr batchSize path n)) hrel y

theorem actual_probabilities_eventually_regular
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      ∃ K : ℕ, ∀ t ≥ K, ∀ y, 2*referenceFloor P ≤ bornProbability P truth
        (actualState P hI regularization hr batchSize path t).action y := by
  filter_upwards [actual_probabilities_tendsto P hI truth regularization hr batchSize hpositive]
    with path hpath
  have he (y : O) : ∀ᶠ t in atTop, 2*referenceFloor P ≤ bornProbability P truth
      (actualState P hI regularization hr batchSize path t).action y := by
    have hlt : 2*referenceFloor P < referenceProbability P y := by
      have hf := referenceFloor_pos P hp
      have hb := four_referenceFloor_le P y
      linarith
    exact ((hpath y).eventually (Ioi_mem_nhds hlt)).mono (fun t ht => ht.le)
  exact eventually_atTop.mp (Filter.eventually_all.mpr he)

theorem actual_recordFeature_eq
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) (r : Fin n × O) :
    recordFeature (actualRecords P hI regularization hr batchSize path n) r =
      responseVector P (actualState P hI regularization hr batchSize path r.1).action r.2 := by
  apply toMatrix_injective
  rfl

theorem actual_fittedProbability_eq
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (truth : PureVector d) (path : AdaptiveInfinitePath O) (n : ℕ) (r : Fin n × O) :
    fittedProbability truth (actualRecords P hI regularization hr batchSize path n) r =
      bornProbability P truth (actualState P hI regularization hr batchSize path r.1).action r.2 := by
  rw [fittedProbability, actual_recordFeature_eq]
  rfl

theorem badRowCount_bound {n : ℕ} (truth : PureVector d) (data : Fin n → Record d O)
    (floor : ℝ) (K : ℕ)
    (hregular : ∀ t : Fin n, K ≤ t.val → ∀ y, 2*floor ≤ fittedProbability truth data (t,y)) :
    badRowCount truth data floor ≤ K*Fintype.card O := by
  classical
  let bad := Finset.univ.filter (fun r : Fin n × O => fittedProbability truth data r < 2*floor)
  have hsmall (r : ↥bad) : r.val.1.val < K := by
    by_contra hn
    have hb := (Finset.mem_filter.mp r.property).2
    exact (not_lt_of_ge (hregular r.val.1 (le_of_not_gt hn) r.val.2)) hb
  let f : ↥bad → Fin K × O := fun r => (⟨r.val.1.val,hsmall r⟩,r.val.2)
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun z : Fin K × O => z.1.val) hrs
    · exact congrArg (fun z : Fin K × O => z.2) hrs
  have hc := Fintype.card_le_of_injective f hinj
  change bad.card ≤ K*Fintype.card O
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hc

end
end QubitOracle.AdaptiveDesign.TangentGLS
