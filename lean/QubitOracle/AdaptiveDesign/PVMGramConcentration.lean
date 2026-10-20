-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.AdaptiveOperatorConcentration
import QubitOracle.AdaptiveDesign.PVMGramTangentBounds
import QubitOracle.AdaptiveDesign.PVMPilotConcentration

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMPilotAdaptive PVMPilotSchedule
open Filter MeasureTheory ProbabilityTheory AdaptiveRidgeConsistency SequentialRidgeController
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def conditionalGramSum (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) : Operator d :=
  ∑ k ∈ Finset.range n, meanGram (k,(PVMPilotAdaptive.actualState d batchSize path k).action)

theorem gram_deviation_concentration (truth : PureVector d) (batchSize : ℕ → ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)).real
        {path | δ*((n+1:ℕ):ℝ) ≤ ‖realizedGram batchSize (n+1) path-conditionalGramSum batchSize (n+1) path‖} ≤
      B*Real.exp (-c*((n+1:ℕ):ℝ)) := by
  have hh := AdaptiveOperatorConcentration.normed (PVMPilotAdaptive.adaptiveProtocol d batchSize)
    (pureParameter d truth) (fun _ _ => rfl) gramNoise (gramNoise_mean _)
    (2*gramBound d) (mul_nonneg (by norm_num) (gramBound_nonnegative d)) gramNoise_bound δ hδ
  have hdesign (k : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
      (PVMPilotAdaptive.adaptiveProtocol d batchSize).design k (adaptiveInfinitePathPrefix k path) =
        (k,(PVMPilotAdaptive.actualState d batchSize path k).action) := rfl
  simpa only [realizedGram,conditionalGramSum,← Finset.sum_sub_distrib,gramNoise,
    actualVectorResponse,hdesign] using hh

theorem frameParameter_frozen (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    frameParameter (measurementFrame d batchSize path n) =
      (pureParameter d (actualPreliminary batchSize path (lastRefresh (batchRefresh batchSize) n))).val := by
  apply toMatrix_injective
  change frameProjector (measurementFrame d batchSize path n) =
    projectedMatrix d (toMatrix (PVMPilotAdaptive.rawEstimator d batchSize path (lastRefresh (batchRefresh batchSize) n)))
  rw [PVMPilotAdaptive.measurementFrame_eq_frozenController]
  exact controllerFrame_firstProjector d _

def lateAlignmentFailure (truth : PureVector d) (batchSize : ℕ → ℕ) (δ : ℝ) (n : ℕ) :
    Set (AdaptiveInfinitePath (PVMOutcome d)) :=
  ⋃ k ∈ Finset.Ico (n/2) n,
    {path | δ ≤ ‖actualPreliminaryError batchSize truth (lastRefresh (batchRefresh batchSize) k) path‖}

theorem late_alignment_concentration (truth : PureVector d) (batchSize : ℕ → ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)).real
        (lateAlignmentFailure truth batchSize δ n ∪ {path | δ ≤ ‖actualPreliminaryError batchSize truth n path‖}) ≤
      ((n:ℝ)+1)*B*Real.exp (-c*mass (lastRefresh (batchRefresh batchSize) (n/2))) := by
  obtain ⟨B,c,hB,hc,ht⟩ := PVMPilotConcentration.preliminary_all batchSize truth δ hδ
  refine ⟨B,c,hB,hc,fun n => ?_⟩
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)
  let k0 := lastRefresh (batchRefresh batchSize) (n/2)
  have hmass (k : ℕ) (hk : n/2 ≤ k) : mass k0 ≤ mass (lastRefresh (batchRefresh batchSize) k) :=
    mass_mono (lastRefresh_monotone _ hk)
  have hb (k : ℕ) (hk : k ∈ Finset.Ico (n/2) n) :
      μ.real {path | δ ≤ ‖actualPreliminaryError batchSize truth (lastRefresh (batchRefresh batchSize) k) path‖} ≤
      B*Real.exp (-c*mass k0) := by
    apply (ht _).trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hmass k (Finset.mem_Ico.mp hk).1) hc.le]
  have hf : μ.real {path | δ ≤ ‖actualPreliminaryError batchSize truth n path‖} ≤
      B*Real.exp (-c*mass k0) := by
    apply (ht n).trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.exp_le_exp.mpr
    have hm := mass_mono ((lastRefresh_le (batchRefresh batchSize) (n/2)).trans (Nat.div_le_self n 2))
    nlinarith [mul_le_mul_of_nonneg_left hm hc.le]
  have hh : μ.real (lateAlignmentFailure truth batchSize δ n) ≤ (n:ℝ)*B*Real.exp (-c*mass k0) := by
    apply (measureReal_biUnion_finset_le (Finset.Ico (n/2) n) _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.Ico (n/2) n, B*Real.exp (-c*mass k0) := Finset.sum_le_sum hb
      _ = ((n-n/2:ℕ):ℝ)*(B*Real.exp (-c*mass k0)) := by simp
      _ ≤ _ := by
        have hn : ((n-n/2:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n (n/2)
        nlinarith [mul_le_mul_of_nonneg_right hn (mul_nonneg hB.le (Real.exp_pos (-c*mass k0)).le)]
  exact (measureReal_union_le _ _).trans (by nlinarith only [hh,hf])

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
