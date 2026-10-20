-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralPreliminary

/-! Bounded martingale responses for a randomly selected PVM. Centering is
conditional on the selected basis and is then averaged over its label. -/
namespace QubitOracle.AdaptiveDesign.PVMGeneralGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMGeneralExploration
open Filter MeasureTheory ProbabilityTheory AdaptiveRidgeConsistency
open BoundedResponseQuarterRate ProbabilityCalculus FiniteDimensionalResponseRates
open scoped BigOperators InnerProductSpace Topology
noncomputable section
variable [PVMExplorationSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

lemma integral_bornKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (theta : PhysicalParameter (d+1)) (a : ℕ × Action d)
    (f : PVMGeneralExploration.Outcome d → E) :
    ∫ o, f o ∂bornKernel theta a =
      ∑ b : Setting d, settingWeight d a.1 b •
        ∑ k : Fin (d+1), basisProbability theta (settingBasis a.2 b) k • f (b,k) := by
  change (∫ o, f o ∂finiteMassMeasure (bornProbability theta a)
    (bornProbability_nonnegative theta a) (bornProbability_sum theta a)) = _
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type]
  simp only [PVMGeneralExploration.bornProbability, Finset.smul_sum, smul_smul]

def centeredBasis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (theta : PhysicalParameter (d+1))
    (v : (ℕ × Action d) → Setting d → Fin (d+1) → E)
    (a : ℕ × Action d) (o : PVMGeneralExploration.Outcome d) : E :=
  centeredLookup (basisProbability theta (settingBasis a.2 o.1)) (v a o.1) o.2

theorem centeredBasis_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (theta : PhysicalParameter (d+1))
    (v : (ℕ × Action d) → Setting d → Fin (d+1) → E) (a : ℕ × Action d) :
    ∫ o, centeredBasis theta v a o ∂bornKernel theta a = 0 := by
  rw [integral_bornKernel]
  simp only [centeredBasis, centeredLookup_sum _ (basisProbability_sum _ _), smul_zero,
    Finset.sum_const_zero]

theorem centeredBasis_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (theta : PhysicalParameter (d+1))
    (v : (ℕ × Action d) → Setting d → Fin (d+1) → E)
    (C : ℝ) (hb : ∀ a b k, ‖v a b k‖ ≤ C) (a : ℕ × Action d)
    (o : PVMGeneralExploration.Outcome d) : ‖centeredBasis theta v a o‖ ≤ 2*C :=
  centeredLookup_norm_bound _ (basisProbability_nonnegative _ _) (basisProbability_sum _ _)
    _ C (hb a o.1) o.2

def scoreResponse (truth : PureVector d) (a : ℕ × Action d)
    (o : PVMGeneralExploration.Outcome d) : HermitianSpace (d+1) :=
  centeredBasis (pureParameter d truth) (fun a b k =>
    (denominator (floor d) (basisProbability (pureParameter d truth) (settingBasis a.2 b) k))⁻¹ •
      basisEffect (settingBasis a.2 b) k) a o

theorem scoreResponse_mean (truth : PureVector d) (a : ℕ × Action d) :
    ∫ o, scoreResponse truth a o ∂bornKernel (pureParameter d truth) a = 0 :=
  centeredBasis_mean _ _ a

theorem scoreResponse_bound (truth : PureVector d) (a : ℕ × Action d)
    (o : PVMGeneralExploration.Outcome d) :
    ‖scoreResponse truth a o‖ ≤ 2*((floor d)⁻¹ * basisBound d) := by
  apply centeredBasis_bound
  intro a b k
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (denominator_pos (floor_pos d) _).le)]
  exact mul_le_mul (inv_anti₀ (floor_pos d) (le_max_right _ _)) (basisEffect_bound _ _)
    (norm_nonneg _) (inv_nonneg.mpr (floor_pos d).le)

def scoreSum (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  ∑ k ∈ Finset.range n, actualVectorResponse (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
    (scoreResponse truth) k path

theorem scoreSum_rootTight (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
      (pureParameter d truth))
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • scoreSum truth batchSize (n+1) path) atTop := by
  apply actualResponse_rootTight_normed _ _ _ (scoreResponse_mean truth)
    (2*((floor d)⁻¹*basisBound d)) _ (scoreResponse_bound truth)
  have hb := basisBound_nonnegative d
  have hf := floor_pos d
  positivity

def explorationCountResponse (truth : PureVector d)
    (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1))
    (a : ℕ × Action d) (o : PVMGeneralExploration.Outcome d) : ℝ := by
  classical
  exact centeredBasis (pureParameter d truth)
    (fun _ b y => if b = Sum.inr l ∧ y = k then (1:ℝ) else 0) a o

theorem explorationCountResponse_eq (truth : PureVector d)
    (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1))
    (a : ℕ × Action d) (o : PVMGeneralExploration.Outcome d) :
    explorationCountResponse truth l k a o =
      if o.1 = Sum.inr l then
        (if o.2=k then 1 else 0)-basisProbability (pureParameter d truth)
          (PVMGeneralGeometry.explorationBasis l) k else 0 := by
  classical
  unfold explorationCountResponse centeredBasis centeredLookup
  by_cases hb : o.1 = Sum.inr l
  · simp [hb, settingBasis, eq_comm]
  · simp [hb]

theorem explorationCountResponse_bound (truth : PureVector d)
    (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1))
    (a : ℕ × Action d) (o : PVMGeneralExploration.Outcome d) :
    ‖explorationCountResponse truth l k a o‖ ≤ 2 := by
  classical
  have hb : ∀ (a : ℕ × Action d) (b : Setting d) (y : Fin (d+1)),
      ‖(if b = Sum.inr l ∧ y=k then (1:ℝ) else 0)‖ ≤ 1 := by
    intro a b y
    split_ifs <;> norm_num
  simpa only [explorationCountResponse, mul_one] using
    centeredBasis_bound (pureParameter d truth) _ 1 hb a o

def explorationCount (truth : PureVector d) (batchSize : ℕ → ℕ)
    (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1))
    (n : ℕ) (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) : ℝ :=
  ∑ t ∈ Finset.range n, actualVectorResponse (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
    (explorationCountResponse truth l k) t path

theorem explorationCount_rootTight (truth : PureVector d) (batchSize : ℕ → ℕ)
    (l : PVMGeneralGeometry.ExplorationIndex d) (k : Fin (d+1)) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
      (pureParameter d truth))
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * explorationCount truth batchSize l k (n+1) path)
      atTop := by
  exact actualResponse_rootTight_normed _ _ _ (centeredBasis_mean _ _)
    2 (by norm_num) (explorationCountResponse_bound truth l k)

theorem score_eq_sum (truth : PureVector d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) (n : ℕ) :
    score (recordFeature (actualRecords batchSize path n))
      (fun r => (denominator (floor d) (fittedProbability truth (actualRecords batchSize path n) r))⁻¹)
      (fun r => observedIndicator (actualRecords batchSize path n) r -
        fittedProbability truth (actualRecords batchSize path n) r) =
      scoreSum truth batchSize n path := by
  classical
  rw [scoreSum, ← Fin.sum_univ_eq_sum_range]
  simp only [score, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  change _ = scoreResponse truth
    (t,(PVMGeneralAdaptive.actualState d batchSize path t).action) (path t)
  rw [scoreResponse, centeredBasis, centeredLookup_eq_residual_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [recordFeature_eq]
  simp only [fittedProbability, recordFeature_eq]
  simp only [observedIndicator, actualRecords, smul_smul, basisProbability]
  congr 1
  ring

end
end QubitOracle.AdaptiveDesign.PVMGeneralGLS

-/
