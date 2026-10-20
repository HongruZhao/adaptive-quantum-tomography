-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralResponse
import QubitOracle.AdaptiveDesign.PVMGeneralMeasurability

/-! Exploration outcomes may have zero probability forever. Grouping the
finite fixed library controls their fitted-weight error without pretending
that clipping disappears, and without splitting the data. -/
namespace QubitOracle.AdaptiveDesign.PVMGeneralGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController TangentGLS
open P2Adaptive PVMGeometry Filter MeasureTheory ProbabilityTheory
open ProbabilityCalculus BoundedResponseQuarterRate
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMExplorationSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem preliminaryError_inMeasure (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
      (pureParameter d truth)) (actualPreliminaryError batchSize truth) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (actualStatistic_stronglyMeasurable batchSize n (fun raw _ =>
      (pureParameter d (nearestVector d (toMatrix raw))).val-(pureParameter d truth).val)).aestronglyMeasurable
  · exact actualPreliminaryError_consistent batchSize truth

section FixedFeatures
variable {Ω R E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype R] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Same-data inverse weights on any fixed finite family. No independence
between the fitted state and the centered counts is needed. -/
theorem fixed_weight_sum_negligible
    (f : R → E) (truth : E) (fit : ℕ → Ω → E) (count : R → ℕ → Ω → ℝ)
    (floor : ℝ) (hf : 0 < floor)
    (he : TendstoInMeasure μ (fun n ω => fit n ω-truth) atTop (fun _ => 0))
    (hm : ∀ r, TightNorm μ (count r) atTop) :
    TendstoInMeasure μ (fun n ω => ∑ r,
      ((denominator floor ⟪f r,fit n ω⟫_ℝ)⁻¹-
       (denominator floor ⟪f r,truth⟫_ℝ)⁻¹) • (count r n ω • f r))
      atTop (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.finite_sum Finset.univ
  intro r _
  let C := ‖f r‖^2/floor^2+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcount : TightNorm μ (fun n ω => C * count r n ω) atTop := by
    apply tight_dominated (hm r) C hC
    intro n ω
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hC]
  apply product_bound_zero he hcount
  intro n ω
  have hw := protected_inverse_lipschitz floor ⟪f r,truth⟫_ℝ ⟪f r,fit n ω⟫_ℝ hf
  rw [← inner_sub_right] at hw
  have hi' := norm_inner_le_norm (𝕜:=ℝ) (f r) (fit n ω-truth)
  rw [Real.norm_eq_abs] at hi'
  have hcoeff : |(denominator floor ⟪f r,fit n ω⟫_ℝ)⁻¹-
      (denominator floor ⟪f r,truth⟫_ℝ)⁻¹| ≤ ‖f r‖ *‖fit n ω-truth‖/floor^2 :=
    hw.trans (div_le_div_of_nonneg_right hi' (sq_nonneg floor))
  simp only [norm_smul, Real.norm_eq_abs, norm_mul, abs_of_pos hC]
  calc
    _ ≤ (‖f r‖ *‖fit n ω-truth‖/floor^2)*(|count r n ω| *‖f r‖) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    _ ≤ ‖fit n ω-truth‖ *(C*|count r n ω|) := by
      dsimp [C]
      calc
        _ = ‖fit n ω-truth‖ * ((‖f r‖^2/floor^2)*|count r n ω|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith : ‖f r‖^2/floor^2 ≤ ‖f r‖^2/floor^2+1)
            (abs_nonneg _)) (norm_nonneg _)

end FixedFeatures

def explorationWeightError (truth : PureVector d) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  ∑ r : PVMGeneralGeometry.ExplorationIndex d × Fin (d+1),
    ((denominator (floor d) (basisProbability
        (pureParameter d (actualPreliminary batchSize path (n+1)))
        (PVMGeneralGeometry.explorationBasis r.1) r.2))⁻¹-
      (denominator (floor d) (basisProbability (pureParameter d truth)
        (PVMGeneralGeometry.explorationBasis r.1) r.2))⁻¹) •
    (((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * explorationCount truth batchSize r.1 r.2 (n+1) path) •
      basisEffect (PVMGeneralGeometry.explorationBasis r.1) r.2)

theorem explorationWeightError_zero (truth : PureVector d) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMGeneralAdaptive.adaptiveProtocol d batchSize)
      (pureParameter d truth)) (explorationWeightError truth batchSize) atTop (fun _ => 0) := by
  exact fixed_weight_sum_negligible
    (fun r : PVMGeneralGeometry.ExplorationIndex d × Fin (d+1) =>
      basisEffect (PVMGeneralGeometry.explorationBasis r.1) r.2)
    (pureParameter d truth).val
    (fun n path => (pureParameter d (actualPreliminary batchSize path (n+1))).val)
    (fun r n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ *
      explorationCount truth batchSize r.1 r.2 (n+1) path)
    (floor d) (floor_pos d)
    ((preliminaryError_inMeasure truth batchSize).comp (tendsto_add_atTop_nat 1))
    (fun r => explorationCount_rootTight truth batchSize r.1 r.2)

end
end QubitOracle.AdaptiveDesign.PVMGeneralGLS

-/
