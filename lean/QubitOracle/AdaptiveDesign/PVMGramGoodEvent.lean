-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGramConcentration
import QubitOracle.AdaptiveDesign.PVMCorrectionAlgebra

/-! Pathwise coercivity of the implemented correction, derived from
alignment of the held controllers and a bounded Gram fluctuation. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMPilotAdaptive PVMPilotSchedule
open Filter MeasureTheory ProbabilityTheory SequentialRidgeController
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem realizedGram_bound (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖realizedGram batchSize n path‖ ≤ (n:ℝ)*gramBound d := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, gramBound d := Finset.sum_le_sum (fun _ _ => basisGramOperator_bound _)
    _ = _ := by simp

theorem last_half_mean_bound (truth : PureVector d) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) (α : ℝ) (hα : 0 ≤ α)
    (hl : ∀ k ∈ Finset.Ico (n/2) n, ∀ A : tangentSpace truth,
      α*‖A‖^2 ≤ ⟪A.val,meanGram (k,(PVMPilotAdaptive.actualState d batchSize path k).action) A.val⟫_ℝ)
    (A : tangentSpace truth) :
    (α/2)*(n:ℝ)*‖A‖^2 ≤ ⟪A.val,conditionalGramSum batchSize n path A.val⟫_ℝ := by
  rw [conditionalGramSum,ContinuousLinearMap.sum_apply,inner_sum]
  have hc : (n:ℝ) ≤ 2*((n-n/2:ℕ):ℝ) := by exact_mod_cast (show n ≤ 2*(n-n/2) by omega)
  calc
    _ ≤ ((n-n/2:ℕ):ℝ)*(α*‖A‖^2) := by
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hα (sq_nonneg ‖A‖))
      nlinarith only [hh]
    _ = ∑ _k ∈ Finset.Ico (n/2) n, α*‖A‖^2 := by simp
    _ ≤ ∑ k ∈ Finset.Ico (n/2) n,
        ⟪A.val,meanGram (k,(PVMPilotAdaptive.actualState d batchSize path k).action) A.val⟫_ℝ :=
      Finset.sum_le_sum (fun k hk => hl k hk A)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
      · intro k _ _
        exact meanGram_nonnegative _ A.val

theorem actual_normal_quadratic (ridge : ℝ) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d))
    (A : tangentSpace (actualPreliminary batchSize path n)) :
    ⟪A,normalMap (tangentFeature (actualPreliminary batchSize path n) (actualRecords batchSize path n))
      (fun _ => 1) ridge A⟫_ℝ = ridge*‖A‖^2+⟪A.val,realizedGram batchSize n path A.val⟫_ℝ := by
  change ⟪A.val,(normalMap _ _ ridge A).val⟫_ℝ = _
  rw [← recordOperator_tangent,recordOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,inner_add_right,inner_smul_right,tangentProjector_self,
    real_inner_self_eq_norm_sq,recordInformation_eq_realized,compress_tangent_inner]
  rfl

theorem good_gram_parameters (truth : PureVector d) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∃ T : ℕ, ∀ (batchSize : ℕ → ℕ) (ridge : ℝ), 0 ≤ ridge →
      ∀ (n : ℕ), T ≤ n → ∀ path : AdaptiveInfinitePath (PVMOutcome d),
      path ∉ lateAlignmentFailure truth batchSize δ n →
      ‖actualPreliminaryError batchSize truth n path‖ < δ →
      ‖realizedGram batchSize n path-conditionalGramSum batchSize n path‖ < δ*(n:ℝ) →
      CoerciveLeastSquares.Coercive
        (normalMap (tangentFeature (actualPreliminary batchSize path n) (actualRecords batchSize path n))
          (fun _ => 1) ridge) (κ*(n:ℝ)) := by
  obtain ⟨δ0,hδ0,hlocal⟩ := local_meanGram_coercive truth
  let α := 1/(4*(d+1:ℝ))
  let κ0 := α/4
  have hα : 0 < α := by dsimp [α]; positivity
  have hκ0 : 0 < κ0 := by dsimp [κ0]; positivity
  let δ := min δ0 (min (1/12) (min (κ0/(96*(gramBound d+1))) κ0))
  have hδ : 0 < δ := by
    dsimp [δ]
    have hG := gramBound_nonnegative d
    positivity
  have hδ0' : δ ≤ δ0 := min_le_left _ _
  have hs1 : δ ≤ 1/12 := (min_le_right _ _).trans (min_le_left _ _)
  have hs2 : δ ≤ κ0/(96*(gramBound d+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : δ ≤ κ0 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (epsilon_tendsto_zero.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨δ,κ0/8,hδ,by positivity,2*T,fun batchSize ridge hr n hn path halign hfit hnoise A => ?_⟩
  have hl (k : ℕ) (hk : k ∈ Finset.Ico (n/2) n) (B : tangentSpace truth) :
      α*‖B‖^2 ≤ ⟪B.val,meanGram (k,(PVMPilotAdaptive.actualState d batchSize path k).action) B.val⟫_ℝ := by
    have hgood : ‖actualPreliminaryError batchSize truth (lastRefresh (batchRefresh batchSize) k) path‖ < δ := by
      by_contra hh
      apply halign
      exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,le_of_not_gt hh⟩⟩
    apply hlocal (PVMPilotAdaptive.actualState d batchSize path k).action k _ (hT k (by
      have hh := (Finset.mem_Ico.mp hk).1; omega)) B
    change ‖frameParameter (measurementFrame d batchSize path k)-(pureParameter d truth).val‖ < δ0
    rw [frameParameter_frozen]
    exact lt_of_lt_of_le hgood hδ0'
  have hmean := last_half_mean_bound truth batchSize n path α hα.le hl
  have htrue (B : tangentSpace truth) : κ0*(n:ℝ)*‖B‖^2 ≤ ⟪B.val,realizedGram batchSize n path B.val⟫_ℝ := by
    have hq := quadratic_opNorm_bound (realizedGram batchSize n path-conditionalGramSum batchSize n path) B.val
    have hbound : ‖realizedGram batchSize n path-conditionalGramSum batchSize n path‖ ≤ κ0*(n:ℝ) :=
      hnoise.le.trans (mul_le_mul_of_nonneg_right hs3 (Nat.cast_nonneg n))
    have hq' := hq.trans (mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖B.val‖))
    rw [ContinuousLinearMap.sub_apply,inner_sub_right] at hq'
    have hh := neg_le_of_abs_le hq'
    have hm := hmean B
    change - (κ0*(n:ℝ)*‖B‖^2) ≤ _ at hh
    dsimp [κ0]
    dsimp [κ0] at hh
    change α/2*(n:ℝ)*‖B.val‖^2 ≤ _ at hm
    nlinarith only [hh,hm]
  have hsmall : 96*gramBound d*δ ≤ κ0 := by
    have hg := gramBound_nonnegative d
    have hh := (le_div_iff₀ (show 0 < 96*(gramBound d+1) by positivity)).mp hs2
    nlinarith
  have hc := nearby_tangent_coercivity (actualPreliminary batchSize path n) truth
    (realizedGram batchSize n path) (n:ℝ) (gramBound d) κ0 δ (Nat.cast_nonneg n)
    (gramBound_nonnegative d) hκ0 hδ.le hs1 hsmall hfit.le
    (realizedGram_bound batchSize n path) htrue A
  rw [actual_normal_quadratic]
  exact hc.trans (le_add_of_nonneg_left (mul_nonneg hr (sq_nonneg ‖A‖)))

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
