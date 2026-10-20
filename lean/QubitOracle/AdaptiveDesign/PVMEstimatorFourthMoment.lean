-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGoodErrorBound
import QubitOracle.AdaptiveDesign.PVMGramFailureRate
import QubitOracle.AdaptiveDesign.PVMPilotHigherMoments
import QubitOracle.AdaptiveDesign.GoodEventMoments

/-! Fourth moments for the actual physical PVM estimator. The only
extra hypotheses are the stated deterministic exploration and batch budgets. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityTheory PVMPilotAdaptive PVMPilotSchedule PVMGeometry
open AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem score_uniformMoment (truth : PureVector d) (b : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth))
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • scoreSum truth b (n+1) path) p := by
  exact actualVectorResponse_uniformMoment _ _ (scoreResponse truth) (scoreResponse_mean truth)
    (2*((floor d)⁻¹*basisBound d)) (by have h := basisBound_nonnegative d; dsimp [floor]; positivity)
    (scoreResponse_bound truth) p

theorem pilot_quadratic_fourthMoment (truth : PureVector d) (b : ℕ → ℕ) (hbudget : OneStepBudget) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ)*‖actualPreliminaryError b truth (n+1) path‖^2) 4 := by
  obtain ⟨K,hK⟩ := hbudget.bddAbove_range
  let C := max K 0
  have hC : 0 ≤ C := le_max_right _ _
  have hs (n : ℕ) : Real.sqrt ((n+1:ℕ):ℝ) ≤ C*mass (n+1) := by
    have hh := hK (Set.mem_range_self n)
    have hh' : Real.sqrt ((n:ℝ)+1)/mass n ≤ C := hh.trans (le_max_left _ _)
    have hx := (div_le_iff₀ (mass_pos n)).mp hh'
    simpa only [Nat.cast_add,Nat.cast_one] using hx.trans
      (mul_le_mul_of_nonneg_left (mass_mono (Nat.le_succ n)) hC)
  apply (PVMPilotHigherMoments.preliminary b truth 8).norm_sq_of_eight.of_dominated _
    (fun n => (actualStatistic_stronglyMeasurable b (n+1) (fun raw _ =>
      Real.sqrt ((n+1:ℕ):ℝ)*‖(pureParameter d (nearestVector d (toMatrix raw))).val-
        (pureParameter d truth).val‖^2)).aestronglyMeasurable) C hC
  intro n path
  simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),norm_pow,norm_norm,
    norm_smul,mul_pow,sq_abs,Real.sq_sqrt (mass_pos _).le,abs_of_pos (mass_pos _)]
  change Real.sqrt ((n+1:ℕ):ℝ)*‖actualPreliminaryError b truth (n+1) path‖^2 ≤
    C*(mass (n+1)*‖actualPreliminaryError b truth (n+1) path‖^2)
  nlinarith only [mul_le_mul_of_nonneg_right (hs n) (sq_nonneg ‖actualPreliminaryError b truth (n+1) path‖)]

theorem corrected_fourthMoment (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (hbudget : OneStepBudget) (hb : BatchMomentCondition b) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth))
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) • projectorError truth ridge hr b (n+1) path) 4 := by
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth)
  obtain ⟨δ,κ,hδ,hκ,T,hrare,hgood⟩ := good_gram_with_rare_failure truth b hp hb
  obtain ⟨C,hC,herror⟩ := corrected_error_of_coercive truth ridge hr κ hκ
  let X := fun n path => C*(‖(Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • scoreSum truth b (n+1) path‖+
    Real.sqrt ((n+1:ℕ):ℝ)*‖actualPreliminaryError b truth (n+1) path‖^2+1)
  have hXm : UniformMoment μ X 4 :=
    (((score_uniformMoment truth b 4).norm.add (pilot_quadratic_fourthMoment truth b hbudget)).add
      (uniformMoment_of_bound (fun _ (_ : AdaptiveInfinitePath (PVMOutcome d)) => (1:ℝ))
        (fun _ => aestronglyMeasurable_const) 1 (by norm_num) (fun _ _ => by norm_num) 4)).const_mul C
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun path => Real.sqrt ((n+1:ℕ):ℝ) • projectorError truth ridge hr b (n+1) path) μ :=
    (actualStatistic_stronglyMeasurable b (n+1) (fun raw data => Real.sqrt ((n+1:ℕ):ℝ) •
      ((pureParameter d (estimateFromRaw raw data (floor d) ridge (floor_pos d) hr)).val-
        (pureParameter d truth).val))).aestronglyMeasurable
  apply fourthMoment_of_good_event _ X hXm (fun _ _ => by dsimp [X]; positivity) hm
    (fun n => gramFailure truth b δ T (n+1)) (fun n => 2*Real.sqrt ((n+1:ℕ):ℝ)) (fun _ => by positivity)
  · intro n path
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have he := preliminaryError_norm_le_two (actualEstimate ridge hr b path (n+1)) truth
    calc
      _ ≤ Real.sqrt ((n+1:ℕ):ℝ)*2 := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
      _ = _ := by ring
  · intro n path hx
    have hg := hgood ridge hr.le (n+1) path hx
    have he := herror b (n+1) (by omega) path hg
    have hn : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hs : 0 < Real.sqrt ((n+1:ℕ):ℝ) := Real.sqrt_pos.mpr hn
    have hsq := Real.sq_sqrt hn.le
    have hi : (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ ≤ 1 := by
      apply (inv_le_one₀ hs).mpr
      rw [Real.le_sqrt (by norm_num) hn.le]
      norm_num
    have hid : Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ) = (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ := by
      field_simp
      exact hsq
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.le]
    apply (mul_le_mul_of_nonneg_left he hs.le).trans
    dsimp only [X]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
    have heq : Real.sqrt ((n+1:ℕ):ℝ)*(C*(‖scoreSum truth b (n+1) path‖/((n+1:ℕ):ℝ)+
        ‖actualPreliminaryError b truth (n+1) path‖^2+1/((n+1:ℕ):ℝ))) =
        C*((Real.sqrt ((n+1:ℕ):ℝ))⁻¹*‖scoreSum truth b (n+1) path‖+
          Real.sqrt ((n+1:ℕ):ℝ)*‖actualPreliminaryError b truth (n+1) path‖^2+
            (Real.sqrt ((n+1:ℕ):ℝ))⁻¹) := by
      calc
        _ = C*((Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ))*‖scoreSum truth b (n+1) path‖+
          Real.sqrt ((n+1:ℕ):ℝ)*‖actualPreliminaryError b truth (n+1) path‖^2+
            Real.sqrt ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ)) := by ring
        _ = _ := by rw [hid]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith only [hi]) hC.le
  · obtain ⟨K,hK⟩ := (hrare 2).bddAbove_range
    refine ⟨16*max K 0,by positivity,fun n => ?_⟩
    have hh := (hK (Set.mem_range_self n)).trans (le_max_left K 0)
    have hs : (2*Real.sqrt ((n+1:ℕ):ℝ))^4 = 16*((n+1:ℕ):ℝ)^2 := by
      have hsq := Real.sq_sqrt (show (0:ℝ) ≤ ((n+1:ℕ):ℝ) by positivity)
      nlinarith [sq_nonneg (Real.sqrt ((n+1:ℕ):ℝ))]
    rw [hs]
    nlinarith only [hh]

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
