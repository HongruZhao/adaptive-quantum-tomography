-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGramGoodEvent
import QubitOracle.AdaptiveDesign.ExplorationRareEventRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exceptional histories have negligible polynomially weighted
probability under the paper's deterministic batch condition. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityTheory PVMPilotAdaptive PVMPilotSchedule SequentialRidgeController
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def gramFailure (truth : PureVector d) (b : ℕ → ℕ) (δ : ℝ) (T n : ℕ) :
    Set (AdaptiveInfinitePath (PVMOutcome d)) :=
  if n < T then Set.univ else
    (lateAlignmentFailure truth b δ n ∪ {path | δ ≤ ‖actualPreliminaryError b truth n path‖}) ∪
      {path | δ*(n:ℝ) ≤ ‖realizedGram b n path-conditionalGramSum b n path‖}

theorem gramFailure_rate (truth : PureVector d) (b : ℕ → ℕ)
    (hp : ∀ j, 0 < b j) (hb : BatchMomentCondition b)
    (δ : ℝ) (hδ : 0 < δ) (T p : ℕ) :
    Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)^p *
      (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth)).real
        (gramFailure truth b δ T (n+1))) atTop (𝓝 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth)
  obtain ⟨B,c,hB,hc,ha⟩ := late_alignment_concentration truth b δ hδ
  obtain ⟨B',c',hB',hc',hg⟩ := gram_deviation_concentration truth b δ hδ
  have h1 := ((ExplorationRareEventRate.held_polynomial_exp b hp hb c hc (p+1)).const_mul B).comp
    (tendsto_add_atTop_nat 1)
  have hnat : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p:ℝ) c' hc').comp hnat).const_mul B'
  simp only [mul_zero] at h1 h2
  simp only [Real.rpow_natCast] at h2
  have ht := h1.add h2
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ ht
  filter_upwards [eventually_ge_atTop T] with n hn
  have he : ¬ n+1 < T := by omega
  have hh : μ.real (gramFailure truth b δ T (n+1)) ≤
      (((n+1:ℕ):ℝ)+1)*B*Real.exp (-c*mass (lastRefresh (batchRefresh b) ((n+1)/2)))+
        B'*Real.exp (-c'*((n+1:ℕ):ℝ)) := by
    rw [gramFailure,if_neg he]
    exact (measureReal_union_le _ _).trans (add_le_add (ha (n+1)) (hg n))
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  have hx : ((n+1:ℕ):ℝ)^p ≤ (((n+1:ℕ):ℝ)+1)^p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have hhx := mul_le_mul_of_nonneg_right hx (show 0 ≤
    (((n+1:ℕ):ℝ)+1)*B*Real.exp (-c*mass (lastRefresh (batchRefresh b) ((n+1)/2))) by positivity)
  dsimp only [Function.comp_def]
  rw [pow_succ]
  nlinarith only [hhx]

theorem good_gram_with_rare_failure (truth : PureVector d) (b : ℕ → ℕ)
    (hp : ∀ j, 0 < b j) (hb : BatchMomentCondition b) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∃ T : ℕ,
      (∀ p : ℕ, Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)^p *
        (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d b) (pureParameter d truth)).real
          (gramFailure truth b δ T (n+1))) atTop (𝓝 0)) ∧
      ∀ (ridge : ℝ), 0 ≤ ridge → ∀ (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)),
        path ∉ gramFailure truth b δ T n →
        CoerciveLeastSquares.Coercive (normalMap
          (tangentFeature (actualPreliminary b path n) (actualRecords b path n)) (fun _ => 1) ridge)
          (κ*(n:ℝ)) := by
  obtain ⟨δ,κ,hδ,hκ,T,hgood⟩ := good_gram_parameters truth
  refine ⟨δ,κ,hδ,hκ,T,fun p => gramFailure_rate truth b hp hb δ hδ T p,
    fun ridge hr n path hx => ?_⟩
  have hn : T ≤ n := by
    by_contra hh
    exact hx (by simp [gramFailure,show n<T by omega])
  rw [gramFailure,if_neg (by omega)] at hx
  have hs := not_or.mp hx
  have hs' := not_or.mp hs.1
  exact hgood b ridge hr n hn path hs'.1 (lt_of_not_ge hs'.2) (lt_of_not_ge hs.2)

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
