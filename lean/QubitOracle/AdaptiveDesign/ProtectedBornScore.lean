import QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments
import QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT
import QubitOracle.AdaptiveDesign.FiniteAdaptiveResponseCLT
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.CompactLimitTransfer
import QubitOracle.Paper.FiniteKernelPathSpace
import QubitOracle.Paper.MartingaleCLT
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.RankOneStageContinuity
import QubitOracle.TwoBasis
/-!
# Protected, centered Born score used in the efficiency proof

This score is evaluated at the fixed true state only for analysis. It is not
an input to the estimator. Protection makes it bounded for every apparatus
rotation, including the finitely many early irregular measurements.
-/

namespace QubitOracle.AdaptiveDesign.ProtectedBornScore

open QubitOracle QubitOracle.Paper GeneralPOVM PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {d : ℕ} {O : Type} [Fintype O]

def gradientVector (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) : EuclideanSpace ℝ (TangentIndex d) :=
  WithLp.toLp 2 (gradient P U o)

def rawScore (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) : EuclideanSpace ℝ (TangentIndex d) :=
  (max (mass P U o) floor)⁻¹ • gradientVector P U o

def scoreMean (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : EuclideanSpace ℝ (TangentIndex d) :=
  ∑ o, mass P U o • rawScore P floor U o

def score (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) : EuclideanSpace ℝ (TangentIndex d) :=
  rawScore P floor U o - scoreMean P floor U

def moment (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ)
    (u : EuclideanSpace ℝ (TangentIndex d))
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : ℝ :=
  ∑ o, mass P U o * ⟪u, score P floor U o⟫_ℝ ^ 2

theorem mass_sum (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) : ∑ o, mass P U o = 1 := by
  have he := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (A 0 0).re)
    (effect_complete P U hU)
  simpa [mass, Matrix.sum_apply] using he

theorem gradient_sum (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) : ∑ o, gradientVector P U o = 0 := by
  ext x
  rcases x with j | j
  · have he := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (A 0 j.succ).re)
      (effect_complete P U hU)
    simpa [gradientVector, GeneralPOVM.gradient, Matrix.sum_apply, Matrix.one_apply,
      (Fin.succ_ne_zero j).symm] using he
  · have he := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => -(A 0 j.succ).im)
      (effect_complete P U hU)
    simpa [gradientVector, GeneralPOVM.gradient, Matrix.sum_apply, Matrix.one_apply,
      (Fin.succ_ne_zero j).symm] using he

theorem score_centered (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) :
    ∑ o, mass P U o • score P floor U o = 0 := by
  simp only [score, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, mass_sum P U hU,
    one_smul]
  exact sub_self _

theorem gradientVector_continuous (P : FinitePOVM (Fin (d+1)) O) (o : O) :
    Continuous (fun U => gradientVector P U o) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun x => gradient_continuous P o x))

theorem rawScore_continuous (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor) (o : O) : Continuous (fun U => rawScore P floor U o) := by
  unfold rawScore
  have hi : Continuous (fun U => (max (mass P U o) floor)⁻¹) :=
    ((mass_continuous P o).max continuous_const).inv₀
      (fun U => (hf.trans_le (le_max_right (mass P U o) floor)).ne')
  exact hi.smul (gradientVector_continuous P o)

theorem score_continuous (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor) (o : O) : Continuous (fun U => score P floor U o) := by
  apply (rawScore_continuous P floor hf o).sub
  exact continuous_finset_sum _ (fun y _ => (mass_continuous P y).smul (rawScore_continuous P floor hf y))

theorem moment_continuous (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor) (u : EuclideanSpace ℝ (TangentIndex d)) :
    Continuous (moment P floor u) := by
  exact continuous_finset_sum _ (fun o _ => (mass_continuous P o).mul
    ((continuous_const.inner (score_continuous P floor hf o)).pow 2))

theorem score_uniformly_bounded (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ → ∀ o, ‖score P floor U o‖ ≤ C := by
  have h (o : O) : ∃ C : ℝ, ∀ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ → ‖score P floor U o‖ ≤ C :=
    isCompact_unitaryMatrices.exists_bound_of_continuousOn
      (score_continuous P floor hf o).continuousOn
  choose B hB using h
  refine ⟨∑ o, |B o|, Finset.sum_nonneg (fun o _ => abs_nonneg _), ?_⟩
  intro U hU o
  exact (hB o U hU).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun y _ => abs_nonneg (B y)) (Finset.mem_univ o)))

theorem scoreMean_zero_of_regular (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hp : ∀ o, floor ≤ mass P U o) : scoreMean P floor U = 0 := by
  have he (o : O) : mass P U o • rawScore P floor U o = gradientVector P U o := by
    rw [rawScore, max_eq_left (hp o), smul_smul,
      mul_inv_cancel₀ (hf.trans_le (hp o)).ne', one_smul]
  simp_rw [scoreMean, he]
  exact gradient_sum P U hU

theorem score_eq_unprotected (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hp : ∀ o, floor ≤ mass P U o) (o : O) :
    score P floor U o = (mass P U o)⁻¹ • gradientVector P U o := by
  rw [score, scoreMean_zero_of_regular P floor hf U hU hp, sub_zero, rawScore, max_eq_left (hp o)]

theorem weightedGram_quadratic {I O : Type} [Fintype I] [Fintype O]
    (p : O → ℝ) (g : O → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I) :
    martingaleScoreQuadraticForm (fun i j => ∑ o, (p o)⁻¹ * (g o i * g o j)) u =
      ∑ o, (p o)⁻¹ * ⟪u, g o⟫_ℝ ^ 2 := by
  classical
  have he : (fun i j => ∑ o, (p o)⁻¹ * (g o i * g o j)) =
      weightedGram p (fun o i => g o i) := by
    ext i j
    simp only [weightedGram, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [he]
  simp only [martingaleScoreQuadraticForm, weightedGram, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.vecMulVec_mulVec,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, pow_two]
  apply Finset.sum_congr rfl
  intro o _
  change (p o)⁻¹ *
    (((fun i => u i) ⬝ᵥ (fun i => g o i)) * ((fun i => g o i) ⬝ᵥ (fun i => u i))) = _
  rw [dotProduct_comm (fun i => u i) (fun i => g o i)]

theorem moment_eq_fisher (P : FinitePOVM (Fin (d+1)) O)
    (floor : ℝ) (hf : 0 < floor) (u : EuclideanSpace ℝ (TangentIndex d))
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hp : ∀ o, floor ≤ mass P U o) :
    moment P floor u U = martingaleScoreQuadraticForm (fisher P U) u := by
  rw [show fisher P U = fun i j => ∑ o,
      (mass P U o)⁻¹ * (gradientVector P U o i * gradientVector P U o j) by
    funext i j; simp only [fisher, safeRatio_eq_div, gradientVector,
      div_eq_mul_inv, mul_comm]]
  rw [weightedGram_quadratic]
  apply Finset.sum_congr rfl
  intro o _
  rw [score_eq_unprotected P floor hf U hU hp, inner_smul_right]
  have hne := (hf.trans_le (hp o)).ne'
  field_simp

theorem moment_tendsto (P : FinitePOVM (Fin (d+1)) O) (hF : FisherSymmetric P)
    (floor : ℝ) (hf : 0 < floor) (hfloor : ∀ o, floor ≤ referenceProbability P o)
    (u : EuclideanSpace ℝ (TangentIndex d))
    (controller : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => controllerTrueOverlapSq (controller n)) atTop (𝓝 1)) :
    Tendsto (fun n => moment P floor u (controller n)) atTop
      (𝓝 (martingaleScoreQuadraticForm
        ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) u)) := by
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ}
    isCompact_unitaryMatrices controller hU
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h
    (moment P floor u) _ ?_
  intro U hU hoverlap
  refine ⟨(moment_continuous P floor hf u).continuousAt, ?_⟩
  rw [moment_eq_fisher P floor hf u U hU (fun o => by
    rw [mass_of_overlap_one P U hU hoverlap]; exact hfloor o),
    fisher_of_overlap_one P hF U hU hoverlap]

theorem referenceFloor_le [Nonempty O] (P : FinitePOVM (Fin (d+1)) O)
    (hp : Regular P) (o : O) : TangentGLS.referenceFloor P ≤ referenceProbability P o := by
  classical
  have hi : 0 < Finset.univ.inf' Finset.univ_nonempty (referenceProbability P) :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun y _ => hp y)
  have hb := Finset.inf'_le (s := Finset.univ) (f := referenceProbability P) (Finset.mem_univ o)
  unfold TangentGLS.referenceFloor
  linarith

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def response (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (floor : ℝ)
    (U : GlobalPFSICBorn.Action d) (o : O) : EuclideanSpace ℝ (TangentIndex d) :=
  score P floor ((trueFrame d truth).conjTranspose * U.matrix) o

theorem response_mean_zero (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (floor : ℝ)
    (U : GlobalPFSICBorn.Action d) : ∫ o, response P truth floor U o ∂bornKernel P truth U = 0 := by
  change (∫ o, response P truth floor U o ∂finiteMassMeasure
    (bornProbability P truth U) (bornProbability_nonnegative P truth U)
    (bornProbability_sum P truth U)) = _
  rw [integral_finiteMassMeasure]
  simp only [bornProbability_pure_eq_mass, response]
  exact score_centered P floor _
    (GlobalPFSIC.relative_unitary _ _ (trueFrame_unitary d truth) U.unitary)

theorem response_bounded (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (hf : 0 < floor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U o, ‖response P truth floor U o‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := score_uniformly_bounded P floor hf
  exact ⟨C, hC, fun U o => hb _
    (GlobalPFSIC.relative_unitary _ _ (trueFrame_unitary d truth) U.unitary) o⟩

theorem response_secondMoment (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (floor : ℝ)
    (U : GlobalPFSICBorn.Action d) (u : EuclideanSpace ℝ (TangentIndex d)) :
    (∫ o, ⟪u, response P truth floor U o⟫_ℝ ^ 2 ∂bornKernel P truth U) =
      moment P floor u ((trueFrame d truth).conjTranspose * U.matrix) := by
  change (∫ o, ⟪u, response P truth floor U o⟫_ℝ ^ 2 ∂finiteMassMeasure
    (bornProbability P truth U) (bornProbability_nonnegative P truth U)
    (bornProbability_sum P truth U)) = _
  rw [integral_finiteMassMeasure]
  simp only [bornProbability_pure_eq_mass, response, moment, smul_eq_mul]

theorem actual_secondMoment_limit
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hF : FisherSymmetric P)
    (truth : PureVector d) (floor : ℝ) (hf : 0 < floor)
    (hfloor : ∀ o, floor ≤ referenceProbability P o)
    (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (u : EuclideanSpace ℝ (TangentIndex d)) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun k => AdaptiveConditionalMoments.secondMoment
        (adaptiveProtocol P hI regularization hr batchSize) truth (response P truth floor) u
        ((adaptiveProtocol P hI regularization hr batchSize).design (k+1)
          (adaptiveInfinitePathPrefix (k+1) path))) atTop
        (𝓝 (martingaleScoreQuadraticForm
          ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) u)) := by
  filter_upwards [adaptive_consistency P hI regularization hr truth batchSize hpositive] with path hp
  have hproj : Tendsto (fun n => GlobalPFSIC.frameProjector
      (measurementFrame P hI regularization hr batchSize path n)) atTop
      (𝓝 (GlobalPFSIC.frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    exact hp.2.2
  have hrel := GlobalPFSIC.relative_overlap_tendsto (trueFrame d truth)
    (trueFrame_unitary d truth) (measurementFrame P hI regularization hr batchSize path) hproj
  have hm := moment_tendsto P hF floor hf hfloor u
    (fun n => (trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path n)
    (fun n => GlobalPFSIC.relative_unitary _ _ (trueFrame_unitary d truth)
      (measurementFrame_unitary P hI regularization hr batchSize path n)) hrel
  have heq (k : ℕ) : AdaptiveConditionalMoments.secondMoment
      (adaptiveProtocol P hI regularization hr batchSize) truth (response P truth floor) u
      ((adaptiveProtocol P hI regularization hr batchSize).design (k+1)
        (adaptiveInfinitePathPrefix (k+1) path)) =
      moment P floor u ((trueFrame d truth).conjTranspose *
        measurementFrame P hI regularization hr batchSize path (k+1)) := by
    exact response_secondMoment P truth floor _ u
  simp_rw [heq]
  exact hm.comp (tendsto_add_atTop_nat 1)

/-- CLT for the actual protected score. All model-specific centering,
boundedness, Lindeberg and conditional covariance limits have been proved.
The direct bounded-response CLT uses only Lean foundational axioms.
This is a score theorem, not yet the GLS-estimator remainder theorem. -/
theorem actual_score_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    (BoundedAdaptiveResponseCLT.problem (adaptiveProtocol P hI regularization hr batchSize) truth
      (response P truth (TangentGLS.referenceFloor P))).VectorSumConvergesToGaussian
        ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) := by
  obtain ⟨C, hC, hb⟩ := response_bounded P truth (TangentGLS.referenceFloor P)
    (TangentGLS.referenceFloor_pos P hp)
  have hM : ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (by norm_num)
  exact FiniteAdaptiveCharacteristic.vector_clt_of_secondMoment_limit _ _ _
    (response_mean_zero P truth _) C hC hb _ hM
    (actual_secondMoment_limit P hI hF truth _ (TangentGLS.referenceFloor_pos P hp)
      (referenceFloor_le P hp) regularization hr batchSize hpositive)

/-- The phase-pair seed requires C1, C2 and rank one, with no Fisher-identity
or covariance-convergence assumption supplied by the user. -/
theorem phasePair_actual_score_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    (BoundedAdaptiveResponseCLT.problem
      (adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
        regularization hr batchSize) truth
      (response (PhasePair.paired P) truth (TangentGLS.referenceFloor (PhasePair.paired P)))).VectorSumConvergesToGaussian
        ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) :=
  actual_score_clt (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization hr batchSize hpositive

end
end QubitOracle.AdaptiveDesign.ProtectedBornScore
