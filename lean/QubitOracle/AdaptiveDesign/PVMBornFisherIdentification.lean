-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMAdaptiveTheorem
import QubitOracle.AdaptiveDesign.P2BornFisherIdentification

/-! Probabilities and derivatives identify the limiting matrix with the Fisher
information of the actual randomized PVM setting/outcome experiment. -/
namespace QubitOracle.AdaptiveDesign.PVMAdaptive
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry PVMExploration PureMatrixController ExplorationRidge
open P2Adaptive (pureParameter trueFrame trueFrame_projector)
open MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000

def relativeBasis {d : ℕ} (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (U : Action d) (b : Setting d) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  T.conjTranspose * (settingBasis U b).matrix

def labChartProbability {d : ℕ} (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (a : ℕ × Action d) (o : PVMOutcome d) (x : TangentIndex d) (t : ℝ) : ℝ :=
  settingWeight d a.1 o.1 *
    (Matrix.trace (rankOneDensity (T.mulVec (directionalState x t)) *
      toMatrix (PVMExploration.responseVector a.2 o))).re

lemma labChartProbability_eq_generic {d : ℕ} (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (a : ℕ × Action d) (o : PVMOutcome d) (x : TangentIndex d) (t : ℝ) :
    labChartProbability T a o x t = genericBornProbability (settingWeight d a.1 o.1)
      (fun i => relativeBasis T a.2 o.1 i o.2) x t := by
  unfold labChartProbability
  rw [PVMExploration.responseVector, basisEffect_matrix]
  have h := basisBornProbability_eq_trace_rankOneDensity_mul_projector
    (fun i => (settingBasis a.2 o.1).matrix i o.2) (T.mulVec (directionalState x t))
  change (basisBornProbability _ _ : ℂ) = Matrix.trace (rankOneDensity _ * projector _) at h
  rw [← h]
  simp only [Complex.ofReal_re, basisBornProbability, P2Adaptive.basisBornAmplitude_transport]
  rfl

lemma genericGradient_eq_basisGradient {d : ℕ} (c : ℝ)
    (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (k : Fin (d+1)) (x : TangentIndex d) :
    genericEffectGradient c (fun i => B i k) x = c * fixedChartBasisGradient B k x := by
  cases x <;> simp [genericEffectGradient, fixedChartBasisGradient, projector_apply,
    Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

lemma labChartProbability_hasDerivAt {d : ℕ} (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (a : ℕ × Action d) (o : PVMOutcome d) (x : TangentIndex d) :
    HasDerivAt (labChartProbability T a o x)
      (settingWeight d a.1 o.1 * fixedChartBasisGradient (relativeBasis T a.2 o.1) o.2 x) 0 := by
  have hh := genericBornProbability_hasDerivAt_zero (settingWeight d a.1 o.1)
    (fun i => relativeBasis T a.2 o.1 i o.2) x
  rw [genericGradient_eq_basisGradient] at hh
  simpa only [funext (labChartProbability_eq_generic T a o x)] using hh

lemma labChartProbability_at_zero {d : ℕ} (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (a : ℕ × Action d) (o : PVMOutcome d) (x : TangentIndex d) :
    labChartProbability T a o x 0 = settingWeight d a.1 o.1 *
      fixedChartBasisProbability (relativeBasis T a.2 o.1) o.2 := by
  rw [labChartProbability_eq_generic]
  cases x <;> simp [genericBornProbability, genericBornAmplitude, directionalState,
    Fin.sum_univ_succ, radial, fixedChartBasisProbability]

lemma labChartProbability_eq_bornProbability {d : ℕ}
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (a : ℕ × Action d) (o : PVMOutcome d) (x : TangentIndex d) (t : ℝ) (ht : t^2 ≤ 4) :
    labChartProbability T a o x t =
      PVMExploration.bornProbability (pureParameter d (P2Adaptive.labChartState T hT x t ht)) a o := by
  unfold PVMExploration.bornProbability basisProbability
  rw [inner_eq_trace]
  rfl

lemma pureProbability_eq_basisProbability {d : ℕ} (truth : PureVector d)
    (a : ℕ × Action d) (o : PVMOutcome d) :
    PVMExploration.bornProbability (pureParameter d truth) a o =
      settingWeight d a.1 o.1 * fixedChartBasisProbability (relativeBasis (trueFrame d truth) a.2 o.1) o.2 := by
  unfold PVMExploration.bornProbability basisProbability
  rw [inner_eq_trace, basisEffect_matrix]
  change settingWeight d a.1 o.1 * (Matrix.trace (rankOneDensity truth.val * projector _)).re = _
  rw [← trueFrame_projector d truth, P2Adaptive.trace_frameProjector_mul]
  have hh := projector_mulVec (trueFrame d truth).conjTranspose
    (fun i => (settingBasis a.2 o.1).matrix i o.2)
  rw [Matrix.conjTranspose_conjTranspose] at hh
  rw [← hh]
  change settingWeight d a.1 o.1 *
    ((relativeBasis (trueFrame d truth) a.2 o.1 0 o.2) * star (relativeBasis (trueFrame d truth) a.2 o.1 0 o.2)).re = _
  simp [fixedChartBasisProbability, Complex.mul_re, Complex.normSq_apply]

/-- Classical Fisher information calculated from the literal Born probabilities
and the derivatives of nearby normalized physical pure states. -/
def actualBornFisher {d : ℕ} (truth : PureVector d) (a : ℕ × Action d) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o : PVMOutcome d,
    (deriv (labChartProbability (trueFrame d truth) a o x) 0 *
      deriv (labChartProbability (trueFrame d truth) a o y) 0) /
      PVMExploration.bornProbability (pureParameter d truth) a o

lemma scaled_fisher_term (q p gx gy : ℝ) :
    ((q*gx)*(q*gy))/(q*p) = q*(gx*gy/p) := by
  by_cases hq : q = 0
  · simp [hq]
  by_cases hp : p = 0
  · simp [hp]
  field_simp

lemma actualBornFisher_eq_weightedBasisFisher {d : ℕ} (truth : PureVector d) (a : ℕ × Action d) :
    actualBornFisher truth a = ∑ b : Setting d, settingWeight d a.1 b •
      fixedChartBasisFisher (relativeBasis (trueFrame d truth) a.2 b) := by
  ext x y
  simp only [actualBornFisher, (labChartProbability_hasDerivAt _ _ _ _).deriv,
    pureProbability_eq_basisProbability, scaled_fisher_term, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, fixedChartBasisFisher, classicalFisher]
  simp only [Finset.mul_sum]

lemma actualBornFisher_eq_mixtureFisher {d : ℕ} (truth : PureVector d) (a : ℕ × Action d) :
    actualBornFisher truth a = mixtureFisher (trueFrame d truth) a.2.matrix a.1 := by
  rw [actualBornFisher_eq_weightedBasisFisher, Fintype.sum_sum_type]
  ext x y
  simp only [Fintype.sum_bool, settingWeight, settingBasis, relativeBasis,
    mixtureFisher, explorationFisher, rankOneStageInformation,
    controllerChiBasis, controllerTauBasis, chiAction, tauAction,
    transportedChiBasis, transportedTauBasis, Matrix.mul_assoc,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  ring

lemma designFisher_eq_actualBornFisher (d : ℕ) (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    designFisher d batchSize truth path n = actualBornFisher truth (n,(actualState d batchSize path n).action) := by
  rw [actualBornFisher_eq_mixtureFisher]
  rfl

/-- The main conclusion with the literal physical Born Fisher, rather than an
algebraic proxy, directly in the statement. -/
theorem pureState_PVM_actualBorn_information
    (d : ℕ) (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth),
      Filter.Tendsto (rawEstimator d batchSize path) Filter.atTop (nhds (pureParameter d truth).1) ∧
      Filter.Tendsto (stateEstimator d batchSize path) Filter.atTop (nhds (rankOneDensity truth.val)) ∧
      Filter.Tendsto (fun n => actualBornFisher truth (n,(actualState d batchSize path n).action))
        Filter.atTop (nhds ((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Filter.Tendsto (fun N : ℕ => (N:ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, actualBornFisher truth (n,(actualState d batchSize path n).action) x y)
        Filter.atTop (nhds (((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  filter_upwards [pureState_PVM_consistency_and_information d hd truth batchSize hpositive] with path hp
  have heq : designFisher d batchSize truth path =
      (fun n => actualBornFisher truth (n,(actualState d batchSize path n).action)) :=
    funext (designFisher_eq_actualBornFisher d batchSize truth path)
  simpa only [heq] using hp

/-- The ray of the held controller is also consistent even for unbounded
positive batch lengths; no complement convergence is required. -/
theorem frozenController_ray_consistent
    (d : ℕ) (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth),
      Filter.Tendsto (fun n => frameProjector (measurementFrame d batchSize path n))
        Filter.atTop (nhds (rankOneDensity truth.val)) := by
  filter_upwards [rawEstimator_consistent d batchSize (pureParameter d truth)] with path hraw
  have hfrozen := SequentialRidgeController.consistent_estimate_at_batch_refresh
    (rawEstimator d batchSize path) (pureParameter d truth).1 hraw batchSize hpositive
  simp only [measurementFrame_eq_frozenController, frameProjector]
  exact hermitianController_firstProjector_tendsto d truth (pureParameter d truth).1 rfl _ hfrozen

end
end QubitOracle.AdaptiveDesign.PVMAdaptive

-/
