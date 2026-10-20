import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.RankOneLosses
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Exact amplitude-chart coordinates and transfer from the projector
coordinates used in the score CLT. The inverse chart is extended by zero
at an orthogonal ray; consistency makes that extension immaterial. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def referenceChartMatrix {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d)) :
    HermitianSpace (d+1) :=
  ofMatrix (GlobalPFSIC.projector (chartState u))
    (GlobalPFSIC.projector_posSemidef _).isHermitian

theorem referenceChart_coordinate {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d)) :
    (2:ℝ) • referenceCoordinate d (referenceChartMatrix u) =
      Real.sqrt (1-tangentRadiusSq u/4) • u := by
  ext i
  cases i <;>
    simp [referenceCoordinate, referenceCoordinateLinear, referenceChartMatrix,
      GeneralPOVM.matrixGradient, GlobalPFSIC.projector_apply, chartState,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem referenceCoordinate_reference (d : ℕ) :
    referenceCoordinate d (pureParameter d (knownReference d)).val = 0 := by
  ext i
  cases i <;>
    simp [referenceCoordinate, referenceCoordinateLinear, pureParameter,
      GeneralPOVM.matrixGradient, knownReference, rankOneDensity, Pi.single_apply]

theorem referenceChart_overlap {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d))
    (hu : tangentRadiusSq u ≤ 4) :
    ⟪(pureParameter d (knownReference d)).val, referenceChartMatrix u⟫_ℝ =
      1-tangentRadiusSq u/4 := by
  rw [inner_eq_trace]
  have hs := Real.sq_sqrt (show 0 ≤ 1-tangentRadiusSq u/4 by linarith)
  simpa [pureParameter, knownReference, rankOneDensity, referenceChartMatrix,
    GlobalPFSIC.projector_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Pi.single_apply, chartState, Complex.mul_re, Complex.mul_im, pow_two] using hs

def trueChartMatrix {d : ℕ} (truth : PureVector d)
    (u : EuclideanSpace ℝ (TangentIndex d)) : HermitianSpace (d+1) :=
  conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth) (referenceChartMatrix u)

theorem trueFrame_referenceParameter {d : ℕ} (truth : PureVector d) :
    conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
      (pureParameter d (knownReference d)).val = (pureParameter d truth).val := by
  apply toMatrix_injective
  exact trueFrame_reference_ray truth

/-- The paper's inverse amplitude chart, globally extended at zero overlap. -/
def amplitudeCoordinates {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    EuclideanSpace ℝ (TangentIndex d) :=
  (Real.sqrt ⟪(pureParameter d truth).val,A⟫_ℝ)⁻¹ •
    ((2:ℝ) • trueCoordinate truth (A-(pureParameter d truth).val))

/-- This is an exact inverse on the open radius-two chart, rather than
merely a map with the same derivative at the centre. -/
theorem amplitudeCoordinates_chart {d : ℕ} (truth : PureVector d)
    (u : EuclideanSpace ℝ (TangentIndex d)) (hu : tangentRadiusSq u < 4) :
    amplitudeCoordinates truth (trueChartMatrix truth u) = u := by
  let U := conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
  have hp : (pureParameter d truth).val = U (pureParameter d (knownReference d)).val :=
    (trueFrame_referenceParameter truth).symm
  have hinner : ⟪(pureParameter d truth).val, trueChartMatrix truth u⟫_ℝ =
      1-tangentRadiusSq u/4 := by
    change ⟪(pureParameter d truth).val, U (referenceChartMatrix u)⟫_ℝ = _
    rw [hp, U.inner_map_map]
    exact referenceChart_overlap u hu.le
  have hcoord : (2:ℝ) • trueCoordinate truth
      (trueChartMatrix truth u-(pureParameter d truth).val) =
      Real.sqrt (1-tangentRadiusSq u/4) • u := by
    change (2:ℝ) • referenceCoordinate d
      (U.symm (U (referenceChartMatrix u)-(pureParameter d truth).val)) = _
    rw [hp, ← map_sub, U.symm_apply_apply, map_sub, referenceCoordinate_reference, sub_zero]
    exact referenceChart_coordinate u
  rw [amplitudeCoordinates, hinner, hcoord, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (show 0 < 1-tangentRadiusSq u/4 by linarith)).ne', one_smul]

theorem amplitude_factor_continuousAt {d : ℕ} (truth : PureVector d) :
    ContinuousAt (fun A : HermitianSpace (d+1) =>
      (Real.sqrt ⟪(pureParameter d truth).val,A⟫_ℝ)⁻¹) (pureParameter d truth).val := by
  apply ContinuousAt.inv₀
  · fun_prop
  · rw [real_inner_self_eq_norm_sq, pureParameter_norm]
    norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Slutsky transfer to the exact amplitude coordinates. The assumptions
are a genuine consistency assertion and the already proved projector CLT. -/
theorem amplitude_clt_of_projector_clt {d : ℕ} (truth : PureVector d)
    {covMatrix : Matrix (TangentIndex d) (TangentIndex d) ℝ}
    (A : ℕ → Ω → HermitianSpace (d+1))
    (hA : ∀ n, StronglyMeasurable (A n))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (pureParameter d truth).val))
    (hclt : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth (A n ω-(pureParameter d truth).val)))
      atTop id (fun _ => μ)
      (multivariateGaussian 0 covMatrix)) :
    TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (A n ω))
      atTop id (fun _ => μ)
      (multivariateGaussian 0 covMatrix) := by
  let factor := fun n ω => (Real.sqrt ⟪(pureParameter d truth).val,A n ω⟫_ℝ)⁻¹
  have hm (n : ℕ) : Measurable (factor n) := by
    exact ((stronglyMeasurable_const.inner (hA n)).measurable.sqrt).inv
  have hf : TendstoInMeasure μ factor atTop (fun _ => (1:ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable)
    filter_upwards [hc] with ω hω
    have hh := (amplitude_factor_continuousAt truth).tendsto.comp hω
    simpa only [Function.comp_def, factor, real_inner_self_eq_norm_sq, pureParameter_norm, one_pow,
      Real.sqrt_one, inv_one] using hh
  have hh := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : EuclideanSpace ℝ (TangentIndex d) × ℝ => x.2 • x.1)
    (by fun_prop) hf (fun n => (hm n).aemeasurable)
  have heq (n : ℕ) (ω : Ω) :
      factor n ω • (Real.sqrt (n:ℝ) • ((2:ℝ) • trueCoordinate truth
        (A n ω-(pureParameter d truth).val))) =
      Real.sqrt (n:ℝ) • amplitudeCoordinates truth (A n ω) := by
    exact smul_comm _ _ _
  exact hh.congr (fun n => Eventually.of_forall (heq n))
    (Eventually.of_forall (fun _ => one_smul ℝ _))

end
end QubitOracle.AdaptiveDesign.TangentGLS
