import QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureChartCovariance
import QubitOracle.AdaptiveDesign.PureChartDifferential
import QubitOracle.AdaptiveDesign.PureChartDomain
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.PureSLDMetric
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
set_option autoImplicit false

/-! Smooth local coordinates in Definition A.2, expressed as a change
from the normalized amplitude chart at the true projector. The change
is an actual local homeomorphism, smooth in both directions. Its
invertible derivative and a measurable constant extension are proved;
they are not extra hypotheses in the statistical endpoint. -/
namespace QubitOracle.Paper.MainPaperPureCharts
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
noncomputable section

abbrev Coordinates (d : ℕ) := PureChartCovariance.Coordinates d

structure SmoothCoordinates (d : ℕ) where
  change : OpenPartialHomeomorph (Coordinates d) (Coordinates d)
  zero_mem_source : (0 : Coordinates d) ∈ change.source
  smooth : ContDiffOn ℝ ∞ change change.source
  inverse_smooth : ContDiffOn ℝ ∞ change.symm change.target

namespace SmoothCoordinates
variable {d : ℕ} (C : SmoothCoordinates d)

def jacobian : Coordinates d →L[ℝ] Coordinates d :=
  fderiv ℝ C.change 0

def inverseJacobian : Coordinates d →L[ℝ] Coordinates d :=
  fderiv ℝ C.change.symm (C.change 0)

theorem hasDerivative : HasFDerivAt C.change C.jacobian 0 := by
  exact (((C.smooth 0 C.zero_mem_source).contDiffAt
    (C.change.open_source.mem_nhds C.zero_mem_source)).differentiableAt (by norm_num)).hasFDerivAt

theorem inverse_hasDerivative :
    HasFDerivAt C.change.symm C.inverseJacobian (C.change 0) := by
  have hm := C.change.map_source C.zero_mem_source
  exact (((C.inverse_smooth _ hm).contDiffAt
    (C.change.open_target.mem_nhds hm)).differentiableAt (by norm_num)).hasFDerivAt

theorem inverse_comp_jacobian :
    C.inverseJacobian.comp C.jacobian = ContinuousLinearMap.id ℝ (Coordinates d) := by
  have he : (fun u => C.change.symm (C.change u)) =ᶠ[𝓝 (0 : Coordinates d)] id := by
    filter_upwards [C.change.open_source.mem_nhds C.zero_mem_source] with u hu
    exact C.change.left_inv hu
  exact ((C.inverse_hasDerivative.comp 0 C.hasDerivative).congr_of_eventuallyEq he.symm).unique
    (hasFDerivAt_id (0 : Coordinates d))

theorem jacobian_comp_inverse :
    C.jacobian.comp C.inverseJacobian = ContinuousLinearMap.id ℝ (Coordinates d) := by
  have hm := C.change.map_source C.zero_mem_source
  have hf : HasFDerivAt C.change C.jacobian (C.change.symm (C.change 0)) := by
    simpa only [C.change.left_inv C.zero_mem_source] using C.hasDerivative
  have he : (fun u => C.change (C.change.symm u)) =ᶠ[𝓝 (C.change 0)] id := by
    filter_upwards [C.change.open_target.mem_nhds hm] with u hu
    exact C.change.right_inv hu
  exact ((hf.comp _ C.inverse_hasDerivative).congr_of_eventuallyEq he.symm).unique
    (hasFDerivAt_id (C.change 0))

/-- The coordinate derivative is invertible because both coordinate
maps are smooth local inverses. No invertibility premise is supplied. -/
def derivativeEquiv : Coordinates d ≃L[ℝ] Coordinates d where
  toLinearEquiv :=
    { toLinearMap := C.jacobian.toLinearMap
      invFun := C.inverseJacobian
      left_inv := by
        intro u
        exact congrArg (fun L : Coordinates d →L[ℝ] Coordinates d => L u) C.inverse_comp_jacobian
      right_inv := by
        intro u
        exact congrArg (fun L : Coordinates d →L[ℝ] Coordinates d => L u) C.jacobian_comp_inverse }
  continuous_toFun := C.jacobian.continuous
  continuous_invFun := C.inverseJacobian.continuous

/-- Extension by the true coordinate outside the open coordinate domain,
as allowed in the domain paragraph following Theorem 4.2. -/
def extension (u : Coordinates d) : Coordinates d := by
  classical
  exact if u ∈ C.change.source then C.change u else C.change 0

theorem extension_measurable : Measurable C.extension := by
  classical
  exact C.change.continuousOn_toFun.measurable_piecewise continuous_const.continuousOn
    C.change.open_source.measurableSet

theorem extension_zero : C.extension 0 = C.change 0 := by
  simp [extension, C.zero_mem_source]

theorem extension_agrees_locally : C.extension =ᶠ[𝓝 (0 : Coordinates d)] C.change := by
  filter_upwards [C.change.open_source.mem_nhds C.zero_mem_source] with u hu
  simp [extension, hu]

theorem extension_hasDerivative : HasFDerivAt C.extension C.derivativeEquiv.toContinuousLinearMap 0 :=
  C.hasDerivative.congr_of_eventuallyEq C.extension_agrees_locally

/-- The corresponding inverse pure-state chart, not an arbitrary state
model supplied independently of the coordinate change. -/
def parametrization (truth : PureVector d) (theta : Coordinates d) : HermitianSpace (d+1) :=
  trueChartMatrix truth (C.change.symm theta)

theorem parametrization_at_truth (truth : PureVector d) :
    C.parametrization truth (C.change 0) = (pureParameter d truth).val := by
  simp only [parametrization, C.change.left_inv C.zero_mem_source]
  have hz : chartState (0 : Coordinates d) = (knownReference d).val := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [chartState, tangentRadiusSq, knownReference]
    · simp [chartState, tangentRadiusSq, knownReference]
      rfl
  have he : referenceChartMatrix (0 : Coordinates d) = (pureParameter d (knownReference d)).val := by
    apply toMatrix_injective
    change GlobalPFSIC.projector (chartState (0 : Coordinates d)) =
      rankOneDensity (knownReference d).val
    rw [hz]
    rfl
  change trueChartMatrix truth 0 = _
  rw [trueChartMatrix, he]
  exact trueFrame_referenceParameter truth

theorem parametrization_hasDerivative (truth : PureVector d) :
    HasFDerivAt (C.parametrization truth)
      (((1/2 : ℝ) • trueLift truth).comp C.derivativeEquiv.symm.toContinuousLinearMap)
      (C.change 0) := by
  have hf : HasFDerivAt (trueChartMatrix truth) ((1/2 : ℝ) • trueLift truth)
      (C.change.symm (C.change 0)) := by
    simpa only [C.change.left_inv C.zero_mem_source] using trueChart_hasFDerivAt_zero truth
  exact hf.comp _ C.inverse_hasDerivative

theorem parametrization_locally_physical (truth : PureVector d) :
    ∀ᶠ theta in 𝓝 (C.change 0),
      ∃ h : PureVector d, C.parametrization truth theta = (pureParameter d h).val := by
  have ht : Tendsto C.change.symm (𝓝 (C.change 0)) (𝓝 (0 : Coordinates d)) := by
    simpa only [C.change.left_inv C.zero_mem_source] using
      C.inverse_hasDerivative.continuousAt.tendsto
  filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : Coordinates d) (by norm_num : (0:ℝ)<2))]
    with theta htheta
  exact ⟨trueChartPureVector truth _ (tangentRadiusSq_lt_four_of_ball _ htheta).le,
    trueChart_is_pure truth _ _⟩

/-- The QFI of this actual inverse chart is the operator used in the
Gaussian covariance formula, rather than a matrix named by convention. -/
theorem parametrization_sld (truth : PureVector d) (u v : Coordinates d) :
    PureSLDMetric.metricFromSLD truth
      (PureSLDMetric.normalizedLift truth (C.derivativeEquiv.symm u))
      (PureSLDMetric.normalizedLift truth (C.derivativeEquiv.symm v)) =
      ⟪u, PureChartCovariance.qfiOperator C.derivativeEquiv v⟫_ℝ :=
  PureChartCovariance.qfi_is_sld truth C.derivativeEquiv u v

end SmoothCoordinates
end
end QubitOracle.Paper.MainPaperPureCharts
