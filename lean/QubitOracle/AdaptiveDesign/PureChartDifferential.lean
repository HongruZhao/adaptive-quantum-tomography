import QubitOracle.AdaptiveDesign.PureChartCoverage
import QubitOracle.AdaptiveDesign.PureSLDMetric
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! Fréchet derivative of the actual normalized amplitude chart. This
identifies the SLD normalization with the chart, rather than merely with
an abstract linear tangent map. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace Topology ComplexOrder Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

def chartAmplitudeLinear (d : ℕ) (i : Fin (d+1)) :
    EuclideanSpace ℝ (TangentIndex d) →L[ℝ] ℂ :=
  Fin.cases 0 (fun j => (1/2:ℝ) •
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (Sum.inl j)))+
      Complex.I • (Complex.ofRealCLM.comp (EuclideanSpace.proj (Sum.inr j))))) i

theorem chartState_continuous (d : ℕ) :
    Continuous (fun u : EuclideanSpace ℝ (TangentIndex d) => chartState u) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun u : EuclideanSpace ℝ (TangentIndex d) =>
      (Real.sqrt (1-tangentRadiusSq u/4) : ℂ))
    unfold tangentRadiusSq
    exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (by fun_prop))
  · change Continuous (fun u : EuclideanSpace ℝ (TangentIndex d) =>
      (⟨u (Sum.inl j)/2,u (Sum.inr j)/2⟩ : ℂ))
    have he : (fun u : EuclideanSpace ℝ (TangentIndex d) =>
        (⟨u (Sum.inl j)/2,u (Sum.inr j)/2⟩ : ℂ)) =
        fun u => ((u (Sum.inl j)/2 : ℝ) : ℂ)+((u (Sum.inr j)/2 : ℝ) : ℂ)*Complex.I := by
      funext u; apply Complex.ext <;> simp
    rw [he]
    fun_prop

theorem chartState_hasFDerivAt_zero (d : ℕ) (i : Fin (d+1)) :
    HasFDerivAt (fun u : EuclideanSpace ℝ (TangentIndex d) => chartState u i)
      (chartAmplitudeLinear d i) 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hn : HasFDerivAt (fun u : EuclideanSpace ℝ (TangentIndex d) => tangentRadiusSq u)
        (0 : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] ℝ) 0 := by
      have hh := (hasFDerivAt_id (𝕜:=ℝ) (x:=(0:EuclideanSpace ℝ (TangentIndex d)))).norm_sq
      simpa [EuclideanSpace.real_norm_sq_eq,tangentRadiusSq] using hh
    have hh := ((hasFDerivAt_const (𝕜:=ℝ) (1:ℝ) (0:EuclideanSpace ℝ (TangentIndex d))).sub
      (hn.mul_const (1/4:ℝ))).sqrt (by simp [tangentRadiusSq])
    have hc := Complex.ofRealCLM.hasFDerivAt.comp 0 hh
    convert! hc using 1 <;>
      simp [chartAmplitudeLinear,chartState,tangentRadiusSq,div_eq_mul_inv] <;> rfl
  · convert (chartAmplitudeLinear d j.succ).hasFDerivAt using 1
    funext u
    apply Complex.ext <;> simp [chartState,chartAmplitudeLinear,Complex.mul_re,Complex.mul_im] <;> ring

theorem referenceChart_continuous (d : ℕ) :
    Continuous (@referenceChartMatrix d) := by
  have he := (toMatrixLinear (d+1)).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr toMatrix_injective)
  apply he.isEmbedding.isInducing.continuous_iff.mpr
  change Continuous (fun u : EuclideanSpace ℝ (TangentIndex d) =>
    GlobalPFSIC.projector (chartState u))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).comp (chartState_continuous d)).mul
    (((continuous_apply j).comp (chartState_continuous d)).star)

theorem referenceChart_hasFDerivAt_zero (d : ℕ) :
    HasFDerivAt (@referenceChartMatrix d) ((1/2:ℝ) • referenceLift d) 0 := by
  let M := (toMatrixLinear (d+1)).toContinuousLinearMap
  have he := (toMatrixLinear (d+1)).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr toMatrix_injective)
  have hm : HasFDerivAt (fun u => toMatrix (referenceChartMatrix u))
      (M.comp ((1/2:ℝ) • referenceLift d)) 0 := by
    apply hasFDerivAt_pi'.mpr
    intro i
    apply hasFDerivAt_pi'.mpr
    intro j
    have hj := Complex.conjCLE.hasFDerivAt.comp 0 (chartState_hasFDerivAt_zero d j)
    have hh := (chartState_hasFDerivAt_zero d i).mul hj
    convert! hh using 1
    ext u
    change ((1/2:ℝ) • referenceTangentMatrix u) i j =
      chartState (0 : EuclideanSpace ℝ (TangentIndex d)) i *
        star (chartAmplitudeLinear d j u) +
      star (chartState (0 : EuclideanSpace ℝ (TangentIndex d)) j) * chartAmplitudeLinear d i u
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      apply Complex.ext <;>
      simp [referenceTangentMatrix,
        chartAmplitudeLinear,chartState,tangentRadiusSq,Complex.mul_re,Complex.mul_im,
        toMatrix_smul,toMatrix_ofMatrix] <;> ring
  exact HasFDerivAt.of_comp_of_isEmbedding (f:=M) (f':=M)
    (referenceChart_continuous d).continuousAt
    M.hasFDerivAt he.isEmbedding hm (Filter.Eventually.of_forall (fun _ => rfl))

theorem trueChart_hasFDerivAt_zero {d : ℕ} (truth : PureVector d) :
    HasFDerivAt (trueChartMatrix truth) ((1/2:ℝ) • trueLift truth) 0 := by
  let U := conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
  have hh := U.toContinuousLinearMap.hasFDerivAt.comp 0 (referenceChart_hasFDerivAt_zero d)
  convert! hh using 1
  ext u
  exact (map_smul U (1/2:ℝ) (referenceLift d u)).symm

theorem chart_sld_metric {d : ℕ} (truth : PureVector d)
    (u v : EuclideanSpace ℝ (TangentIndex d)) :
    PureSLDMetric.metricFromSLD truth
      ⟨fderiv ℝ (trueChartMatrix truth) 0 u, by
        rw [(trueChart_hasFDerivAt_zero truth).fderiv]
        exact (PureSLDMetric.normalizedLift truth u).property⟩
      ⟨fderiv ℝ (trueChartMatrix truth) 0 v, by
        rw [(trueChart_hasFDerivAt_zero truth).fderiv]
        exact (PureSLDMetric.normalizedLift truth v).property⟩ = ⟪u,v⟫_ℝ := by
  simpa only [(trueChart_hasFDerivAt_zero truth).fderiv,PureSLDMetric.normalizedLift,
    ContinuousLinearMap.smul_apply] using
    PureSLDMetric.normalized_metric truth u v

end
end QubitOracle.AdaptiveDesign.TangentGLS
