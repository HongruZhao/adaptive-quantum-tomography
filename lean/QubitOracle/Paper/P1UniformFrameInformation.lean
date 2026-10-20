import QubitOracle.Paper.P1UniformFrameBorn
import QubitOracle.Paper.MixedInformationMartingale

/-! # P1: physical Fisher information and a center-safe oracle frame -/
namespace QubitOracle.AdaptiveDesign.P1

open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
noncomputable section

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤

/-- A radial/tangent frame is a physical uniform frame. -/
def fromRadialFrame (r : Fin 3 → Real) (f : MixedRadialTangentFrame r) : UniformFrame where
  axis k := ⟨radialTangentAxes f.tangentFirst f.tangentSecond f.radial k,
    (radialTangentAxes_unit r f k).le⟩
  unit_axes := radialTangentAxes_unit r f
  resolution i j := by
    have h := congrFun (congrFun f.resolution i) j
    simpa [radialTangentAxes, Fin.sum_univ_succ, QubitOracle.blochOuter,
      Matrix.one_apply, add_assoc] using h

/-- Total deterministic oracle frame, including the maximally mixed center. -/
def canonicalUniformFrame (r : Fin 3 → Real) : UniformFrame :=
  fromRadialFrame r (mixedCanonicalRadialTangentFrame r)

/-- Predictable Fisher matrix of one uniformly randomized frame. -/
def frameFisher (theta : Fin 3 → Real) (f : UniformFrame) :
    Matrix (Fin 3) (Fin 3) Real :=
  (1 / 3 : Real) • ∑ k : Fin 3, QubitOracle.mixedAxisFisher theta (f.axis k).1

/-- This is exactly the Fisher matrix of the labeled Born experiment. -/
theorem frameFisher_eq_BornFisher (theta : Fin 3 → Real) (f : UniformFrame) :
    frameFisher theta f =
      qubitLabeledActionFisher theta (.frame f.toQubitThreeAxisFrame) := by
  ext i j
  simp [frameFisher, qubitLabeledActionFisher, qubitLabeledActionWeight,
    qubitLabeledActionAxis, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]

theorem frameFisher_radial_eq (theta r : Fin 3 → Real)
    (f : MixedRadialTangentFrame r) :
    frameFisher theta (fromRadialFrame r f) =
      mixedStageInformation theta (radialTangentMass (1/3) (1/3))
        (radialTangentAxes f.tangentFirst f.tangentSecond f.radial) := by
  ext i j
  simp [frameFisher, fromRadialFrame, mixedStageInformation,
    radialTangentMass, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply]
  ring

/-- Exact Bures-optimal information at every interior controller, including zero. -/
theorem canonicalUniformFrame_exact (r : Fin 3 → Real)
    (hr : QubitOracle.blochNormSq r < 1) :
    frameFisher r (canonicalUniformFrame r) = mixedBuresTarget r := by
  rw [canonicalUniformFrame, frameFisher_radial_eq]
  exact mixedStageInformation_bures_exact r hr (mixedCanonicalRadialTangentFrame r)

/-- Truth-evaluated information converges even when the selected frame rotates
or jumps at the maximally mixed center. -/
theorem canonicalUniformFrame_information_tendsto (theta : Fin 3 → Real)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (controller : Nat → Fin 3 → Real)
    (hc : Tendsto controller atTop (nhds theta))
    (hcInterior : ∀ n, QubitOracle.blochNormSq (controller n) < 1) :
    Tendsto (fun n => frameFisher theta (canonicalUniformFrame (controller n)))
      atTop (nhds (mixedBuresTarget theta)) := by
  simpa only [canonicalUniformFrame, frameFisher_radial_eq] using
    mixedBuresStage_tendsto theta hInterior controller hc hcInterior
      (fun n => mixedCanonicalRadialTangentFrame (controller n))

/-- Selected-axis Fisher minus its predictable frame average. -/
def fisherReward (theta : Fin 3 → Real) (i j : Fin 3)
    (f : UniformFrame) (z : LabeledBinaryOutcome) : Real :=
  QubitOracle.mixedAxisFisher theta (f.axis z.1).1 i j - frameFisher theta f i j

private theorem integral_frame_label_reward (theta : OneQubitPhysicalParameter)
    (f : UniformFrame) (g : Fin 3 → Real) :
    (∫ z : LabeledBinaryOutcome, g z.1
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame)) =
      (1 / 3 : Real) * ∑ k : Fin 3, g k := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul, Measure.real_def, qubitLabeledBornResponseKernel_singleton]
  simp_rw [ENNReal.toReal_ofReal
    (qubitLabeledBornProbability_nonnegative theta (.frame f.toQubitThreeAxisFrame) _)]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_binaryOutcome]
  simp [qubitLabeledBornProbability, qubitLabeledActionWeight,
    qubitLabeledActionAxis, binaryBornProbability, BinaryOutcome.sign]
  ring

theorem fisherReward_mean (theta : OneQubitPhysicalParameter)
    (i j : Fin 3) (f : UniformFrame) :
    (∫ z, fisherReward theta.1 i j f z
      ∂qubitLabeledBornResponseKernel theta (.frame f.toQubitThreeAxisFrame)) = 0 := by
  unfold fisherReward
  rw [integral_frame_label_reward theta f (fun k =>
    QubitOracle.mixedAxisFisher theta.1 (f.axis k).1 i j - frameFisher theta.1 f i j),
    Finset.sum_sub_distrib]
  simp [frameFisher, Matrix.smul_apply, Matrix.sum_apply]

theorem frameFisher_entry_bound (theta : Fin 3 → Real)
    (ht : QubitOracle.blochNormSq theta < 1)
    (f : UniformFrame) (i j : Fin 3) :
    ‖frameFisher theta f i j‖ ≤ (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  change ‖(1 / 3 : Real) * ∑ k : Fin 3,
    QubitOracle.mixedAxisFisher theta (f.axis k).1 i j‖ ≤ _
  rw [norm_mul]
  have hs := norm_sum_le (Finset.univ : Finset (Fin 3))
    (fun k => QubitOracle.mixedAxisFisher theta (f.axis k).1 i j)
  have hs2 : (∑ k : Fin 3,
      ‖QubitOracle.mixedAxisFisher theta (f.axis k).1 i j‖) ≤
      3 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by
    calc
      _ ≤ ∑ k : Fin 3, (1 - QubitOracle.blochNormSq theta)⁻¹ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mixedAxisInformation_entry_norm_le theta (f.axis k).1 ht (f.unit_axes k) i j
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left (hs.trans hs2) (norm_nonneg (1 / 3 : Real))
  norm_num at hh ⊢
  linarith

theorem fisherReward_bound (theta : Fin 3 → Real)
    (ht : QubitOracle.blochNormSq theta < 1)
    (i j : Fin 3) (f : UniformFrame) (z : LabeledBinaryOutcome) :
    ‖fisherReward theta i j f z‖ ≤ 2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  exact (norm_sub_le _ _).trans (by
    have ha := mixedAxisInformation_entry_norm_le theta (f.axis z.1).1 ht
      (f.unit_axes z.1) i j
    have hb := frameFisher_entry_bound theta ht f i j
    linarith)

/-- Realized selected-axis information and predictable information have the
same empirical limit on the literal adaptive Born path. -/
theorem fisherInnovation_average_ae (policy : FramePolicy)
    (theta : OneQubitPhysicalParameter)
    (ht : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂pathMeasure policy theta, ∀ i j : Fin 3,
      Tendsto (fun N : Nat => (N : Real)⁻¹ * ∑ k ∈ Finset.range (N+1),
        (QubitOracle.mixedAxisFisher theta.1 (actualAxis policy k path) i j -
          frameFisher theta.1 (actualFrame policy k path) i j)) atTop (nhds 0) := by
  exact ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    centeredReward_average_ae policy theta (fisherReward theta.1 i j)
      (2 * (1 - QubitOracle.blochNormSq theta.1)⁻¹)
      (by positivity)
      (fisherReward_bound theta.1 ht i j) (fisherReward_mean theta i j)

end
end QubitOracle.AdaptiveDesign.P1
