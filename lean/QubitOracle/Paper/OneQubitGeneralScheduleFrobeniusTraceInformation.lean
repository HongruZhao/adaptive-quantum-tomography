import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedInformationMartingale
import QubitOracle.Paper.MixedOracleFeasible
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.MixedStageStability
import QubitOracle.Paper.OneQubitAPSRLSContract
import QubitOracle.Paper.OneQubitFixedDesignInformation
import QubitOracle.Paper.OneQubitLocalContinuousFrame
import QubitOracle.Paper.OneQubitTwoStageInformationConvergence
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Filter MeasureTheory Set Matrix
open scoped BigOperators Topology Matrix

noncomputable section

private theorem generalSchedule_blochNormSq_mul_vector
    (c : Real) (x : RLSVector 3) :
    QubitOracle.blochNormSq (fun i => c * x i) =
      c ^ 2 * QubitOracle.blochNormSq x := by
  unfold QubitOracle.blochNormSq
  simp_rw [mul_pow]
  rw [Finset.mul_sum]





/-! ## A total deterministic radial/tangent frame -/

/-- A radial/tangent frame at every Bloch vector.  At the center it is the
ordered Pauli frame.  Away from the center it is the Householder frame aligned
with the normalized Bloch direction. -/
noncomputable def mixedCanonicalRadialTangentFrame
    (r : RLSVector 3) : MixedRadialTangentFrame r := by
  classical
  by_cases hzero : QubitOracle.blochNormSq r = 0
  · have hrzero : r = 0 := (blochNormSq_eq_zero_iff r).1 hzero
    exact
      { radial := qubitPauliCoordinateAxis 2
        tangentFirst := qubitPauliCoordinateAxis 0
        tangentSecond := qubitPauliCoordinateAxis 1
        radial_unit := qubitPauliCoordinateAxis_normSq 2
        tangentFirst_unit := qubitPauliCoordinateAxis_normSq 0
        tangentSecond_unit := qubitPauliCoordinateAxis_normSq 1
        tangentFirst_orthogonal := by simp [hrzero, QubitOracle.blochDot]
        tangentSecond_orthogonal := by simp [hrzero, QubitOracle.blochDot]
        radial_dot_sq := by
          simp [hrzero, QubitOracle.blochDot, QubitOracle.blochNormSq]
        resolution := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [qubitPauliCoordinateAxis, QubitOracle.blochOuter,
              Matrix.one_apply]
        radial_outer_of_nonzero := by
          intro hnonzero
          exact (hnonzero hzero).elim }
  · have hrpos : 0 < QubitOracle.blochNormSq r :=
      lt_of_le_of_ne (blochNormSq_nonneg r) (Ne.symm hzero)
    let u : RLSVector 3 := localNormalizedBlochDirection r
    let R : Matrix (Fin 3) (Fin 3) Real :=
      qubitTruthAlignedHouseholderFrame u
    have hu : QubitOracle.blochNormSq u = 1 := by
      exact localNormalizedBlochDirection_normSq hrpos
    have hradial : qubitFrameAxis R 2 = u := by
      exact qubitTruthAlignedHouseholderFrame_radial_axis hu
    have hsqrt : Real.sqrt (QubitOracle.blochNormSq r) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hrpos)
    have hdotRadial : QubitOracle.blochDot r u =
        Real.sqrt (QubitOracle.blochNormSq r) := by
      have hsquare := Real.sq_sqrt hrpos.le
      have hsqrtExpanded :
          Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) ≠ 0 := by
        simpa [QubitOracle.blochNormSq, Fin.sum_univ_succ] using hsqrt
      simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at hsquare
      simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
        QubitOracle.blochNormSq, Fin.sum_univ_succ]
      calc
        r 0 * (r 0 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2))) +
              (r 1 * (r 1 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2))) +
                r 2 * (r 2 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)))) =
            (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) /
              Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) := by
                field_simp [hsqrtExpanded]
        _ = Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) := by
          rw [div_eq_iff hsqrtExpanded]
          nlinarith [hsquare]
    exact
      { radial := qubitFrameAxis R 2
        tangentFirst := qubitFrameAxis R 0
        tangentSecond := qubitFrameAxis R 1
        radial_unit := qubitTruthAlignedHouseholderFrame_axis_normSq u 2
        tangentFirst_unit :=
          qubitTruthAlignedHouseholderFrame_axis_normSq u 0
        tangentSecond_unit :=
          qubitTruthAlignedHouseholderFrame_axis_normSq u 1
        tangentFirst_orthogonal := by
          have horth := qubitTruthAlignedHouseholderFrame_axes_orthogonal
            u (2 : Fin 3) (0 : Fin 3)
          rw [if_neg (by decide), hradial] at horth
          change QubitOracle.blochDot r (qubitFrameAxis R 0) = 0
          simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
            Fin.sum_univ_succ] at horth ⊢
          field_simp [hsqrt] at horth
          simpa [mul_comm, mul_left_comm, mul_assoc] using horth
        tangentSecond_orthogonal := by
          have horth := qubitTruthAlignedHouseholderFrame_axes_orthogonal
            u (2 : Fin 3) (1 : Fin 3)
          rw [if_neg (by decide), hradial] at horth
          change QubitOracle.blochDot r (qubitFrameAxis R 1) = 0
          simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
            Fin.sum_univ_succ] at horth ⊢
          field_simp [hsqrt] at horth
          simpa [mul_comm, mul_left_comm, mul_assoc] using horth
        radial_dot_sq := by
          rw [hradial, hdotRadial, Real.sq_sqrt hrpos.le]
        resolution := by
          have hmatrix : R * R.transpose = 1 :=
            mul_eq_one_comm.mp
              (qubitTruthAlignedHouseholderFrame_transpose_mul_self u)
          ext i j
          simpa [R, QubitOracle.blochOuter, qubitFrameAxis,
            Matrix.mul_apply, Fin.sum_univ_succ, add_assoc] using
              congrFun (congrFun hmatrix i) j
        radial_outer_of_nonzero := by
          intro _hnonzero
          rw [hradial]
          ext i j
          simp [u, localNormalizedBlochDirection, mixedRadialProjector,
            QubitOracle.blochOuter]
          field_simp [hsqrt, hzero]
          rw [Real.sq_sqrt hrpos.le]
          ring }

/-! ## Literal Frobenius/trace exploitation and full information -/

/-- Per-observation adaptive exploitation information at truth `theta`, with
allocations and axes selected from the safe controller value `x`. -/
noncomputable def generalScheduleFrobeniusTraceControllerInformation
    (theta x : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  let frame := mixedCanonicalRadialTangentFrame x
  mixedStageInformation theta
    (radialTangentMass
      (mixedCoherenceAllocation x) (mixedRadialAllocation x))
    (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial)

theorem generalScheduleFrobeniusTraceControllerInformation_entry_norm_le
    (theta x : RLSVector 3)
    (hThetaInterior : QubitOracle.blochNormSq theta < 1)
    (hXInterior : QubitOracle.blochNormSq x < 1)
    (i j : Fin 3) :
    ‖generalScheduleFrobeniusTraceControllerInformation theta x i j‖ <=
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  let frame := mixedCanonicalRadialTangentFrame x
  let mass := radialTangentMass
    (mixedCoherenceAllocation x) (mixedRadialAllocation x)
  let axis := radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial
  have hmass0 : forall k, 0 <= mass k :=
    radialTangentMass_nonnegative _ _
      (mixedCoherenceAllocation_pos x hXInterior).le
      (mixedRadialAllocation_pos x hXInterior).le
  have hmassSum : (∑ k, mass k) = 1 :=
    radialTangentMass_sum _ _ (mixedAllocations_sum x hXInterior)
  have haxis : forall k, QubitOracle.blochNormSq (axis k) = 1 :=
    radialTangentAxes_unit x frame
  rw [Real.norm_eq_abs]
  unfold generalScheduleFrobeniusTraceControllerInformation
    mixedStageInformation
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change |∑ k, mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| <= _
  calc
    |∑ k, mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| <=
        ∑ k, |mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, mass k *
          ‖QubitOracle.mixedAxisFisher theta (axis k) i j‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg (hmass0 k), Real.norm_eq_abs]
    _ <= ∑ k, mass k *
          (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (mixedAxisInformation_entry_norm_le
          theta (axis k) hThetaInterior (haxis k) i j)
        (hmass0 k)
    _ = (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      rw [← Finset.sum_mul, hmassSum, one_mul]


/-! ## The same total controller closes Bures information at the center -/

/-- Equal-mass Bures exploitation information using the same total canonical
radial/tangent frame. -/
noncomputable def generalScheduleCanonicalBuresControllerInformation
    (theta x : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  let frame := mixedCanonicalRadialTangentFrame x
  mixedStageInformation theta
    (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
    (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial)











end

end QubitOracle.Paper
