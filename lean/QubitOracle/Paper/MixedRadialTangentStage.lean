import QubitOracle.Paper.MixedRotationalTarget

/-!
# Radial/tangent realization of mixed-qubit exploitation information
-/

namespace QubitOracle
namespace Paper

open Filter
open scoped BigOperators Topology Matrix

/-- Three-axis allocation with two equal tangent masses and one radial mass. -/
def radialTangentMass (a b : Real) : Fin 3 -> Real :=
  ![a, a, b]

/-- Ordered tangent, tangent, radial measurement axes. -/
def radialTangentAxes
    (tangentFirst tangentSecond radial : Fin 3 -> Real) :
    Fin 3 -> Fin 3 -> Real :=
  ![tangentFirst, tangentSecond, radial]

/-- The exact geometric data meant by a radial axis and any orthonormal
estimated tangent pair.  `radial_outer_of_nonzero` records only the
sign-insensitive projector property needed by information. -/
structure MixedRadialTangentFrame (r : Fin 3 -> Real) where
  radial : Fin 3 -> Real
  tangentFirst : Fin 3 -> Real
  tangentSecond : Fin 3 -> Real
  radial_unit : blochNormSq radial = 1
  tangentFirst_unit : blochNormSq tangentFirst = 1
  tangentSecond_unit : blochNormSq tangentSecond = 1
  tangentFirst_orthogonal : blochDot r tangentFirst = 0
  tangentSecond_orthogonal : blochDot r tangentSecond = 0
  radial_dot_sq : blochDot r radial ^ 2 = blochNormSq r
  resolution :
    blochOuter tangentFirst + blochOuter tangentSecond + blochOuter radial = 1
  radial_outer_of_nonzero :
    blochNormSq r ≠ 0 -> blochOuter radial = mixedRadialProjector r

/-- The tangent/radial mass function is a probability mass exactly when
`2a+b=1`. -/
theorem radialTangentMass_nonnegative
    (a b : Real) (ha : 0 <= a) (hb : 0 <= b) :
    ∀ i, 0 <= radialTangentMass a b i := by
  intro i
  fin_cases i <;> simp [radialTangentMass, ha, hb]

theorem radialTangentMass_sum
    (a b : Real) (hsum : 2 * a + b = 1) :
    ∑ i, radialTangentMass a b i = 1 := by
  simp [radialTangentMass, Fin.sum_univ_succ]
  linarith

/-- All three axes encoded by a radial/tangent frame are unit. -/
theorem radialTangentAxes_unit
    (r : Fin 3 -> Real) (frame : MixedRadialTangentFrame r) :
    ∀ i, blochNormSq
      (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial i) = 1 := by
  intro i
  fin_cases i <;> simp [radialTangentAxes, frame.tangentFirst_unit,
    frame.tangentSecond_unit, frame.radial_unit]

/-- At a tangent axis, controller-evaluated Fisher information is its outer
projector. -/
theorem mixedAxisFisher_eq_outer_of_orthogonal
    (r u : Fin 3 -> Real) (horth : blochDot r u = 0) :
    mixedAxisFisher r u = blochOuter u := by
  unfold mixedAxisFisher
  simp [horth]

/-- At the radial axis, controller-evaluated Fisher information has the
radial Bernoulli denominator. -/
theorem mixedAxisFisher_eq_radial_of_dot_sq
    (r u : Fin 3 -> Real)
    (hradial : blochDot r u ^ 2 = blochNormSq r) :
    mixedAxisFisher r u =
      (1 - blochNormSq r)⁻¹ • blochOuter u := by
  unfold mixedAxisFisher
  rw [hradial]

/-- Exact finite-sum expansion for a radial/tangent stage. -/
theorem mixedStageInformation_radialTangent_expand
    (r : Fin 3 -> Real) (frame : MixedRadialTangentFrame r)
    (a b : Real) :
    mixedStageInformation r (radialTangentMass a b)
      (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial) =
      a • mixedAxisFisher r frame.tangentFirst +
      a • mixedAxisFisher r frame.tangentSecond +
      b • mixedAxisFisher r frame.radial := by
  unfold mixedStageInformation radialTangentMass radialTangentAxes
  simp [Fin.sum_univ_succ]
  abel

/-- Controller-stage information in radial/tangent projector form. -/
theorem mixedStageInformation_radialTangent_eq_projectors
    (r : Fin 3 -> Real) (frame : MixedRadialTangentFrame r)
    (a b : Real) :
    mixedStageInformation r (radialTangentMass a b)
      (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial) =
      a • blochOuter frame.tangentFirst +
      a • blochOuter frame.tangentSecond +
      (b / (1 - blochNormSq r)) • blochOuter frame.radial := by
  rw [mixedStageInformation_radialTangent_expand]
  rw [mixedAxisFisher_eq_outer_of_orthogonal r frame.tangentFirst
      frame.tangentFirst_orthogonal,
    mixedAxisFisher_eq_outer_of_orthogonal r frame.tangentSecond
      frame.tangentSecond_orthogonal,
    mixedAxisFisher_eq_radial_of_dot_sq r frame.radial frame.radial_dot_sq]
  rw [smul_smul]
  congr 2

/-- The two tangent outer products equal the tangent-plane projector away
from the center; their individual rotation is irrelevant. -/
theorem tangentOuter_sum_eq_mixedTangentProjector
    (r : Fin 3 -> Real) (frame : MixedRadialTangentFrame r)
    (hr0 : blochNormSq r ≠ 0) :
    blochOuter frame.tangentFirst + blochOuter frame.tangentSecond =
      mixedTangentProjector r := by
  rw [mixedTangentProjector, ← frame.radial_outer_of_nonzero hr0]
  have hres := frame.resolution
  exact eq_sub_of_add_eq hres

/-- Frobenius/trace radial-tangent stages realize the center-safe target at
the controller, including at the center. -/
theorem mixedStageInformation_frobeniusTrace_exact
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1)
    (frame : MixedRadialTangentFrame r) :
    mixedStageInformation r
      (radialTangentMass (mixedCoherenceAllocation r)
        (mixedRadialAllocation r))
      (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial) =
      mixedFrobeniusTraceTarget r := by
  rw [mixedStageInformation_radialTangent_eq_projectors]
  by_cases hr0 : blochNormSq r = 0
  · have hgap : mixedRadialGap r = 1 := by
      unfold mixedRadialGap
      rw [hr0]
      norm_num
    have ha : mixedCoherenceAllocation r = 1 / 3 := by
      rw [mixedCoherenceAllocation, hgap]
      norm_num
    have hb : mixedRadialAllocation r = 1 / 3 := by
      rw [mixedRadialAllocation, hgap]
      norm_num
    have htarget : mixedFrobeniusTraceTarget r =
        (1 / 3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) := by
      have router : blochOuter r = 0 := by
        have rr : r = 0 := by
          apply funext
          intro i
          have hi : r i ^ 2 <= blochNormSq r := by
            unfold blochNormSq
            exact Finset.single_le_sum (fun j _ => sq_nonneg (r j))
              (Finset.mem_univ i)
          rw [hr0] at hi
          simp only [Pi.zero_apply]
          nlinarith [sq_nonneg (r i)]
        rw [rr]
        ext i j
        simp [blochOuter]
      rw [mixedFrobeniusTraceTarget]
      simp [hgap, router]
      norm_num
    rw [ha, hb, hr0, sub_zero, div_one, htarget]
    rw [← smul_add, ← smul_add, frame.resolution]
  · have hr0pos : 0 < blochNormSq r := by
      have hnonneg : 0 <= blochNormSq r :=
        Finset.sum_nonneg fun i _ => sq_nonneg (r i)
      exact lt_of_le_of_ne hnonneg (Ne.symm hr0)
    rw [← smul_add]
    rw [tangentOuter_sum_eq_mixedTangentProjector r frame hr0,
      frame.radial_outer_of_nonzero hr0]
    exact (mixedFrobeniusTraceTarget_eq_radialTangent
      r hr0pos hr).symm

/-- Bures radial-tangent stages realize the center-safe Bures target at the
controller, including at the center. -/
theorem mixedStageInformation_bures_exact
    (r : Fin 3 -> Real) (hr : blochNormSq r < 1)
    (frame : MixedRadialTangentFrame r) :
    mixedStageInformation r
      (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
      (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial) =
      mixedBuresTarget r := by
  rw [mixedStageInformation_radialTangent_eq_projectors]
  by_cases hr0 : blochNormSq r = 0
  · have router : blochOuter r = 0 := by
      have rr : r = 0 := by
        apply funext
        intro i
        have hi : r i ^ 2 <= blochNormSq r := by
          unfold blochNormSq
          exact Finset.single_le_sum (fun j _ => sq_nonneg (r j))
            (Finset.mem_univ i)
        rw [hr0] at hi
        simp only [Pi.zero_apply]
        nlinarith [sq_nonneg (r i)]
      rw [rr]
      ext i j
      simp [blochOuter]
    have htarget : mixedBuresTarget r =
        (1 / 3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) := by
      simp [mixedBuresTarget, hr0, router]
    rw [hr0, sub_zero, div_one, htarget]
    rw [← smul_add, ← smul_add, frame.resolution]
  · have hr0pos : 0 < blochNormSq r := by
      have hnonneg : 0 <= blochNormSq r :=
        Finset.sum_nonneg fun i _ => sq_nonneg (r i)
      exact lt_of_le_of_ne hnonneg (Ne.symm hr0)
    rw [← smul_add]
    rw [tangentOuter_sum_eq_mixedTangentProjector r frame hr0,
      frame.radial_outer_of_nonzero hr0]
    exact (mixedBuresTarget_eq_radialTangent r hr0pos hr).symm

/-- The manuscript's Frobenius/trace exploitation information converges at
the truth. The tangent pair may rotate arbitrarily from stage to stage. -/
theorem mixedFrobeniusTraceStage_tendsto
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (hcontrollerInterior : ∀ n, blochNormSq (controller n) < 1)
    (frame : ∀ n, MixedRadialTangentFrame (controller n)) :
    Tendsto
      (fun n => mixedStageInformation theta
        (radialTangentMass
          (mixedCoherenceAllocation (controller n))
          (mixedRadialAllocation (controller n)))
        (radialTangentAxes (frame n).tangentFirst
          (frame n).tangentSecond (frame n).radial))
      atTop (nhds (mixedFrobeniusTraceTarget theta)) := by
  apply mixedStageInformation_tendsto_of_exact_continuous_target
    theta htheta controller hcontroller
      (fun n => radialTangentMass
        (mixedCoherenceAllocation (controller n))
        (mixedRadialAllocation (controller n)))
      (fun n => radialTangentAxes (frame n).tangentFirst
        (frame n).tangentSecond (frame n).radial)
  · intro n m
    exact radialTangentMass_nonnegative _ _
      (mixedCoherenceAllocation_pos
        (controller n) (hcontrollerInterior n)).le
      (mixedRadialAllocation_pos
        (controller n) (hcontrollerInterior n)).le m
  · intro n
    exact radialTangentMass_sum _ _
      (mixedAllocations_sum (controller n) (hcontrollerInterior n))
  · intro n
    exact radialTangentAxes_unit (controller n) (frame n)
  · exact continuousAt_mixedFrobeniusTraceTarget theta htheta
  · intro n
    exact mixedStageInformation_frobeniusTrace_exact
      (controller n) (hcontrollerInterior n) (frame n)

/-- The manuscript's equal-allocation Bures exploitation information
converges at the truth, without choosing a convergent tangent frame. -/
theorem mixedBuresStage_tendsto
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (hcontrollerInterior : ∀ n, blochNormSq (controller n) < 1)
    (frame : ∀ n, MixedRadialTangentFrame (controller n)) :
    Tendsto
      (fun n => mixedStageInformation theta
        (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
        (radialTangentAxes (frame n).tangentFirst
          (frame n).tangentSecond (frame n).radial))
      atTop (nhds (mixedBuresTarget theta)) := by
  apply mixedStageInformation_tendsto_of_exact_continuous_target
    theta htheta controller hcontroller
      (fun _ => radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
      (fun n => radialTangentAxes (frame n).tangentFirst
        (frame n).tangentSecond (frame n).radial)
  · intro n m
    exact radialTangentMass_nonnegative _ _ (by norm_num) (by norm_num) m
  · intro n
    exact radialTangentMass_sum _ _ (by norm_num)
  · intro n
    exact radialTangentAxes_unit (controller n) (frame n)
  · exact continuousAt_mixedBuresTarget theta htheta
  · intro n
    exact mixedStageInformation_bures_exact
      (controller n) (hcontrollerInterior n) (frame n)

namespace Label

/-- Canonical Lean support for `lem:SI_mixed_stage`: both rotationally
invariant mixed-state oracle designs converge independently of tangent-frame
rotations. -/
theorem lem_SI_mixed_stage
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1)
    (controller : Nat -> Fin 3 -> Real)
    (hcontroller : Tendsto controller atTop (nhds theta))
    (hcontrollerInterior : ∀ n, blochNormSq (controller n) < 1)
    (frame : ∀ n, MixedRadialTangentFrame (controller n)) :
    Tendsto
      (fun n => mixedStageInformation theta
        (radialTangentMass
          (mixedCoherenceAllocation (controller n))
          (mixedRadialAllocation (controller n)))
        (radialTangentAxes (frame n).tangentFirst
          (frame n).tangentSecond (frame n).radial))
      atTop (nhds (mixedFrobeniusTraceTarget theta)) ∧
    Tendsto
      (fun n => mixedStageInformation theta
        (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
        (radialTangentAxes (frame n).tangentFirst
          (frame n).tangentSecond (frame n).radial))
      atTop (nhds (mixedBuresTarget theta)) := by
  exact ⟨
    mixedFrobeniusTraceStage_tendsto theta htheta controller hcontroller
      hcontrollerInterior frame,
    mixedBuresStage_tendsto theta htheta controller hcontroller
      hcontrollerInterior frame⟩

end Label

end Paper
end QubitOracle
