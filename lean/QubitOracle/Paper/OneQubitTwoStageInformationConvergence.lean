import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.OneQubitFixedDesignInformation
import QubitOracle.Paper.OneQubitRotationTransport
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Truth-aligned frames and the pilot contract -/

/-- The `k`th physical axis represented by the `k`th column of a frame. -/
def qubitFrameAxis
    (R : Matrix (Fin 3) (Fin 3) Real) (k : Fin 3) : Fin 3 -> Real :=
  fun i => R i k

/-- The Householder frame aligned with a chosen unit truth direction.  Its
columns are the physical axes obtained by transporting the north-pole Pauli
frame back to the original Bloch coordinates. -/
def qubitTruthAlignedHouseholderFrame
    (truthDirection : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun i k =>
    qubitHouseholderToNorth truthDirection
      (qubitPauliCoordinateAxis k) i

theorem qubitTruthAlignedHouseholderFrame_axis
    (truthDirection : Fin 3 -> Real) (k : Fin 3) :
    qubitFrameAxis (qubitTruthAlignedHouseholderFrame truthDirection) k =
      qubitHouseholderToNorth truthDirection
        (qubitPauliCoordinateAxis k) := by
  rfl

theorem qubitTruthAlignedHouseholderFrame_axis_normSq
    (truthDirection : Fin 3 -> Real) (k : Fin 3) :
    blochNormSq
        (qubitFrameAxis
          (qubitTruthAlignedHouseholderFrame truthDirection) k) = 1 := by
  rw [qubitTruthAlignedHouseholderFrame_axis,
    qubitHouseholderToNorth_normSq_preserved,
    qubitPauliCoordinateAxis_normSq]

/-- Deterministic output of the pilot controller.  Each estimate is an
orthonormal frame, and every matrix entry converges to the truth-aligned
Householder frame. -/
structure QubitPilotFrameConvergence
    (truthDirection : Fin 3 -> Real) where
  estimatedFrame : Nat -> Matrix (Fin 3) (Fin 3) Real
  axis_unit : ∀ n k,
    blochNormSq (qubitFrameAxis (estimatedFrame n) k) = 1
  axes_orthogonal : ∀ n k l,
    blochDot (qubitFrameAxis (estimatedFrame n) k)
        (qubitFrameAxis (estimatedFrame n) l) =
      if k = l then 1 else 0
  entry_tendsto : ∀ i k,
    Tendsto (fun n => estimatedFrame n i k) atTop
      (nhds (qubitTruthAlignedHouseholderFrame truthDirection i k))

/-- Coordinatewise frame convergence implies convergence of every dot
product with a fixed Bloch vector. -/
theorem qubitFrameAxis_dot_tendsto
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (x : Fin 3 -> Real) (k : Fin 3) :
    Tendsto
      (fun n => blochDot (qubitFrameAxis (pilot.estimatedFrame n) k) x)
      atTop
      (nhds (blochDot
        (qubitFrameAxis
          (qubitTruthAlignedHouseholderFrame truthDirection) k) x)) := by
  have h0 := Tendsto.mul_const (x (0 : Fin 3))
    (pilot.entry_tendsto (0 : Fin 3) k)
  have h1 := Tendsto.mul_const (x (1 : Fin 3))
    (pilot.entry_tendsto (1 : Fin 3) k)
  have h2 := Tendsto.mul_const (x (2 : Fin 3))
    (pilot.entry_tendsto (2 : Fin 3) k)
  simpa [blochDot, qubitFrameAxis, Fin.sum_univ_succ] using
    h0.add (h1.add h2)

/-- Coordinates of a Bloch vector in a controller frame. -/
def qubitFrameCoordinates
    (R : Matrix (Fin 3) (Fin 3) Real) (x : Fin 3 -> Real) :
    Fin 3 -> Real :=
  fun k => blochDot (qubitFrameAxis R k) x

theorem qubitFrameCoordinates_tendsto
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (x : Fin 3 -> Real) (k : Fin 3) :
    Tendsto
      (fun n => qubitFrameCoordinates (pilot.estimatedFrame n) x k)
      atTop
      (nhds (qubitFrameCoordinates
        (qubitTruthAlignedHouseholderFrame truthDirection) x k)) :=
  qubitFrameAxis_dot_tendsto pilot x k

/-! ## Mixed complete rotated Pauli blocks -/

/-- The mixed complete-block Fisher matrix expressed in the moving controller
coordinates.  The clean fixed-design module has already computed this matrix
exactly. -/
def mixedRotatedPauliCompleteBlockFisher
    (theta : Fin 3 -> Real) (R : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  mixedPauliCompleteBlockFisher (qubitFrameCoordinates R theta)

/-- Entrywise convergence of one complete rotated mixed block.  The interior
Bloch premise makes the limiting Bernoulli denominator nonzero; final
information convergence is not assumed. -/
theorem mixedRotatedPauliCompleteBlockFisher_entry_tendsto
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (theta : Fin 3 -> Real) (hInterior : blochNormSq theta < 1)
    (i j : Fin 3) :
    Tendsto
      (fun n => mixedRotatedPauliCompleteBlockFisher
        theta (pilot.estimatedFrame n) i j)
      atTop
      (nhds (mixedRotatedPauliCompleteBlockFisher theta
        (qubitTruthAlignedHouseholderFrame truthDirection) i j)) := by
  by_cases hij : i = j
  · subst j
    have hcoordinate := qubitFrameCoordinates_tendsto pilot theta i
    have hdenominator :=
      Tendsto.const_sub (1 : Real) (hcoordinate.pow 2)
    have hpositive :
        0 < 1 -
          qubitFrameCoordinates
            (qubitTruthAlignedHouseholderFrame truthDirection) theta i ^ 2 := by
      simpa [qubitFrameCoordinates, blochDot_directional_comm] using
        (QubitOracle.mixedAxisFisher_denominator_pos theta
          (qubitFrameAxis
            (qubitTruthAlignedHouseholderFrame truthDirection) i)
          hInterior
          (qubitTruthAlignedHouseholderFrame_axis_normSq truthDirection i))
    have hinverse := hdenominator.inv₀ (ne_of_gt hpositive)
    simpa [mixedRotatedPauliCompleteBlockFisher,
      mixedPauliCompleteBlockFisher_apply] using hinverse
  · simp [mixedRotatedPauliCompleteBlockFisher,
      mixedPauliCompleteBlockFisher_apply, hij]

/-- Matrix convergence follows from the nine entrywise limits. -/
theorem mixedRotatedPauliCompleteBlockFisher_tendsto
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (theta : Fin 3 -> Real) (hInterior : blochNormSq theta < 1) :
    Tendsto
      (fun n => mixedRotatedPauliCompleteBlockFisher
        theta (pilot.estimatedFrame n))
      atTop
      (nhds (mixedRotatedPauliCompleteBlockFisher theta
        (qubitTruthAlignedHouseholderFrame truthDirection))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact mixedRotatedPauliCompleteBlockFisher_entry_tendsto
    pilot theta hInterior i j

/-- Convergence of the mixed per-observation block information. -/
theorem mixedRotatedPauliPerObservationInformation_tendsto
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (theta : Fin 3 -> Real) (hInterior : blochNormSq theta < 1) :
    Tendsto
      (fun n => (1 / 3 : Real) •
        mixedRotatedPauliCompleteBlockFisher
          theta (pilot.estimatedFrame n))
      atTop
      (nhds ((1 / 3 : Real) •
        mixedRotatedPauliCompleteBlockFisher theta
          (qubitTruthAlignedHouseholderFrame truthDirection))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  simpa only [Matrix.smul_apply, smul_eq_mul] using
    Tendsto.const_mul (1 / 3 : Real)
      (mixedRotatedPauliCompleteBlockFisher_entry_tendsto
        pilot theta hInterior i j)

/-- Exact limiting mixed oracle entry, reusing the fixed-design calculation. -/
theorem mixedRotatedPauliOraclePerObservationInformation_apply
    (truthDirection theta : Fin 3 -> Real) (i j : Fin 3) :
    ((1 / 3 : Real) • mixedRotatedPauliCompleteBlockFisher theta
      (qubitTruthAlignedHouseholderFrame truthDirection)) i j =
      if i = j then
        (3 * (1 -
          qubitFrameCoordinates
            (qubitTruthAlignedHouseholderFrame truthDirection) theta i ^ 2))⁻¹
      else 0 := by
  exact mixedPauliPerObservationInformation_apply
    (qubitFrameCoordinates
      (qubitTruthAlignedHouseholderFrame truthDirection) theta) i j

/-! ## Pure two-axis rotated tangent blocks -/

/-- The first two columns of the truth-aligned frame are exactly the two
transported tangent axes used by the clean fixed-design module. -/
theorem qubitTruthAlignedHouseholderFrame_finTwo_axis
    (r : Fin 3 -> Real) (k : Fin 2) :
    qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) k.castSucc =
      pureTruthTangentCoordinateAxis r k := by
  rw [qubitTruthAlignedHouseholderFrame_axis]
  unfold pureTruthTangentCoordinateAxis
  apply congrArg (qubitHouseholderToNorth r)
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [qubitPauliCoordinateAxis, pureNorthTangentCoordinateAxis]

/-- Dot products of the transported truth-tangent coordinate axes. -/
theorem pureTruthTangentCoordinateAxis_dot
    (r : Fin 3 -> Real) (k i : Fin 2) :
    blochDot (pureTruthTangentCoordinateAxis r k)
        (pureTruthTangentCoordinateAxis r i) =
      if k = i then 1 else 0 := by
  calc
    blochDot (pureTruthTangentCoordinateAxis r k)
        (pureTruthTangentCoordinateAxis r i) =
      blochDot
        (qubitHouseholderToNorth r
          (pureTruthTangentCoordinateAxis r k))
        (qubitHouseholderToNorth r
          (pureTruthTangentCoordinateAxis r i)) :=
        (qubitHouseholderToNorth_dot_preserved r
          (pureTruthTangentCoordinateAxis r k)
          (pureTruthTangentCoordinateAxis r i)).symm
    _ = blochDot (pureNorthTangentCoordinateAxis k)
        (pureNorthTangentCoordinateAxis i) := by
      rw [pureTruthTangentCoordinateAxis_toNorth,
        pureTruthTangentCoordinateAxis_toNorth]
    _ = if k = i then 1 else 0 := by
      fin_cases k <;> fin_cases i <;>
        simp [pureNorthTangentCoordinateAxis, blochDot,
          Fin.sum_univ_succ]

/-- Fisher matrix of one approximately transported tangent-axis measurement,
written in the exact truth-tangent local coordinates.  At the oracle frame
this reduces to the source-computed pure Fisher matrix. -/
def pureRotatedTangentAxisFisher
    (r : Fin 3 -> Real) (R : Matrix (Fin 3) (Fin 3) Real)
    (k i j : Fin 2) : Real :=
  4 * blochDot (qubitFrameAxis R k.castSucc)
        (pureTruthTangentCoordinateAxis r i) *
      blochDot (qubitFrameAxis R k.castSucc)
        (pureTruthTangentCoordinateAxis r j) *
      (1 - blochDot (qubitFrameAxis R k.castSucc) r ^ 2)⁻¹

/-- Complete approximate two-axis tangent block. -/
def pureRotatedTangentCompleteBlockFisher
    (r : Fin 3 -> Real) (R : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 2) (Fin 2) Real :=
  fun i j => ∑ k : Fin 2, pureRotatedTangentAxisFisher r R k i j

theorem pureRotatedTangentAxisFisher_tendsto
    {r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1)
    (pilot : QubitPilotFrameConvergence r) (k i j : Fin 2) :
    Tendsto
      (fun n => pureRotatedTangentAxisFisher
        r (pilot.estimatedFrame n) k i j)
      atTop
      (nhds (pureRotatedTangentAxisFisher r
        (qubitTruthAlignedHouseholderFrame r) k i j)) := by
  have hi := qubitFrameAxis_dot_tendsto pilot
    (pureTruthTangentCoordinateAxis r i) k.castSucc
  have hj := qubitFrameAxis_dot_tendsto pilot
    (pureTruthTangentCoordinateAxis r j) k.castSucc
  have hr := qubitFrameAxis_dot_tendsto pilot r k.castSucc
  have hdenominator := Tendsto.const_sub (1 : Real) (hr.pow 2)
  have htangent :
      blochDot
          (qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) k.castSucc) r =
        0 := by
    rw [qubitTruthAlignedHouseholderFrame_finTwo_axis]
    exact pureTruthTangentCoordinateAxis_tangent r k hTruthUnit
  have hne :
      1 -
          blochDot
            (qubitFrameAxis
              (qubitTruthAlignedHouseholderFrame r) k.castSucc) r ^ 2 ≠ 0 := by
    rw [htangent]
    norm_num
  have hinverse := hdenominator.inv₀ hne
  simpa only [pureRotatedTangentAxisFisher] using
    (((tendsto_const_nhds.mul hi).mul hj).mul hinverse)

theorem pureRotatedTangentCompleteBlockFisher_entry_tendsto
    {r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1)
    (pilot : QubitPilotFrameConvergence r) (i j : Fin 2) :
    Tendsto
      (fun n => pureRotatedTangentCompleteBlockFisher
        r (pilot.estimatedFrame n) i j)
      atTop
      (nhds (pureRotatedTangentCompleteBlockFisher r
        (qubitTruthAlignedHouseholderFrame r) i j)) := by
  unfold pureRotatedTangentCompleteBlockFisher
  apply tendsto_finset_sum
  intro k _
  exact pureRotatedTangentAxisFisher_tendsto hTruthUnit pilot k i j

theorem pureRotatedTangentCompleteBlockFisher_tendsto
    {r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1)
    (pilot : QubitPilotFrameConvergence r) :
    Tendsto
      (fun n => pureRotatedTangentCompleteBlockFisher
        r (pilot.estimatedFrame n))
      atTop
      (nhds (pureRotatedTangentCompleteBlockFisher r
        (qubitTruthAlignedHouseholderFrame r))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact pureRotatedTangentCompleteBlockFisher_entry_tendsto
    hTruthUnit pilot i j




/-! ## Explicit two-stage schedules -/

/-- A count normalized by the total sample index.  Its value at `n = 0` is
irrelevant to the `atTop` statements. -/
def normalizedStageCount (count : Nat -> Nat) (n : Nat) : Real :=
  (count n : Real) / (n : Real)

/-- Mixed schedule: the pilot is `o(n)`, complete three-observation blocks
consume asymptotically all observations, and every finite-stage budget is
explicit. -/
structure MixedQubitTwoStageSchedule where
  pilotCount : Nat -> Nat
  completeBlocks : Nat -> Nat
  budget : ∀ n, pilotCount n + 3 * completeBlocks n <= n
  pilot_fraction_tendsto_zero :
    Tendsto (normalizedStageCount pilotCount) atTop (nhds 0)
  block_fraction_tendsto_one_third :
    Tendsto (normalizedStageCount completeBlocks) atTop
      (nhds (1 / 3 : Real))

/-- Pure schedule with complete two-observation tangent blocks. -/
structure PureQubitTwoStageSchedule where
  pilotCount : Nat -> Nat
  completeBlocks : Nat -> Nat
  budget : ∀ n, pilotCount n + 2 * completeBlocks n <= n
  pilot_fraction_tendsto_zero :
    Tendsto (normalizedStageCount pilotCount) atTop (nhds 0)
  block_fraction_tendsto_one_half :
    Tendsto (normalizedStageCount completeBlocks) atTop
      (nhds (1 / 2 : Real))

/-! ## Pilot removal and normalized information limits -/

/-- Normalized predictable mixed information.  `pilotPerObservation` is a
fixed finite pilot information matrix; multiplying it by an `o(n)` fraction
makes its normalized contribution vanish. -/
def mixedTwoStageNormalizedInformation
    (schedule : MixedQubitTwoStageSchedule)
    (pilotPerObservation : Matrix (Fin 3) (Fin 3) Real)
    (theta : Fin 3 -> Real)
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (n : Nat) : Matrix (Fin 3) (Fin 3) Real :=
  normalizedStageCount schedule.pilotCount n • pilotPerObservation +
    normalizedStageCount schedule.completeBlocks n •
      mixedRotatedPauliCompleteBlockFisher
        theta (pilot.estimatedFrame n)

theorem mixedTwoStageNormalizedInformation_entry_tendsto
    (schedule : MixedQubitTwoStageSchedule)
    (pilotPerObservation : Matrix (Fin 3) (Fin 3) Real)
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (theta : Fin 3 -> Real) (hInterior : blochNormSq theta < 1)
    (i j : Fin 3) :
    Tendsto
      (fun n => mixedTwoStageNormalizedInformation
        schedule pilotPerObservation theta pilot n i j)
      atTop
      (nhds (((1 / 3 : Real) •
        mixedRotatedPauliCompleteBlockFisher theta
          (qubitTruthAlignedHouseholderFrame truthDirection)) i j)) := by
  have hpilot := Tendsto.mul_const (pilotPerObservation i j)
    schedule.pilot_fraction_tendsto_zero
  have hmain := schedule.block_fraction_tendsto_one_third.mul
    (mixedRotatedPauliCompleteBlockFisher_entry_tendsto
      pilot theta hInterior i j)
  simpa [mixedTwoStageNormalizedInformation,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    hpilot.add hmain

/-- The `o(n)` pilot fraction does not change the mixed normalized matrix
limit. -/
theorem mixedTwoStageNormalizedInformation_tendsto
    (schedule : MixedQubitTwoStageSchedule)
    (pilotPerObservation : Matrix (Fin 3) (Fin 3) Real)
    {truthDirection : Fin 3 -> Real}
    (pilot : QubitPilotFrameConvergence truthDirection)
    (theta : Fin 3 -> Real) (hInterior : blochNormSq theta < 1) :
    Tendsto
      (fun n => mixedTwoStageNormalizedInformation
        schedule pilotPerObservation theta pilot n)
      atTop
      (nhds ((1 / 3 : Real) •
        mixedRotatedPauliCompleteBlockFisher theta
          (qubitTruthAlignedHouseholderFrame truthDirection))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact mixedTwoStageNormalizedInformation_entry_tendsto
    schedule pilotPerObservation pilot theta hInterior i j

/-- Normalized predictable pure information with a fixed finite pilot
information matrix. -/
def pureTwoStageNormalizedInformation
    (schedule : PureQubitTwoStageSchedule)
    (pilotPerObservation : Matrix (Fin 2) (Fin 2) Real)
    (r : Fin 3 -> Real) (pilot : QubitPilotFrameConvergence r)
    (n : Nat) : Matrix (Fin 2) (Fin 2) Real :=
  normalizedStageCount schedule.pilotCount n • pilotPerObservation +
    normalizedStageCount schedule.completeBlocks n •
      pureRotatedTangentCompleteBlockFisher r (pilot.estimatedFrame n)



namespace Label


end Label

end

end QubitOracle.Paper
