import QubitOracle.Paper.OneQubitRotationTransport
import QubitOracle.Paper.OneQubitTwoStageInformationConvergence

/-!
# A local continuous orthonormal frame for a qubit truth direction

Fix a unit truth direction `r` and a seed `b` that is not parallel to `r`.
For a nearby estimate `x`, this file constructs

1. the normalized radial direction `u(x)`,
2. the normalized Gram--Schmidt residual of `b` against `u(x)`,
3. the concrete three-dimensional cross product of the radial and first
   tangent directions.

The local domain exposes both denominators explicitly: `x` must be nonzero
and the Gram--Schmidt residual must be nonzero.  The moving frame never uses
the Householder formula.  A fixed orthogonal change of tangent coordinates,
computed once at the truth, relates its limit to the oracle frame required by
`QubitPilotFrameConvergence`.
-/

namespace QubitOracle.Paper

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Euclidean normalization and Gram--Schmidt -/

/-- Euclidean normalization in explicit Bloch coordinates. -/
def localNormalizedBlochDirection (x : Fin 3 -> Real) : Fin 3 -> Real :=
  fun i => x i / Real.sqrt (blochNormSq x)

/-- Gram--Schmidt residual of the fixed seed against the normalized radial
direction. -/
def localFrameFirstResidual
    (b x : Fin 3 -> Real) : Fin 3 -> Real :=
  fun i =>
    b i - blochDot b (localNormalizedBlochDirection x) *
      localNormalizedBlochDirection x i

/-- First normalized tangent direction. -/
def localFrameFirstTangent
    (b x : Fin 3 -> Real) : Fin 3 -> Real :=
  localNormalizedBlochDirection (localFrameFirstResidual b x)

/-- Concrete right-handed cross product on `Fin 3`. -/
def qubitCrossProduct
    (a b : Fin 3 -> Real) : Fin 3 -> Real :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

/-- Second tangent direction, with orientation fixed by the concrete cross
product. -/
def localFrameSecondTangent
    (b x : Fin 3 -> Real) : Fin 3 -> Real :=
  qubitCrossProduct (localNormalizedBlochDirection x)
    (localFrameFirstTangent b x)

/-- The explicit local denominator and nonparallel assumptions. -/
structure LocalContinuousFrameDomain
    (b x : Fin 3 -> Real) : Prop where
  radial_denominator_pos : 0 < blochNormSq x
  tangent_denominator_pos : 0 < blochNormSq (localFrameFirstResidual b x)

/-- A seed is nonparallel to the unit truth precisely when its truth-level
Gram--Schmidt residual has positive squared norm. -/
def LocalFrameSeedNonparallelAt
    (b r : Fin 3 -> Real) : Prop :=
  0 < blochNormSq (localFrameFirstResidual b r)

theorem blochDot_self_eq_blochNormSq (x : Fin 3 -> Real) :
    blochDot x x = blochNormSq x := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

theorem blochDot_comm_localFrame (x y : Fin 3 -> Real) :
    blochDot x y = blochDot y x := by
  simp [blochDot, Fin.sum_univ_succ]
  ring

theorem localNormalizedBlochDirection_normSq
    {x : Fin 3 -> Real} (hx : 0 < blochNormSq x) :
    blochNormSq (localNormalizedBlochDirection x) = 1 := by
  have hxsum : 0 < ∑ i : Fin 3, x i ^ 2 := by
    simpa [blochNormSq] using hx
  unfold localNormalizedBlochDirection blochNormSq
  simp_rw [div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt hxsum.le]
  exact div_self hxsum.ne'

theorem localNormalizedBlochDirection_dot_self
    {x : Fin 3 -> Real} (hx : 0 < blochNormSq x) :
    blochDot (localNormalizedBlochDirection x)
        (localNormalizedBlochDirection x) = 1 := by
  rw [blochDot_self_eq_blochNormSq,
    localNormalizedBlochDirection_normSq hx]

theorem localFrameFirstResidual_dot_radial
    {b x : Fin 3 -> Real} (hx : 0 < blochNormSq x) :
    blochDot (localFrameFirstResidual b x)
        (localNormalizedBlochDirection x) = 0 := by
  have hu := localNormalizedBlochDirection_normSq hx
  calc
    blochDot (localFrameFirstResidual b x)
        (localNormalizedBlochDirection x) =
      blochDot b (localNormalizedBlochDirection x) -
        blochDot b (localNormalizedBlochDirection x) *
          blochNormSq (localNormalizedBlochDirection x) := by
            simp [localFrameFirstResidual, blochDot, blochNormSq,
              Fin.sum_univ_succ]
            ring
    _ = 0 := by rw [hu]; ring

theorem localFrameFirstTangent_normSq
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x) :
    blochNormSq (localFrameFirstTangent b x) = 1 := by
  exact localNormalizedBlochDirection_normSq
    hDomain.tangent_denominator_pos

theorem localFrameFirstTangent_dot_radial
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x) :
    blochDot (localFrameFirstTangent b x)
        (localNormalizedBlochDirection x) = 0 := by
  have hresidual := localFrameFirstResidual_dot_radial
    (b := b) hDomain.radial_denominator_pos
  calc
    blochDot (localFrameFirstTangent b x)
        (localNormalizedBlochDirection x) =
      blochDot (localFrameFirstResidual b x)
          (localNormalizedBlochDirection x) /
        Real.sqrt (blochNormSq (localFrameFirstResidual b x)) := by
          simp [localFrameFirstTangent, localNormalizedBlochDirection,
            blochDot, Fin.sum_univ_succ]
          ring
    _ = 0 := by rw [hresidual]; simp

/-! ## Cross-product algebra -/

theorem qubitCrossProduct_dot_left
    (a b : Fin 3 -> Real) :
    blochDot (qubitCrossProduct a b) a = 0 := by
  simp [qubitCrossProduct, blochDot, Fin.sum_univ_succ]
  ring

theorem qubitCrossProduct_dot_right
    (a b : Fin 3 -> Real) :
    blochDot (qubitCrossProduct a b) b = 0 := by
  simp [qubitCrossProduct, blochDot, Fin.sum_univ_succ]
  ring

/-- Lagrange's identity in the concrete three-dimensional coordinates. -/
theorem qubitCrossProduct_normSq
    (a b : Fin 3 -> Real) :
    blochNormSq (qubitCrossProduct a b) =
      blochNormSq a * blochNormSq b - blochDot a b ^ 2 := by
  simp [qubitCrossProduct, blochNormSq, blochDot,
    Fin.sum_univ_succ]
  ring

theorem localFrameSecondTangent_normSq
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x) :
    blochNormSq (localFrameSecondTangent b x) = 1 := by
  rw [localFrameSecondTangent, qubitCrossProduct_normSq,
    localNormalizedBlochDirection_normSq
      hDomain.radial_denominator_pos,
    localFrameFirstTangent_normSq hDomain]
  have horth := localFrameFirstTangent_dot_radial hDomain
  rw [blochDot_comm_localFrame] at horth
  rw [horth]
  norm_num

theorem localFrameSecondTangent_dot_radial
    (b x : Fin 3 -> Real) :
    blochDot (localFrameSecondTangent b x)
        (localNormalizedBlochDirection x) = 0 := by
  exact qubitCrossProduct_dot_left
    (localNormalizedBlochDirection x) (localFrameFirstTangent b x)

theorem localFrameSecondTangent_dot_first
    (b x : Fin 3 -> Real) :
    blochDot (localFrameSecondTangent b x)
        (localFrameFirstTangent b x) = 0 := by
  exact qubitCrossProduct_dot_right
    (localNormalizedBlochDirection x) (localFrameFirstTangent b x)

/-! ## The local orthonormal frame -/

/-- Columns are first tangent, second tangent, and radial direction. -/
def localContinuousQubitFrame
    (b x : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun i k =>
    if k = 0 then localFrameFirstTangent b x i
    else if k = 1 then localFrameSecondTangent b x i
    else localNormalizedBlochDirection x i

@[simp]
theorem localContinuousQubitFrame_axis_zero
    (b x : Fin 3 -> Real) :
    qubitFrameAxis (localContinuousQubitFrame b x) 0 =
      localFrameFirstTangent b x := by
  funext i
  simp [qubitFrameAxis, localContinuousQubitFrame]

@[simp]
theorem localContinuousQubitFrame_axis_one
    (b x : Fin 3 -> Real) :
    qubitFrameAxis (localContinuousQubitFrame b x) 1 =
      localFrameSecondTangent b x := by
  funext i
  simp [qubitFrameAxis, localContinuousQubitFrame]

@[simp]
theorem localContinuousQubitFrame_axis_two
    (b x : Fin 3 -> Real) :
    qubitFrameAxis (localContinuousQubitFrame b x) 2 =
      localNormalizedBlochDirection x := by
  funext i
  simp [qubitFrameAxis, localContinuousQubitFrame]

/-- The three local columns are orthonormal on the explicit domain. -/
theorem localContinuousQubitFrame_axes_orthogonal
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x)
    (k l : Fin 3) :
    blochDot (qubitFrameAxis (localContinuousQubitFrame b x) k)
        (qubitFrameAxis (localContinuousQubitFrame b x) l) =
      if k = l then 1 else 0 := by
  have ht1 :
      blochDot (localFrameFirstTangent b x)
          (localFrameFirstTangent b x) = 1 := by
    rw [blochDot_self_eq_blochNormSq,
      localFrameFirstTangent_normSq hDomain]
  have ht2 :
      blochDot (localFrameSecondTangent b x)
          (localFrameSecondTangent b x) = 1 := by
    rw [blochDot_self_eq_blochNormSq,
      localFrameSecondTangent_normSq hDomain]
  have hu :
      blochDot (localNormalizedBlochDirection x)
          (localNormalizedBlochDirection x) = 1 :=
    localNormalizedBlochDirection_dot_self
      hDomain.radial_denominator_pos
  have ht1u := localFrameFirstTangent_dot_radial hDomain
  have hut1 :
      blochDot (localNormalizedBlochDirection x)
          (localFrameFirstTangent b x) = 0 := by
    rw [blochDot_comm_localFrame]
    exact ht1u
  have ht2u := localFrameSecondTangent_dot_radial b x
  have hut2 :
      blochDot (localNormalizedBlochDirection x)
          (localFrameSecondTangent b x) = 0 := by
    rw [blochDot_comm_localFrame]
    exact ht2u
  have ht2t1 := localFrameSecondTangent_dot_first b x
  have ht1t2 :
      blochDot (localFrameFirstTangent b x)
          (localFrameSecondTangent b x) = 0 := by
    rw [blochDot_comm_localFrame]
    exact ht2t1
  fin_cases k <;> fin_cases l <;>
    simp [ht1, ht2, hu, ht1u, hut1, ht2u, hut2, ht2t1, ht1t2]

theorem localContinuousQubitFrame_axis_unit
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x)
    (k : Fin 3) :
    blochNormSq (qubitFrameAxis (localContinuousQubitFrame b x) k) = 1 := by
  have h := localContinuousQubitFrame_axes_orthogonal hDomain k k
  rw [if_pos rfl, blochDot_self_eq_blochNormSq] at h
  exact h

/-- Matrix form of column orthonormality. -/
theorem localContinuousQubitFrame_transpose_mul_self
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x) :
    (localContinuousQubitFrame b x).transpose *
        localContinuousQubitFrame b x = 1 := by
  ext k l
  have h := localContinuousQubitFrame_axes_orthogonal hDomain k l
  simpa [Matrix.mul_apply, Matrix.one_apply, qubitFrameAxis, blochDot] using h

/-- Since the frame is square, column orthonormality also gives row
orthonormality. -/
theorem localContinuousQubitFrame_mul_transpose_self
    {b x : Fin 3 -> Real} (hDomain : LocalContinuousFrameDomain b x) :
    localContinuousQubitFrame b x *
        (localContinuousQubitFrame b x).transpose = 1 := by
  exact mul_eq_one_comm.mp
    (localContinuousQubitFrame_transpose_mul_self hDomain)

/-! ## Truth domain and the fixed oracle coordinate change -/

theorem localContinuousFrameDomain_at_unit_truth
    {b r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r) :
    LocalContinuousFrameDomain b r := by
  exact ⟨by rw [hTruthUnit]; norm_num, hSeed⟩

theorem localNormalizedBlochDirection_unit_truth
    {r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1) :
    localNormalizedBlochDirection r = r := by
  funext i
  simp [localNormalizedBlochDirection, hTruthUnit]

theorem localContinuousQubitFrame_radial_axis_at_truth
    {b r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1) :
    qubitFrameAxis (localContinuousQubitFrame b r) 2 = r := by
  rw [localContinuousQubitFrame_axis_two,
    localNormalizedBlochDirection_unit_truth hTruthUnit]

theorem qubitTruthAlignedHouseholderFrame_radial_axis
    {r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1) :
    qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) 2 = r := by
  rw [qubitTruthAlignedHouseholderFrame_axis]
  have hmap := qubitHouseholderToNorth_maps_truth r hTruthUnit
  calc
    qubitHouseholderToNorth r (qubitPauliCoordinateAxis 2) =
        qubitHouseholderToNorth r directionalNorthPole := by
      congr 1
      funext i
      fin_cases i <;>
        simp [qubitPauliCoordinateAxis, directionalNorthPole]
    _ = qubitHouseholderToNorth r
        (qubitHouseholderToNorth r r) := by rw [hmap]
    _ = r := qubitHouseholderToNorth_involutive r r

theorem qubitPauliCoordinateAxes_dot (k l : Fin 3) :
    blochDot (qubitPauliCoordinateAxis k)
        (qubitPauliCoordinateAxis l) =
      if k = l then 1 else 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [qubitPauliCoordinateAxis, blochDot, Fin.sum_univ_succ]

theorem qubitTruthAlignedHouseholderFrame_axes_orthogonal
    (r : Fin 3 -> Real) (k l : Fin 3) :
    blochDot (qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) k)
        (qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) l) =
      if k = l then 1 else 0 := by
  rw [qubitTruthAlignedHouseholderFrame_axis,
    qubitTruthAlignedHouseholderFrame_axis,
    qubitHouseholderToNorth_dot_preserved,
    qubitPauliCoordinateAxes_dot]

theorem qubitTruthAlignedHouseholderFrame_transpose_mul_self
    (r : Fin 3 -> Real) :
    (qubitTruthAlignedHouseholderFrame r).transpose *
        qubitTruthAlignedHouseholderFrame r = 1 := by
  ext k l
  have h := qubitTruthAlignedHouseholderFrame_axes_orthogonal r k l
  simpa [Matrix.mul_apply, Matrix.one_apply, qubitFrameAxis, blochDot] using h

/-- Fixed orthogonal coordinate change from the continuous truth frame to the
project's oracle frame. -/
def localFrameToOracleChange
    (b r : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  (localContinuousQubitFrame b r).transpose *
    qubitTruthAlignedHouseholderFrame r

theorem localFrameToOracleChange_transpose_mul_self
    {b r : Fin 3 -> Real} (hTruthDomain : LocalContinuousFrameDomain b r) :
    (localFrameToOracleChange b r).transpose *
        localFrameToOracleChange b r = 1 := by
  have hLocalRows :=
    localContinuousQubitFrame_mul_transpose_self hTruthDomain
  have hOracleColumns :=
    qubitTruthAlignedHouseholderFrame_transpose_mul_self r
  calc
    (localFrameToOracleChange b r).transpose *
        localFrameToOracleChange b r =
      (qubitTruthAlignedHouseholderFrame r).transpose *
        (localContinuousQubitFrame b r *
          (localContinuousQubitFrame b r).transpose) *
        qubitTruthAlignedHouseholderFrame r := by
          simp [localFrameToOracleChange, Matrix.transpose_mul]
          noncomm_ring
    _ = (qubitTruthAlignedHouseholderFrame r).transpose *
        qubitTruthAlignedHouseholderFrame r := by rw [hLocalRows]; simp
    _ = 1 := hOracleColumns

/-- The moving local frame followed by the fixed truth-level coordinate
change.  Householder is not evaluated at `x`. -/
def oracleAlignedLocalContinuousFrame
    (b r x : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  localContinuousQubitFrame b x * localFrameToOracleChange b r

theorem oracleAlignedLocalContinuousFrame_at_truth
    {b r : Fin 3 -> Real} (hTruthDomain : LocalContinuousFrameDomain b r) :
    oracleAlignedLocalContinuousFrame b r r =
      qubitTruthAlignedHouseholderFrame r := by
  unfold oracleAlignedLocalContinuousFrame localFrameToOracleChange
  rw [← Matrix.mul_assoc,
    localContinuousQubitFrame_mul_transpose_self hTruthDomain]
  simp

theorem oracleAlignedLocalContinuousFrame_transpose_mul_self
    {b r x : Fin 3 -> Real}
    (hTruthDomain : LocalContinuousFrameDomain b r)
    (hDomain : LocalContinuousFrameDomain b x) :
    (oracleAlignedLocalContinuousFrame b r x).transpose *
        oracleAlignedLocalContinuousFrame b r x = 1 := by
  have hLocalColumns :=
    localContinuousQubitFrame_transpose_mul_self hDomain
  have hChangeColumns :=
    localFrameToOracleChange_transpose_mul_self hTruthDomain
  calc
    (oracleAlignedLocalContinuousFrame b r x).transpose *
        oracleAlignedLocalContinuousFrame b r x =
      (localFrameToOracleChange b r).transpose *
        ((localContinuousQubitFrame b x).transpose *
          localContinuousQubitFrame b x) *
        localFrameToOracleChange b r := by
          simp [oracleAlignedLocalContinuousFrame, Matrix.transpose_mul]
          noncomm_ring
    _ = (localFrameToOracleChange b r).transpose *
        localFrameToOracleChange b r := by rw [hLocalColumns]; simp
    _ = 1 := hChangeColumns

theorem oracleAlignedLocalContinuousFrame_axes_orthogonal
    {b r x : Fin 3 -> Real}
    (hTruthDomain : LocalContinuousFrameDomain b r)
    (hDomain : LocalContinuousFrameDomain b x) (k l : Fin 3) :
    blochDot (qubitFrameAxis (oracleAlignedLocalContinuousFrame b r x) k)
        (qubitFrameAxis (oracleAlignedLocalContinuousFrame b r x) l) =
      if k = l then 1 else 0 := by
  have hmatrix := oracleAlignedLocalContinuousFrame_transpose_mul_self
    hTruthDomain hDomain
  have happly := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) Real => M k l) hmatrix
  simpa [Matrix.mul_apply, Matrix.one_apply, qubitFrameAxis, blochDot] using happly

theorem oracleAlignedLocalContinuousFrame_axis_unit
    {b r x : Fin 3 -> Real}
    (hTruthDomain : LocalContinuousFrameDomain b r)
    (hDomain : LocalContinuousFrameDomain b x) (k : Fin 3) :
    blochNormSq
        (qubitFrameAxis (oracleAlignedLocalContinuousFrame b r x) k) = 1 := by
  have h := oracleAlignedLocalContinuousFrame_axes_orthogonal
    hTruthDomain hDomain k k
  rw [if_pos rfl, blochDot_self_eq_blochNormSq] at h
  exact h

/-- The fixed change does not mix the radial coordinate.  Thus its nontrivial
part is exactly a fixed orthogonal change of the two tangent coordinates. -/
theorem localFrameToOracleChange_radial_column
    {b r : Fin 3 -> Real} (hTruthUnit : blochNormSq r = 1)
    (hTruthDomain : LocalContinuousFrameDomain b r) (i : Fin 3) :
    localFrameToOracleChange b r i 2 =
      if i = 2 then 1 else 0 := by
  have hRadial :
      qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) 2 =
        qubitFrameAxis (localContinuousQubitFrame b r) 2 := by
    rw [qubitTruthAlignedHouseholderFrame_radial_axis hTruthUnit,
      localContinuousQubitFrame_radial_axis_at_truth hTruthUnit]
  have hdot := localContinuousQubitFrame_axes_orthogonal
    hTruthDomain i 2
  rw [localFrameToOracleChange, Matrix.mul_apply]
  change blochDot
      (qubitFrameAxis (localContinuousQubitFrame b r) i)
      (qubitFrameAxis (qubitTruthAlignedHouseholderFrame r) 2) =
    if i = 2 then 1 else 0
  rw [hRadial]
  exact hdot

/-! ## Coordinatewise continuity -/

theorem blochNormSq_tendsto_of_coordinatewise
    (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i))) :
    Tendsto (fun n => blochNormSq (x n)) atTop (nhds (blochNormSq r)) := by
  have h0 := (hx (0 : Fin 3)).pow 2
  have h1 := (hx (1 : Fin 3)).pow 2
  have h2 := (hx (2 : Fin 3)).pow 2
  simpa [blochNormSq, Fin.sum_univ_succ] using h0.add (h1.add h2)

theorem localNormalizedBlochDirection_entry_tendsto
    (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hr : 0 < blochNormSq r) (i : Fin 3) :
    Tendsto (fun n => localNormalizedBlochDirection (x n) i)
      atTop (nhds (localNormalizedBlochDirection r i)) := by
  have hnorm := blochNormSq_tendsto_of_coordinatewise x r hx
  have hsqrt :
      Tendsto (fun n => Real.sqrt (blochNormSq (x n))) atTop
        (nhds (Real.sqrt (blochNormSq r))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hnorm
  have hinverse := hsqrt.inv₀ (ne_of_gt (Real.sqrt_pos.2 hr))
  simpa [localNormalizedBlochDirection, div_eq_mul_inv] using
    (hx i).mul hinverse

theorem localFrameFirstResidual_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hr : 0 < blochNormSq r) (i : Fin 3) :
    Tendsto (fun n => localFrameFirstResidual b (x n) i)
      atTop (nhds (localFrameFirstResidual b r i)) := by
  have hu : ∀ j,
      Tendsto (fun n => localNormalizedBlochDirection (x n) j)
        atTop (nhds (localNormalizedBlochDirection r j)) :=
    fun j => localNormalizedBlochDirection_entry_tendsto x r hx hr j
  have hdot0 := Tendsto.const_mul (b (0 : Fin 3)) (hu (0 : Fin 3))
  have hdot1 := Tendsto.const_mul (b (1 : Fin 3)) (hu (1 : Fin 3))
  have hdot2 := Tendsto.const_mul (b (2 : Fin 3)) (hu (2 : Fin 3))
  have hdot :
    Tendsto
        (fun n => blochDot b (localNormalizedBlochDirection (x n)))
        atTop (nhds (blochDot b (localNormalizedBlochDirection r))) := by
    simpa [blochDot, Fin.sum_univ_succ] using
      hdot0.add (hdot1.add hdot2)
  simpa [localFrameFirstResidual] using
    Tendsto.const_sub (b i) (hdot.mul (hu i))

theorem localFrameFirstTangent_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hTruthDomain : LocalContinuousFrameDomain b r) (i : Fin 3) :
    Tendsto (fun n => localFrameFirstTangent b (x n) i)
      atTop (nhds (localFrameFirstTangent b r i)) := by
  apply localNormalizedBlochDirection_entry_tendsto
    (fun n => localFrameFirstResidual b (x n))
      (localFrameFirstResidual b r)
  · intro j
    exact localFrameFirstResidual_entry_tendsto b x r hx
      hTruthDomain.radial_denominator_pos j
  · exact hTruthDomain.tangent_denominator_pos

theorem localFrameSecondTangent_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hTruthDomain : LocalContinuousFrameDomain b r) (i : Fin 3) :
    Tendsto (fun n => localFrameSecondTangent b (x n) i)
      atTop (nhds (localFrameSecondTangent b r i)) := by
  have hu : ∀ j,
      Tendsto (fun n => localNormalizedBlochDirection (x n) j)
        atTop (nhds (localNormalizedBlochDirection r j)) :=
    fun j => localNormalizedBlochDirection_entry_tendsto x r hx
      hTruthDomain.radial_denominator_pos j
  have ht : ∀ j,
      Tendsto (fun n => localFrameFirstTangent b (x n) j)
        atTop (nhds (localFrameFirstTangent b r j)) :=
    fun j => localFrameFirstTangent_entry_tendsto b x r hx
      hTruthDomain j
  fin_cases i
  · simpa [localFrameSecondTangent, qubitCrossProduct] using
      (hu (1 : Fin 3)).mul (ht (2 : Fin 3)) |>.sub
        ((hu (2 : Fin 3)).mul (ht (1 : Fin 3)))
  · simpa [localFrameSecondTangent, qubitCrossProduct] using
      (hu (2 : Fin 3)).mul (ht (0 : Fin 3)) |>.sub
        ((hu (0 : Fin 3)).mul (ht (2 : Fin 3)))
  · simpa [localFrameSecondTangent, qubitCrossProduct] using
      (hu (0 : Fin 3)).mul (ht (1 : Fin 3)) |>.sub
        ((hu (1 : Fin 3)).mul (ht (0 : Fin 3)))

/-- Coordinatewise estimate convergence gives entrywise convergence of the
raw local frame. -/
theorem localContinuousQubitFrame_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hTruthDomain : LocalContinuousFrameDomain b r) (i k : Fin 3) :
    Tendsto (fun n => localContinuousQubitFrame b (x n) i k)
      atTop (nhds (localContinuousQubitFrame b r i k)) := by
  fin_cases k
  · simpa [localContinuousQubitFrame] using
      localFrameFirstTangent_entry_tendsto b x r hx hTruthDomain i
  · simpa [localContinuousQubitFrame] using
      localFrameSecondTangent_entry_tendsto b x r hx hTruthDomain i
  · simpa [localContinuousQubitFrame] using
      localNormalizedBlochDirection_entry_tendsto x r hx
        hTruthDomain.radial_denominator_pos i

theorem oracleAlignedLocalContinuousFrame_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hTruthDomain : LocalContinuousFrameDomain b r) (i k : Fin 3) :
    Tendsto (fun n => oracleAlignedLocalContinuousFrame b r (x n) i k)
      atTop (nhds (qubitTruthAlignedHouseholderFrame r i k)) := by
  have hraw :
      Tendsto (fun n => oracleAlignedLocalContinuousFrame b r (x n) i k)
        atTop (nhds (oracleAlignedLocalContinuousFrame b r r i k)) := by
    unfold oracleAlignedLocalContinuousFrame
    simp only [Matrix.mul_apply]
    apply tendsto_finset_sum
    intro j _
    exact (localContinuousQubitFrame_entry_tendsto
      b x r hx hTruthDomain i j).mul tendsto_const_nhds
  rw [oracleAlignedLocalContinuousFrame_at_truth hTruthDomain] at hraw
  exact hraw

/-! ## Eventual-domain safeguard and pilot packaging -/

/-- Outside the local domain use the fixed identity frame.  Eventually, the
controller uses only the continuous local construction. -/
noncomputable def safeguardedLocalContinuousControllerFrame
    (b r x : Fin 3 -> Real) : Matrix (Fin 3) (Fin 3) Real := by
  classical
  exact if LocalContinuousFrameDomain b x then
    oracleAlignedLocalContinuousFrame b r x
  else 1

theorem identityQubitFrame_axes_orthogonal (k l : Fin 3) :
    blochDot (qubitFrameAxis (1 : Matrix (Fin 3) (Fin 3) Real) k)
        (qubitFrameAxis (1 : Matrix (Fin 3) (Fin 3) Real) l) =
      if k = l then 1 else 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.one_apply, qubitFrameAxis, blochDot, Fin.sum_univ_succ]

theorem safeguardedLocalContinuousControllerFrame_axes_orthogonal
    {b r x : Fin 3 -> Real}
    (hTruthDomain : LocalContinuousFrameDomain b r) (k l : Fin 3) :
    blochDot
        (qubitFrameAxis
          (safeguardedLocalContinuousControllerFrame b r x) k)
        (qubitFrameAxis
          (safeguardedLocalContinuousControllerFrame b r x) l) =
      if k = l then 1 else 0 := by
  classical
  by_cases hDomain : LocalContinuousFrameDomain b x
  · simp [safeguardedLocalContinuousControllerFrame, hDomain,
      oracleAlignedLocalContinuousFrame_axes_orthogonal
        hTruthDomain hDomain]
  · simp [safeguardedLocalContinuousControllerFrame, hDomain,
      identityQubitFrame_axes_orthogonal]

theorem safeguardedLocalContinuousControllerFrame_axis_unit
    {b r x : Fin 3 -> Real}
    (hTruthDomain : LocalContinuousFrameDomain b r) (k : Fin 3) :
    blochNormSq
        (qubitFrameAxis
          (safeguardedLocalContinuousControllerFrame b r x) k) = 1 := by
  have h := safeguardedLocalContinuousControllerFrame_axes_orthogonal
    (b := b) (r := r) (x := x) hTruthDomain k k
  rw [if_pos rfl, blochDot_self_eq_blochNormSq] at h
  exact h

theorem safeguardedLocalContinuousControllerFrame_entry_tendsto
    (b : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real) (r : Fin 3 -> Real)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hTruthDomain : LocalContinuousFrameDomain b r)
    (hEventuallyDomain : ∀ᶠ n in atTop,
      LocalContinuousFrameDomain b (x n))
    (i k : Fin 3) :
    Tendsto
      (fun n => safeguardedLocalContinuousControllerFrame b r (x n) i k)
      atTop (nhds (qubitTruthAlignedHouseholderFrame r i k)) := by
  classical
  have hraw := oracleAlignedLocalContinuousFrame_entry_tendsto
    b x r hx hTruthDomain i k
  have heq :
      (fun n => oracleAlignedLocalContinuousFrame b r (x n) i k) =ᶠ[atTop]
        (fun n =>
          safeguardedLocalContinuousControllerFrame b r (x n) i k) := by
    filter_upwards [hEventuallyDomain] with n hn
    simp [safeguardedLocalContinuousControllerFrame, hn]
  exact hraw.congr' heq

/-- Package coordinatewise estimator convergence and eventual local-domain
membership into the exact deterministic pilot contract used by the two-stage
information theorem. -/
noncomputable def localContinuousFramePilot
    (b r : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real)
    (hTruthUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hEventuallyDomain : ∀ᶠ n in atTop,
      LocalContinuousFrameDomain b (x n)) :
    QubitPilotFrameConvergence r := by
  let hTruthDomain : LocalContinuousFrameDomain b r :=
    localContinuousFrameDomain_at_unit_truth hTruthUnit hSeed
  exact
    { estimatedFrame := fun n =>
        safeguardedLocalContinuousControllerFrame b r (x n)
      axis_unit := fun n k =>
        safeguardedLocalContinuousControllerFrame_axis_unit
          hTruthDomain k
      axes_orthogonal := fun n k l =>
        safeguardedLocalContinuousControllerFrame_axes_orthogonal
          hTruthDomain k l
      entry_tendsto := fun i k =>
        safeguardedLocalContinuousControllerFrame_entry_tendsto
          b x r hx hTruthDomain hEventuallyDomain i k }

namespace Label

/-- Honest local continuous-frame reduction.  The output is the existing
`QubitPilotFrameConvergence` contract; the premises are only a unit truth,
nonparallel seed, coordinatewise estimator convergence, and eventual
membership in the two-denominator local domain. -/
theorem lem_SI_local_continuous_frame_qubit_reduction
    (b r : Fin 3 -> Real) (x : Nat -> Fin 3 -> Real)
    (hTruthUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r)
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i)))
    (hEventuallyDomain : ∀ᶠ n in atTop,
      LocalContinuousFrameDomain b (x n)) :
    (LocalContinuousFrameDomain b r) ∧
      Nonempty (QubitPilotFrameConvergence r) := by
  exact ⟨localContinuousFrameDomain_at_unit_truth hTruthUnit hSeed,
    ⟨localContinuousFramePilot b r x hTruthUnit hSeed hx
      hEventuallyDomain⟩⟩

end Label

end

end QubitOracle.Paper
