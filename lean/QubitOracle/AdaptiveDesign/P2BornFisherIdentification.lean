import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.GlobalPFSICBorn

/-!
# The information in P2 is the Fisher information of its literal Born law

This bridge identifies both probabilities and derivatives. The fixed true
frame occurs only in the chart used to evaluate information; the implemented
measurement protocol and its ridge/pure estimators do not take that frame.
-/

namespace QubitOracle.AdaptiveDesign.P2Adaptive

open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController
open scoped BigOperators ComplexOrder

noncomputable section

theorem trace_frameProjector_mul {d : ℕ}
    (T E : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix.trace (frameProjector T * E) = (T.conjTranspose * E * T) 0 0 := by
  rw [Matrix.trace_mul_comm, frameProjector, trace_mul_projector]
  simp only [quadratic, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem transportedEffect_relativeFrame {d : ℕ}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : Outcome d) :
    T.conjTranspose * transportedEffect U o * T =
      transportedEffect (T.conjTranspose * U) o := by
  simp only [transportedEffect, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- The probabilities in the actual adaptive trajectory, evaluated at the
unknown pure state, equal the reference-chart masses used in `designFisher`. -/
theorem bornProbability_pure_eq_transportedMass {d : ℕ} (hd : 0 < d)
    (truth : PureVector d) (U : Action d) (o : Outcome d) :
    bornProbability hd (pureParameter d truth) U o =
      transportedMass ((trueFrame d truth).conjTranspose * U.matrix) o := by
  have h := congrArg Complex.re (bornProbability_eq_trace hd (pureParameter d truth) U o)
  change bornProbability hd (pureParameter d truth) U o =
    (Matrix.trace (rankOneDensity truth.val * transportedEffect U.matrix o)).re at h
  rw [← trueFrame_projector d truth, trace_frameProjector_mul,
    transportedEffect_relativeFrame] at h
  exact h

theorem basisBornAmplitude_transport {d : ℕ}
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (w psi : Fin (d+1) → ℂ) :
    basisBornAmplitude w (T.mulVec psi) =
      basisBornAmplitude (T.conjTranspose.mulVec w) psi := by
  change dotProduct (star w) (T.mulVec psi) =
    dotProduct (star (T.conjTranspose.mulVec w)) psi
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- A laboratory-state Born probability, expressed by its density matrix.
This definition uses the very same transported effects as the actual kernel. -/
def labChartProbability {d : ℕ}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : Outcome d) (x : TangentIndex d) (t : ℝ) : ℝ :=
  (Matrix.trace (rankOneDensity (T.mulVec (directionalState x t)) *
    transportedEffect U o)).re

theorem trace_rankOneDensity_transportedEffect {d : ℕ}
    (psi : Fin (d+1) → ℂ) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : Outcome d) :
    (Matrix.trace (rankOneDensity psi * transportedEffect U o)).re =
      effectWeight d * basisBornProbability (U.mulVec (measurementVector o)) psi := by
  rw [transportedEffect_projector, Matrix.mul_smul, Matrix.trace_smul]
  have h := basisBornProbability_eq_trace_rankOneDensity_mul_projector
    (U.mulVec (measurementVector o)) psi
  change (effectWeight d • Matrix.trace (rankOneDensity psi *
    rankOneBasisProjector (U.mulVec (measurementVector o)))).re = _
  rw [← h]
  simp

theorem labChartProbability_eq_genericBornProbability {d : ℕ}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : Outcome d) (x : TangentIndex d) (t : ℝ) :
    labChartProbability T U o x t =
      genericBornProbability (effectWeight d)
        ((T.conjTranspose * U).mulVec (measurementVector o)) x t := by
  rw [labChartProbability, trace_rankOneDensity_transportedEffect]
  simp only [basisBornProbability, basisBornAmplitude_transport, Matrix.mulVec_mulVec]
  rfl

/-- Each chart derivative used in the P2 information is the derivative of
the exact laboratory Born probability, with the measurement kept fixed. -/
theorem labChartProbability_hasDerivAt_zero {d : ℕ}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : Outcome d) (x : TangentIndex d) :
    HasDerivAt (labChartProbability T U o x)
      (transportedGradient (T.conjTranspose * U) o x) 0 := by
  have h := genericBornProbability_hasDerivAt_zero (effectWeight d)
    ((T.conjTranspose * U).mulVec (measurementVector o)) x
  have hg : genericEffectGradient (effectWeight d)
      ((T.conjTranspose * U).mulVec (measurementVector o)) x =
      transportedGradient (T.conjTranspose * U) o x := by
    cases x <;> simp only [genericEffectGradient, transportedGradient, transportedEffect_projector]
  rw [hg] at h
  have heq : labChartProbability T U o x = genericBornProbability (effectWeight d)
      ((T.conjTranspose * U).mulVec (measurementVector o)) x :=
    funext (labChartProbability_eq_genericBornProbability T U o x)
  rw [heq]
  exact h

theorem pureStateNormSq_unitary_mulVec {d : ℕ}
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (psi : Fin (d+1) → ℂ) :
    pureStateNormSq (T.mulVec psi) = pureStateNormSq psi := by
  apply Complex.ofReal_injective
  rw [← rankOneDensity_trace_eq_normSq, ← rankOneDensity_trace_eq_normSq]
  change Matrix.trace (projector (T.mulVec psi)) = Matrix.trace (projector psi)
  have hleft : T.conjTranspose * T = 1 := Matrix.mem_unitaryGroup_iff'.mp hT
  rw [projector_mulVec, Matrix.trace_mul_cycle, hleft, Matrix.one_mul]

/-- Within the chart domain the laboratory chart is a normalized physical
pure state, including when the Hilbert dimension is not a power of two. -/
def labChartState {d : ℕ}
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (x : TangentIndex d) (t : ℝ) (ht : t^2 ≤ 4) : PureVector d :=
  ⟨T.mulVec (directionalState x t), by
    change pureStateNormSq (T.mulVec (directionalState x t)) = 1
    rw [pureStateNormSq_unitary_mulVec T hT]
    exact directionalState_normalized x t ht⟩

/-- The chart probability is literally the probability assigned by the
implemented Born kernel to this physical nearby state. -/
theorem labChartProbability_eq_bornProbability {d : ℕ} (hd : 0 < d)
    (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (U : Action d) (o : Outcome d) (x : TangentIndex d) (t : ℝ) (ht : t^2 ≤ 4) :
    labChartProbability T U.matrix o x t =
      bornProbability hd (pureParameter d (labChartState T hT x t ht)) U o := by
  exact (congrArg Complex.re (bornProbability_eq_trace hd
    (pureParameter d (labChartState T hT x t ht)) U o)).symm

theorem labChartProbability_at_zero {d : ℕ}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : Outcome d) (x : TangentIndex d) :
    labChartProbability T U o x 0 = transportedMass (T.conjTranspose * U) o := by
  have hz : T.mulVec (directionalState x 0) = fun i => T i 0 := by
    ext i
    cases x <;> simp [Matrix.mulVec, dotProduct, directionalState, Fin.sum_univ_succ, radial]
  rw [labChartProbability, hz]
  change (Matrix.trace (frameProjector T * transportedEffect U o)).re = _
  rw [trace_frameProjector_mul, transportedEffect_relativeFrame]
  rfl

/-- Fisher information constructed from actual kernel probabilities and
actual derivatives of the physical laboratory-state chart. `safeRatio`
uses the conventional zero contribution at zero-probability outcomes. -/
def actualBornFisher {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o, safeRatio (bornProbability hd (pureParameter d truth) U o)
    (deriv (labChartProbability (trueFrame d truth) U.matrix o x) 0 *
      deriv (labChartProbability (trueFrame d truth) U.matrix o y) 0)

theorem actualBornFisher_eq_transportedFisher {d : ℕ} (hd : 0 < d)
    (truth : PureVector d) (U : Action d) :
    actualBornFisher hd truth U =
      transportedFisher ((trueFrame d truth).conjTranspose * U.matrix) := by
  have hderiv : ∀ (o : Outcome d) (x : TangentIndex d),
      deriv (labChartProbability (trueFrame d truth) U.matrix o x) 0 =
        transportedGradient ((trueFrame d truth).conjTranspose * U.matrix) o x :=
    fun o x => (labChartProbability_hasDerivAt_zero (trueFrame d truth) U.matrix o x).deriv
  funext x y
  unfold actualBornFisher transportedFisher
  apply Finset.sum_congr rfl
  intro o ho
  rw [bornProbability_pure_eq_transportedMass, hderiv, hderiv]

/-- The information converging in the final P2 theorem is this literal
Born Fisher information of its current, batch-frozen measurement action. -/
theorem designFisher_eq_actualBornFisher {d : ℕ} (hd : 0 < d)
    (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    designFisher hd batchSize truth path n =
      actualBornFisher hd truth (actualState hd batchSize path n).action := by
  rw [actualBornFisher_eq_transportedFisher]
  rfl

end

end QubitOracle.AdaptiveDesign.P2Adaptive
