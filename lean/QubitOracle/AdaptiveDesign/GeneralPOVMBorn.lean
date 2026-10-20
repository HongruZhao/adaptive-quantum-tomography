import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICIdentification
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.P2BornFisherIdentification
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.FiniteGillMassar
import QubitOracle.LocalChart
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.TwoBasis
/-! # Physical Born derivatives for arbitrary Hermitian effects
This calculus bridge does not require rank-one effects or the explicit library.
-/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian PureMatrixController
open GlobalPFSIC (projector quadratic frameProjector)
open GlobalPFSICBorn (Action)
open P2Adaptive (pureParameter trueFrame trueFrame_projector trace_frameProjector_mul labChartState)
open scoped BigOperators ComplexOrder
noncomputable section

def matrixGradient {d : ℕ} (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : TangentIndex d → ℝ
  | .inl j => (A 0 j.succ).re
  | .inr j => -(A 0 j.succ).im

theorem quadratic_directionalState {d : ℕ}
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hA : A.IsHermitian)
    (x : TangentIndex d) (t : ℝ) :
    (quadratic A (directionalState x t)).re =
      (radial t)^2 * (A 0 0).re + (t/2)^2 *
        (A (Sum.elim Fin.succ Fin.succ x) (Sum.elim Fin.succ Fin.succ x)).re +
        t * radial t * matrixGradient A x := by
  rcases x with j | j
  · have hc := congrArg (fun B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => B j.succ 0) hA.eq
    change star (A 0 j.succ) = A j.succ 0 at hc
    have hs : directionalState (.inl j) t =
        GlobalPFSIC.liftVector (radial t) (t/2) 0 (GlobalPFSIC.coordinate j) := by
      ext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [directionalState, GlobalPFSIC.liftVector]
      · by_cases h : k = j <;>
          simp [directionalState, GlobalPFSIC.liftVector, GlobalPFSIC.coordinate, GlobalPFSIC.phase4, h]
    rw [hs, GlobalPFSIC.quadratic_liftVector]
    simp [GlobalPFSIC.headRow, GlobalPFSIC.headColumn, GlobalPFSIC.tailBlock,
      GlobalPFSIC.coordinate, GlobalPFSIC.phase4, quadratic, ← hc,
      matrixGradient, Pi.single_apply, ← Complex.ofReal_pow, ← Complex.ofReal_div,
      Complex.mul_re, Complex.mul_im]
    ring
  · have hc := congrArg (fun B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => B j.succ 0) hA.eq
    change star (A 0 j.succ) = A j.succ 0 at hc
    have hs : directionalState (.inr j) t =
        GlobalPFSIC.liftVector (radial t) (t/2) 1 (GlobalPFSIC.coordinate j) := by
      ext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [directionalState, GlobalPFSIC.liftVector]
      · by_cases h : k = j <;>
          simp [directionalState, GlobalPFSIC.liftVector, GlobalPFSIC.coordinate, GlobalPFSIC.phase4, h, mul_comm]
    rw [hs, GlobalPFSIC.quadratic_liftVector]
    simp [GlobalPFSIC.headRow, GlobalPFSIC.headColumn, GlobalPFSIC.tailBlock,
      GlobalPFSIC.coordinate, GlobalPFSIC.phase4, quadratic, ← hc,
      matrixGradient, Pi.single_apply, ← Complex.ofReal_pow, ← Complex.ofReal_div,
      Complex.mul_re, Complex.mul_im]
    ring

theorem quadratic_directionalState_hasDerivAt_zero {d : ℕ}
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hA : A.IsHermitian) (x : TangentIndex d) :
    HasDerivAt (fun t => (quadratic A (directionalState x t)).re) (matrixGradient A x) 0 := by
  have hfirst := (hasDerivAt_radial_zero.pow 2).mul_const (A 0 0).re
  have hsecond := (((hasDerivAt_id (x := (0:ℝ))).div_const 2).pow 2).mul_const
    (A (Sum.elim Fin.succ Fin.succ x) (Sum.elim Fin.succ Fin.succ x)).re
  have hthird := ((hasDerivAt_id (x := (0:ℝ))).mul hasDerivAt_radial_zero).mul_const
    (matrixGradient A x)
  convert (hfirst.add hsecond).add hthird using 1
  all_goals first
    | rfl
    | (funext t; exact quadratic_directionalState A hA x t)
    | (simp [radial])

theorem effect_relativeFrame {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O)
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) :
    T.conjTranspose * effect P U o * T = effect P (T.conjTranspose * U) o := by
  simp only [effect, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

def labChartProbability {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : O) (x : TangentIndex d) (t : ℝ) : ℝ :=
  (Matrix.trace (rankOneDensity (T.mulVec (directionalState x t)) * effect P U o)).re

theorem labChartProbability_eq_quadratic {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : O) (x : TangentIndex d) (t : ℝ) :
    labChartProbability P T U o x t =
      (quadratic (effect P (T.conjTranspose * U) o) (directionalState x t)).re := by
  unfold labChartProbability
  change (Matrix.trace (projector (T.mulVec (directionalState x t)) * effect P U o)).re = _
  rw [GlobalPFSIC.projector_mulVec]
  have ht : Matrix.trace (T * projector (directionalState x t) * T.conjTranspose * effect P U o) =
      Matrix.trace ((T.conjTranspose * effect P U o * T) * projector (directionalState x t)) := by
    rw [Matrix.mul_assoc (T * projector (directionalState x t)) T.conjTranspose (effect P U o),
      Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  rw [ht, effect_relativeFrame, trace_mul_projector]

theorem labChartProbability_hasDerivAt_zero {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (o : O) (x : TangentIndex d) :
    HasDerivAt (labChartProbability P T U o x)
      (gradient P (T.conjTranspose * U) o x) 0 := by
  have he : labChartProbability P T U o x =
      fun t => (quadratic (effect P (T.conjTranspose * U) o) (directionalState x t)).re :=
    funext (labChartProbability_eq_quadratic P T U o x)
  rw [he]
  exact quadratic_directionalState_hasDerivAt_zero _ (effect_positive P _ o).isHermitian x

theorem bornProbability_pure_eq_mass {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : Action d) (o : O) :
    bornProbability P truth U o = mass P ((trueFrame d truth).conjTranspose * U.matrix) o := by
  have h := congrArg Complex.re (bornProbability_eq_trace P truth U o)
  change bornProbability P truth U o =
    (Matrix.trace (rankOneDensity truth.val * effect P U.matrix o)).re at h
  rw [← trueFrame_projector d truth, trace_frameProjector_mul, effect_relativeFrame] at h
  exact h

/-- In the chart domain these are probabilities of the same physical kernel. -/
theorem labChartProbability_eq_bornProbability {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (U : Action d) (o : O) (x : TangentIndex d) (t : ℝ) (ht : t^2 ≤ 4) :
    labChartProbability P T U.matrix o x t =
      bornProbability P (labChartState T hT x t ht) U o :=
  (congrArg Complex.re (bornProbability_eq_trace P (labChartState T hT x t ht) U o)).symm

/-- Actual outcome probabilities and derivatives, holding the measurement fixed. -/
def actualBornFisher {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : Action d) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o, safeRatio (bornProbability P truth U o)
    (deriv (labChartProbability P (trueFrame d truth) U.matrix o x) 0 *
      deriv (labChartProbability P (trueFrame d truth) U.matrix o y) 0)

theorem actualBornFisher_eq_fisher {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : Action d) :
    actualBornFisher P truth U = fisher P ((trueFrame d truth).conjTranspose * U.matrix) := by
  have hd (o : O) (x : TangentIndex d) :=
    (labChartProbability_hasDerivAt_zero P (trueFrame d truth) U.matrix o x).deriv
  funext x y
  unfold actualBornFisher fisher
  apply Finset.sum_congr rfl
  intro o _
  rw [bornProbability_pure_eq_mass, hd, hd]

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
  (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
  (regularization : ℝ) (hregularization : 0 < regularization)

theorem designFisher_eq_actualBornFisher (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath O) (n : ℕ) :
    designFisher P hI regularization hregularization batchSize truth path n =
      actualBornFisher P truth (actualState P hI regularization hregularization batchSize path n).action := by
  rw [actualBornFisher_eq_fisher]
  rfl

open Filter MeasureTheory
open scoped Topology

/-- General P2 with literal conditional Born information. This theorem assumes
only C1, C2, C3, a positive ridge parameter, a normalized pure truth, and
positive deterministic batch lengths. In particular it assumes no limit. -/
theorem adaptive_actualBorn_information (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (adaptiveProtocol P hI regularization hregularization batchSize) truth,
      Tendsto (rawEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (pureParameter d truth).1) ∧
      Tendsto (stateEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun n => actualBornFisher P truth
        (actualState P hI regularization hregularization batchSize path n).action) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        actualBornFisher P truth
          (actualState P hI regularization hregularization batchSize path n).action x y) atTop
        (𝓝 (((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  filter_upwards [adaptive_consistency_and_information P hI regularization hregularization
    hp hF truth batchSize hpositive] with path hpath
  have heq : (fun n => actualBornFisher P truth
      (actualState P hI regularization hregularization batchSize path n).action) =
      designFisher P hI regularization hregularization batchSize truth path :=
    funext (fun n => (designFisher_eq_actualBornFisher P hI regularization hregularization
      batchSize truth path n).symm)
  refine ⟨hpath.1, hpath.2.1, ?_, ?_⟩
  · rw [heq]
    exact hpath.2.2.1
  · intro x y
    simpa only [← designFisher_eq_actualBornFisher] using hpath.2.2.2 x y

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
