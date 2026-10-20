import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.Paper.FiniteKernelPathSpace

/-!
# Exact physical Born response and all-observation regression frame

The parameter is a positive, trace-one Hermitian matrix. Every action is an
actual unitary conjugation of the explicitly constructed finite POVM. Its
finite response kernel, expectation identity, uniform response bound, and
uniformly positive regression-frame constant are proved here.

Actions have the discrete measurable space. This is sufficient and exact for
a policy generated from finite outcome histories; no measurable selection on
an uncountable ambient estimator space is required.
-/

namespace QubitOracle.AdaptiveDesign.GlobalPFSICBorn

open MeasureTheory ProbabilityTheory QubitOracle.Paper
open GlobalPFSIC GlobalPFSICHermitian FiniteFrameCoercivity
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section

abbrev PhysicalParameter (n : ℕ) :=
  {A : HermitianSpace n // (toMatrix A).PosSemidef ∧ Matrix.trace (toMatrix A) = 1}

structure Action (d : ℕ) where
  matrix : Matrix (Fin (d+1)) (Fin (d+1)) ℂ
  unitary : matrix ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ

instance (d : ℕ) : MeasurableSpace (Action d) := ⊤
instance (d : ℕ) : MeasurableSpace (Outcome d) := ⊤
instance (d : ℕ) : MeasurableSingletonClass (Outcome d) where
  measurableSet_singleton _ := by trivial

def responseVector {d : ℕ} (hd : 0 < d) (U : Action d) (o : Outcome d) : HermitianSpace (d+1) :=
  conjugationIsometry U.matrix U.unitary (effectVector hd o)

def regressionFrame {d : ℕ} (hd : 0 < d) (U : Action d) :
    HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  frameOperator (responseVector hd U)

def bornProbability {d : ℕ} (hd : 0 < d) (theta : PhysicalParameter (d+1))
    (U : Action d) (o : Outcome d) : ℝ :=
  ⟪responseVector hd U o, theta.1⟫_ℝ

theorem bornProbability_eq_trace {d : ℕ} (hd : 0 < d) (theta : PhysicalParameter (d+1))
    (U : Action d) (o : Outcome d) :
    (bornProbability hd theta U o : ℂ) =
      Matrix.trace (toMatrix theta.1 * transportedEffect U.matrix o) := by
  rw [bornProbability, complex_inner_eq_trace]
  rfl

theorem bornProbability_eq_quadratic {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) (o : Outcome d) :
    bornProbability hd theta U o = effectWeight d *
      (quadratic (toMatrix theta.1) (U.matrix.mulVec (measurementVector o))).re := by
  have h := congrArg Complex.re (bornProbability_eq_trace hd theta U o)
  rw [transportedEffect_projector, Matrix.mul_smul, Matrix.trace_smul, trace_mul_projector] at h
  simpa using h

theorem bornProbability_nonnegative {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) (o : Outcome d) :
    0 ≤ bornProbability hd theta U o := by
  rw [bornProbability_eq_quadratic]
  apply mul_nonneg (effectWeight_pos d hd).le
  have h := theta.2.1.dotProduct_mulVec_nonneg (U.matrix.mulVec (measurementVector o))
  have hr := (Complex.nonneg_iff.mp h).1
  simpa [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hr

theorem bornProbability_sum {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) :
    ∑ o, bornProbability hd theta U o = 1 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [bornProbability_eq_trace]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum,
    transportedEffect_complete hd U.matrix U.unitary, Matrix.mul_one, theta.2.2]

def bornMeasure {d : ℕ} (hd : 0 < d) (theta : PhysicalParameter (d+1)) (U : Action d) :
    Measure (Outcome d) :=
  finiteMassMeasure (bornProbability hd theta U)
    (bornProbability_nonnegative hd theta U) (bornProbability_sum hd theta U)

instance bornMeasure_isProbability {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) :
    IsProbabilityMeasure (bornMeasure hd theta U) := by
  unfold bornMeasure
  infer_instance

def bornKernel {d : ℕ} (hd : 0 < d) (theta : PhysicalParameter (d+1)) :
    Kernel (Action d) (Outcome d) where
  toFun := bornMeasure hd theta
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    intro t ht
    trivial

instance bornKernel_isMarkov {d : ℕ} (hd : 0 < d) (theta : PhysicalParameter (d+1)) :
    IsMarkovKernel (bornKernel hd theta) where
  isProbabilityMeasure U := bornMeasure_isProbability hd theta U

/-- The exact one-hot response normal equation for this physical POVM. -/
theorem responseVector_mean {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) :
    ∫ o, responseVector hd U o ∂bornKernel hd theta U = regressionFrame hd U theta.1 := by
  change (∫ o, responseVector hd U o ∂finiteMassMeasure
    (bornProbability hd theta U) (bornProbability_nonnegative hd theta U)
    (bornProbability_sum hd theta U)) = _
  rw [integral_finiteMassMeasure]
  rfl

def responseBound {d : ℕ} (hd : 0 < d) : ℝ := ∑ o : Outcome d, ‖effectVector hd o‖

theorem responseBound_nonnegative {d : ℕ} (hd : 0 < d) : 0 ≤ responseBound hd :=
  Finset.sum_nonneg (fun o _ => norm_nonneg _)

theorem responseVector_norm_le {d : ℕ} (hd : 0 < d) (U : Action d) (o : Outcome d) :
    ‖responseVector hd U o‖ ≤ responseBound hd := by
  rw [responseVector, (conjugationIsometry U.matrix U.unitary).norm_map]
  exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ o)

theorem regressionFrame_truth_norm_le {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) :
    ‖regressionFrame hd U theta.1‖ ≤ responseBound hd := by
  calc
    ‖regressionFrame hd U theta.1‖ =
        ‖∑ o : Outcome d, bornProbability hd theta U o • responseVector hd U o‖ := rfl
    _ ≤ ∑ o : Outcome d, ‖bornProbability hd theta U o • responseVector hd U o‖ :=
      norm_sum_le _ _
    _ ≤ ∑ o : Outcome d, bornProbability hd theta U o * responseBound hd := by
      apply Finset.sum_le_sum
      intro o _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bornProbability_nonnegative hd theta U o)]
      exact mul_le_mul_of_nonneg_left (responseVector_norm_le hd U o)
        (bornProbability_nonnegative hd theta U o)
    _ = responseBound hd := by rw [← Finset.sum_mul, bornProbability_sum, one_mul]

theorem responseInnovation_bound {d : ℕ} (hd : 0 < d)
    (theta : PhysicalParameter (d+1)) (U : Action d) (o : Outcome d) :
    ‖responseVector hd U o - regressionFrame hd U theta.1‖ ≤ 2 * responseBound hd := by
  calc
    _ ≤ ‖responseVector hd U o‖ + ‖regressionFrame hd U theta.1‖ := norm_sub_le _ _
    _ ≤ responseBound hd + responseBound hd :=
      add_le_add (responseVector_norm_le hd U o) (regressionFrame_truth_norm_le hd theta U)
    _ = 2 * responseBound hd := by ring

theorem exists_uniform_regression_coercivity {d : ℕ} (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ U : Action d, CoerciveLeastSquares.Coercive (regressionFrame hd U) κ := by
  obtain ⟨κ, hκ, hframe⟩ := transportedFrame_uniform_coercivity hd
  exact ⟨κ, hκ, fun U => hframe U.matrix U.unitary⟩

end

end QubitOracle.AdaptiveDesign.GlobalPFSICBorn
