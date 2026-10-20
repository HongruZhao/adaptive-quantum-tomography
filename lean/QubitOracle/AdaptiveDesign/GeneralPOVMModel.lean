import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem

/-! # Arbitrary finite, globally identifying POVMs
No rank, equal-weight, phase, latitude, or library restriction is imposed.
The actual Born kernel, response mean, bounded innovations and uniform frame
bound are proved for every pure truth in every finite complex dimension.
-/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open MeasureTheory ProbabilityTheory QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian FiniteFrameCoercivity PureMatrixController
open GlobalPFSIC (projector quadratic)
open GlobalPFSICBorn (Action)
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

def effect {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) :=
  U * P.effect o * U.conjTranspose

theorem effect_positive {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : O) :
    (effect P U o).PosSemidef := (P.positive o).mul_mul_conjTranspose_same U

theorem effect_complete {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) : ∑ o, effect P U o = 1 := by
  simp only [effect, ← Matrix.sum_mul, ← Matrix.mul_sum, P.complete, Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp hU

def effectVector {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (o : O) : HermitianSpace (d+1) :=
  ofMatrix (P.effect o) (P.positive o).isHermitian

/-- C1: zero measurement coordinates force a Hermitian matrix to vanish. -/
def Identifying {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) : Prop :=
  ∀ A : HermitianSpace (d+1), (∀ o, ⟪effectVector P o, A⟫_ℝ = 0) → A = 0

def responseVector {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) (U : Action d) (o : O) : HermitianSpace (d+1) :=
  conjugationIsometry U.matrix U.unitary (effectVector P o)

def regressionFrame {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) (U : Action d) :
    HermitianSpace (d+1) →ₗ[ℝ] HermitianSpace (d+1) :=
  frameOperator (responseVector P U)

def bornProbability {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d)
    (U : Action d) (o : O) : ℝ :=
  ⟪responseVector P U o, (P2Adaptive.pureParameter d theta).1⟫_ℝ

theorem bornProbability_eq_trace {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d)
    (U : Action d) (o : O) :
    (bornProbability P theta U o : ℂ) =
      Matrix.trace (toMatrix (P2Adaptive.pureParameter d theta).1 * effect P U.matrix o) := by
  rw [bornProbability, complex_inner_eq_trace]
  rfl

theorem bornProbability_nonnegative {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d) (U : Action d) (o : O) :
    0 ≤ bornProbability P theta U o := by
  have hr := congrArg Complex.re (bornProbability_eq_trace P theta U o)
  change bornProbability P theta U o =
    (Matrix.trace (rankOneDensity theta.val * effect P U.matrix o)).re at hr
  change bornProbability P theta U o =
    (Matrix.trace (projector theta.val * effect P U.matrix o)).re at hr
  rw [Matrix.trace_mul_comm, trace_mul_projector] at hr
  rw [hr]
  have h := (effect_positive P U.matrix o).dotProduct_mulVec_nonneg theta.val
  simpa [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using (Complex.nonneg_iff.mp h).1

theorem bornProbability_sum {d : ℕ} {O : Type} [Fintype O] (P : FinitePOVM (Fin (d+1)) O)
    (theta : PureVector d) (U : Action d) :
    ∑ o, bornProbability P theta U o = 1 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [bornProbability_eq_trace]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum,
    effect_complete P U.matrix U.unitary, Matrix.mul_one, (P2Adaptive.pureParameter d theta).2.2]

def bornMeasure {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d) (U : Action d) :
    Measure (O) :=
  finiteMassMeasure (bornProbability P theta U)
    (bornProbability_nonnegative P theta U) (bornProbability_sum P theta U)

instance bornMeasure_isProbability {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O)
    (theta : PureVector d) (U : Action d) :
    IsProbabilityMeasure (bornMeasure P theta U) := by
  unfold bornMeasure
  infer_instance

def bornKernel {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d) :
    Kernel (Action d) (O) where
  toFun := bornMeasure P theta
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    intro t ht
    trivial

instance bornKernel_isMarkov {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) (theta : PureVector d) :
    IsMarkovKernel (bornKernel P theta) where
  isProbabilityMeasure U := bornMeasure_isProbability P theta U

/-- The exact one-hot response normal equation for this physical POVM. -/
theorem responseVector_mean {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O)
    (theta : PureVector d) (U : Action d) :
    ∫ o, responseVector P U o ∂bornKernel P theta U = regressionFrame P U (P2Adaptive.pureParameter d theta).1 := by
  change (∫ o, responseVector P U o ∂finiteMassMeasure
    (bornProbability P theta U) (bornProbability_nonnegative P theta U)
    (bornProbability_sum P theta U)) = _
  rw [integral_finiteMassMeasure]
  rfl

def responseBound {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) : ℝ := ∑ o : O, ‖effectVector P o‖

theorem responseBound_nonnegative {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) : 0 ≤ responseBound P :=
  Finset.sum_nonneg (fun o _ => norm_nonneg _)

theorem responseVector_norm_le {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O) (U : Action d) (o : O) :
    ‖responseVector P U o‖ ≤ responseBound P := by
  rw [responseVector, (conjugationIsometry U.matrix U.unitary).norm_map]
  exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ o)

theorem regressionFrame_truth_norm_le {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O)
    (theta : PureVector d) (U : Action d) :
    ‖regressionFrame P U (P2Adaptive.pureParameter d theta).1‖ ≤ responseBound P := by
  calc
    ‖regressionFrame P U (P2Adaptive.pureParameter d theta).1‖ =
        ‖∑ o : O, bornProbability P theta U o • responseVector P U o‖ := rfl
    _ ≤ ∑ o : O, ‖bornProbability P theta U o • responseVector P U o‖ :=
      norm_sum_le _ _
    _ ≤ ∑ o : O, bornProbability P theta U o * responseBound P := by
      apply Finset.sum_le_sum
      intro o _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bornProbability_nonnegative P theta U o)]
      exact mul_le_mul_of_nonneg_left (responseVector_norm_le P U o)
        (bornProbability_nonnegative P theta U o)
    _ = responseBound P := by rw [← Finset.sum_mul, bornProbability_sum, one_mul]

theorem responseInnovation_bound {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] (P : FinitePOVM (Fin (d+1)) O)
    (theta : PureVector d) (U : Action d) (o : O) :
    ‖responseVector P U o - regressionFrame P U (P2Adaptive.pureParameter d theta).1‖ ≤ 2 * responseBound P := by
  calc
    _ ≤ ‖responseVector P U o‖ + ‖regressionFrame P U (P2Adaptive.pureParameter d theta).1‖ := norm_sub_le _ _
    _ ≤ responseBound P + responseBound P :=
      add_le_add (responseVector_norm_le P U o) (regressionFrame_truth_norm_le P theta U)
    _ = 2 * responseBound P := by ring

theorem exists_uniform_regression_coercivity {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hP : Identifying P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ U : Action d,
      CoerciveLeastSquares.Coercive (regressionFrame P U) κ := by
  obtain ⟨κ, hκ, hframe⟩ := exists_positive_coercivity_of_separating (effectVector P) hP
  exact ⟨κ, hκ, fun U => coercivity_preserved_by_isometry
    (conjugationIsometry U.matrix U.unitary) (effectVector P) κ hframe⟩

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
