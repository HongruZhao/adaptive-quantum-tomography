import QubitOracle.Paper.SequentialMartingale

/-!
# Score and Hessian identities for finite conditional models

For a positive finite mass function, the first and second derivatives of the
normalization identity sum to zero.  This file uses those two certified
derivative identities to derive score centering and the information identity
for the negative log-mass Hessian.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Finite conditional masses with certified first and second parameter
derivatives at each chart point. -/
structure FiniteLogDerivativeModel
    (Theta M Y D : Type*) [Fintype Y] where
  outcome : OutcomeKernel Theta M Y
  firstDerivative : Theta -> M -> Y -> D -> ℝ
  secondDerivative : Theta -> M -> Y -> Matrix D D ℝ
  mass_pos : ∀ theta m y, 0 < outcome.mass (theta, m) y
  firstDerivative_sum_zero : ∀ theta m j,
    ∑ y, firstDerivative theta m y j = 0
  secondDerivative_sum_zero : ∀ theta m j k,
    ∑ y, secondDerivative theta m y j k = 0

/-- Logarithmic first derivative of a positive conditional mass. -/
def FiniteLogDerivativeModel.logScore
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (m : M) (y : Y) : D -> ℝ :=
  (model.outcome.mass (theta, m) y)⁻¹ • model.firstDerivative theta m y

/-- The derivative-certified model induces a centered finite score model. -/
def FiniteLogDerivativeModel.toFiniteScoreModel
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D) :
    FiniteScoreModel Theta M Y D where
  outcome := model.outcome
  score := model.logScore
  score_centered := by
    intro theta m j
    calc
      (∑ y, model.outcome.mass (theta, m) y *
          model.logScore theta m y j) =
          ∑ y, model.firstDerivative theta m y j := by
            apply Finset.sum_congr rfl
            intro y _
            simp [FiniteLogDerivativeModel.logScore,
              (model.mass_pos theta m y).ne']
      _ = 0 := model.firstDerivative_sum_zero theta m j

/-- Negative Hessian of the conditional log mass, expressed through mass
derivatives. -/
def FiniteLogDerivativeModel.observedInformation
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (m : M) (y : Y) : Matrix D D ℝ :=
  Matrix.vecMulVec (model.logScore theta m y) (model.logScore theta m y) -
    (model.outcome.mass (theta, m) y)⁻¹ • model.secondDerivative theta m y

/-- Conditional expected negative log-mass Hessian equals conditional Fisher
information. -/
theorem finiteOutcomeExpectation_observedInformation_eq_information
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (m : M) :
    finiteOutcomeExpectation model.outcome theta m
        (fun y => model.observedInformation theta m y) =
      conditionalInformation model.toFiniteScoreModel theta m := by
  ext j k
  rw [conditionalInformation_apply]
  simp only [finiteOutcomeExpectation, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have hsecond :
      (∑ y, model.outcome.mass (theta, m) y *
        ((model.outcome.mass (theta, m) y)⁻¹ *
          model.secondDerivative theta m y j k)) = 0 := by
    calc
      (∑ y, model.outcome.mass (theta, m) y *
          ((model.outcome.mass (theta, m) y)⁻¹ *
            model.secondDerivative theta m y j k)) =
          ∑ y, model.secondDerivative theta m y j k := by
            apply Finset.sum_congr rfl
            intro y _
            simp [(model.mass_pos theta m y).ne']
      _ = 0 := model.secondDerivative_sum_zero theta m j k
  calc
    (∑ y, model.outcome.mass (theta, m) y *
        (model.logScore theta m y j * model.logScore theta m y k -
          (model.outcome.mass (theta, m) y)⁻¹ *
            model.secondDerivative theta m y j k)) =
        (∑ y, model.outcome.mass (theta, m) y *
          (model.logScore theta m y j * model.logScore theta m y k)) -
        (∑ y, model.outcome.mass (theta, m) y *
          ((model.outcome.mass (theta, m) y)⁻¹ *
            model.secondDerivative theta m y j k)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ y, model.outcome.mass (theta, m) y *
          (model.logScore theta m y j * model.logScore theta m y k) := by
            rw [hsecond, sub_zero]

end

end QubitOracle.Paper
