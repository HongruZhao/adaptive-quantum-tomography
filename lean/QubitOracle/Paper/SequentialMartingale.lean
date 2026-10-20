import QubitOracle.Paper.SequentialExperiment

/-!
# Finite conditional expectations for the adaptive score martingale

These are exact finite-sum conditional expectations for the alternating
history model.  They prove the score-centering and conditional covariance
identities before any asymptotic martingale theorem is invoked.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Conditional expectation over the outcome kernel after a setting has been
revealed. -/
def finiteOutcomeExpectation
    {Theta M Y E : Type*} [Fintype Y]
    [AddCommMonoid E] [Module ℝ E]
    (p : OutcomeKernel Theta M Y) (theta : Theta) (m : M)
    (f : Y -> E) : E :=
  ∑ y, p.mass (theta, m) y • f y

/-- Conditional expectation over the predictable randomized setting. -/
def finitePolicyExpectation
    {M Y E : Type*} [Fintype M]
    [AddCommMonoid E] [Module ℝ E]
    (q : AdaptivePolicy M Y) (h : SequentialHistory M Y)
    (f : M -> E) : E :=
  ∑ m, q.mass h m • f m

theorem finiteOutcomeExpectation_smul
    {Theta M Y E : Type*} [Fintype Y]
    [AddCommMonoid E] [Module ℝ E]
    (p : OutcomeKernel Theta M Y) (theta : Theta) (m : M)
    (c : ℝ) (f : Y -> E) :
    finiteOutcomeExpectation p theta m (fun y => c • f y) =
      c • finiteOutcomeExpectation p theta m f := by
  simp [finiteOutcomeExpectation, Finset.smul_sum, smul_smul, mul_comm]

/-- The certified score has zero conditional mean after the setting is
revealed. -/
theorem finiteOutcomeExpectation_score_eq_zero
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => model.score theta m y) = 0 := by
  funext j
  simp only [finiteOutcomeExpectation, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply]
  exact model.score_centered theta m j

/-- A regular-round weight known after the setting is revealed preserves
conditional score centering. -/
theorem finiteOutcomeExpectation_weightedScore_eq_zero
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (regularWeight : ℝ) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => regularWeight • model.score theta m y) = 0 := by
  rw [finiteOutcomeExpectation_smul,
    finiteOutcomeExpectation_score_eq_zero, smul_zero]

/-- Conditional second moment of the score is the conditional Fisher
information. -/
theorem finiteOutcomeExpectation_scoreOuter_eq_information
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => Matrix.vecMulVec (model.score theta m y)
        (model.score theta m y)) =
      conditionalInformation model theta m :=
  rfl

/-- A regular-round weight pulls through the conditional second moment. -/
theorem finiteOutcomeExpectation_weightedScoreOuter_eq_information
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (regularWeight : ℝ) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => regularWeight •
        Matrix.vecMulVec (model.score theta m y) (model.score theta m y)) =
      regularWeight • conditionalInformation model theta m := by
  rw [finiteOutcomeExpectation_smul,
    finiteOutcomeExpectation_scoreOuter_eq_information]

/-- The tower expectation before the randomized setting is also zero. -/
theorem finitePolicyExpectation_scoreTower_eq_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (h : SequentialHistory M Y) :
    finitePolicyExpectation q h (fun m =>
      finiteOutcomeExpectation model.outcome theta m
        (fun y => model.score theta m y)) = 0 := by
  simp [finitePolicyExpectation, finiteOutcomeExpectation_score_eq_zero]

/-- Information predictable before the randomized setting is revealed. -/
def preSettingPredictableInformation
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (h : SequentialHistory M Y) : Matrix D D ℝ :=
  finitePolicyExpectation q h (fun m => conditionalInformation model theta m)

/-- Accumulated score with a weight fixed after each setting and before its
outcome.  In the LAN application this is `C_{n,i} = 1 - E_{n,i}`. -/
def weightedHistoryScore
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ) :
    SequentialHistory M Y -> D -> ℝ
  | [] => 0
  | (m, y) :: h =>
      weightedHistoryScore model theta regularWeight h +
        regularWeight h m • model.score theta m y

/-- Accumulated conditional information with the same predictable regular
weights. -/
def weightedAccumulatedInformation
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ) :
    SequentialHistory M Y -> Matrix D D ℝ
  | [] => 0
  | (m, _y) :: h =>
      weightedAccumulatedInformation model theta regularWeight h +
        regularWeight h m • conditionalInformation model theta m

/-- Normalized regular information along the realized selected settings. -/
def weightedEmpiricalInformation
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ)
    (h : SequentialHistory M Y) : Matrix D D ℝ :=
  (h.length : ℝ)⁻¹ •
    weightedAccumulatedInformation model theta regularWeight h

/-- The regular-score central sequence used in adaptive LAN. -/
def weightedCentralSequence
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ)
    (h : SequentialHistory M Y) : D -> ℝ :=
  (Real.sqrt (h.length : ℝ))⁻¹ •
    weightedHistoryScore model theta regularWeight h

end

end QubitOracle.Paper
