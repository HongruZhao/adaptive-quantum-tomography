import QubitOracle.Paper.SequentialLikelihoodAlgebra

/-!
# Finite adaptive sequential experiments

This file gives a fully normalized finite-outcome model for the algebraic
layer of the adaptive quantum experiment.  Histories are stored in reverse
chronological order, so the tail of `(m, y) :: h` is exactly the history
available before the newest setting and outcome.  The policy has no parameter
argument, which enforces parameter-free predictable randomization by type.

The construction is deliberately finite and discrete.  The later
measure-theoretic layer must connect it to Radon--Nikodym derivatives and
conditional expectations for general kernels.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- A normalized finite probability kernel represented by its mass
function. -/
structure FiniteKernel (α β : Type*) [Fintype β] where
  mass : α -> β -> ℝ
  mass_nonneg : ∀ a b, 0 ≤ mass a b
  sum_mass : ∀ a, ∑ b, mass a b = 1

namespace FiniteKernel

/-- Convex mixture of two finite kernels. -/
def convexMix {α β : Type*} [Fintype β]
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (exploit explore : FiniteKernel α β) : FiniteKernel α β where
  mass a b :=
    (1 - epsilon) * exploit.mass a b + epsilon * explore.mass a b
  mass_nonneg a b :=
    add_nonneg
      (mul_nonneg (sub_nonneg.mpr hepsilon1) (exploit.mass_nonneg a b))
      (mul_nonneg hepsilon0 (explore.mass_nonneg a b))
  sum_mass a := by
    calc
      (∑ b, ((1 - epsilon) * exploit.mass a b +
          epsilon * explore.mass a b)) =
          (1 - epsilon) * (∑ b, exploit.mass a b) +
            epsilon * (∑ b, explore.mass a b) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 1 := by rw [exploit.sum_mass, explore.sum_mass]; ring

@[simp]
theorem convexMix_mass {α β : Type*} [Fintype β]
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (exploit explore : FiniteKernel α β) (a : α) (b : β) :
    (convexMix epsilon hepsilon0 hepsilon1 exploit explore).mass a b =
      (1 - epsilon) * exploit.mass a b + epsilon * explore.mass a b :=
  rfl

end FiniteKernel

/-- Recorded settings and outcomes, newest observation first. -/
abbrev SequentialHistory (M Y : Type*) := List (M × Y)

/-- Information available after a setting is selected but before its outcome
is revealed. -/
abbrev PreOutcomeHistory (M Y : Type*) := SequentialHistory M Y × M

/-- Reveal the predictable setting selected from the past history. -/
def revealSetting {M Y : Type*} (h : SequentialHistory M Y) (m : M) :
    PreOutcomeHistory M Y :=
  (h, m)

/-- Reveal the outcome and extend the recorded history. -/
def revealOutcome {M Y : Type*} (g : PreOutcomeHistory M Y) (y : Y) :
    SequentialHistory M Y :=
  (g.2, y) :: g.1

/-- A predictable policy.  Its domain is the observed past and, crucially,
there is no unknown-parameter argument. -/
abbrev AdaptivePolicy (M Y : Type*) [Fintype M] :=
  FiniteKernel (SequentialHistory M Y) M

/-- Conditional outcome law after the setting has been revealed. -/
abbrev OutcomeKernel (Theta M Y : Type*) [Fintype Y] :=
  FiniteKernel (Theta × M) Y

/-- The exact initial/exploitation/exploration policy kernel. -/
def shotwisePolicyKernel {M Y : Type*} [Fintype M]
    (initial : Bool) (epsilon : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (exploit explore : AdaptivePolicy M Y) : AdaptivePolicy M Y :=
  if initial then explore
  else FiniteKernel.convexMix epsilon hepsilon0 hepsilon1 exploit explore

/-- Conditional Born mass, abstracted as the parameter-dependent outcome
kernel. -/
def conditionalBornMass {Theta M Y : Type*} [Fintype Y]
    (p : OutcomeKernel Theta M Y) (theta : Theta) (m : M) (y : Y) : ℝ :=
  p.mass (theta, m) y

/-- Product of all parameter-free setting-policy factors along a path. -/
def policyPathMass {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) : SequentialHistory M Y -> ℝ
  | [] => 1
  | (m, _y) :: h => policyPathMass q h * q.mass h m

/-- Product of all parameter-dependent outcome factors along a path. -/
def outcomePathMass {Theta M Y : Type*} [Fintype Y]
    (p : OutcomeKernel Theta M Y) (theta : Theta) :
    SequentialHistory M Y -> ℝ
  | [] => 1
  | (m, y) :: h => outcomePathMass p theta h * p.mass (theta, m) y

/-- Joint mass of the complete recorded adaptive path. -/
def adaptivePathMass {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta) :
    SequentialHistory M Y -> ℝ
  | [] => 1
  | (m, y) :: h =>
      adaptivePathMass q p theta h * q.mass h m * p.mass (theta, m) y

theorem adaptivePathMass_eq_policy_mul_outcome
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y)
    (theta : Theta) (h : SequentialHistory M Y) :
    adaptivePathMass q p theta h =
      policyPathMass q h * outcomePathMass p theta h := by
  induction h with
  | nil => simp [adaptivePathMass, policyPathMass, outcomePathMass]
  | cons z h ih =>
      rcases z with ⟨m, y⟩
      simp [adaptivePathMass, policyPathMass, outcomePathMass, ih]
      ring

/-- Product of the shotwise conditional outcome-mass ratios. -/
def shotwiseLikelihoodRatio {Theta M Y : Type*} [Fintype Y]
    (p : OutcomeKernel Theta M Y) (theta theta' : Theta) :
    SequentialHistory M Y -> ℝ
  | [] => 1
  | (m, y) :: h =>
      shotwiseLikelihoodRatio p theta theta' h *
        (p.mass (theta', m) y / p.mass (theta, m) y)

theorem outcomePathLikelihoodRatio_eq_shotwiseProduct
    {Theta M Y : Type*} [Fintype Y]
    (p : OutcomeKernel Theta M Y) (theta theta' : Theta)
    (h : SequentialHistory M Y) :
    outcomePathMass p theta' h / outcomePathMass p theta h =
      shotwiseLikelihoodRatio p theta theta' h := by
  induction h with
  | nil => simp [outcomePathMass, shotwiseLikelihoodRatio]
  | cons z h ih =>
      rcases z with ⟨m, y⟩
      rw [outcomePathMass, outcomePathMass, shotwiseLikelihoodRatio]
      calc
        (outcomePathMass p theta' h * p.mass (theta', m) y) /
            (outcomePathMass p theta h * p.mass (theta, m) y) =
            (outcomePathMass p theta' h / outcomePathMass p theta h) *
              (p.mass (theta', m) y / p.mass (theta, m) y) := by
                exact (div_mul_div_comm _ _ _ _).symm
        _ = shotwiseLikelihoodRatio p theta theta' h *
              (p.mass (theta', m) y / p.mass (theta, m) y) := by
                rw [ih]

/-- Exact finite-path likelihood factorization.  The common adaptive policy
cancels even though it depends on the realized past. -/
theorem finiteAdaptiveLikelihoodRatio_factorization
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y)
    (theta theta' : Theta) (h : SequentialHistory M Y)
    (hq : policyPathMass q h ≠ 0) :
    adaptivePathMass q p theta' h / adaptivePathMass q p theta h =
      shotwiseLikelihoodRatio p theta theta' h := by
  rw [adaptivePathMass_eq_policy_mul_outcome,
    adaptivePathMass_eq_policy_mul_outcome]
  rw [commonPolicyMass_cancels _ _ _ hq]
  exact outcomePathLikelihoodRatio_eq_shotwiseProduct p theta theta' h

/-- A finite conditional outcome model equipped with a certified centered
score vector. -/
structure FiniteScoreModel
    (Theta M Y D : Type*) [Fintype Y] where
  outcome : OutcomeKernel Theta M Y
  score : Theta -> M -> Y -> D -> ℝ
  score_centered : ∀ theta m j,
    ∑ y, outcome.mass (theta, m) y * score theta m y j = 0

/-- One-shot score increment. -/
def scoreIncrement {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (y : Y) : D -> ℝ :=
  model.score theta m y

/-- Conditional mean of the score increment. -/
def conditionalScoreMean {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) : D -> ℝ :=
  fun j => ∑ y, model.outcome.mass (theta, m) y * model.score theta m y j

theorem conditionalScoreMean_eq_zero
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) :
    conditionalScoreMean model theta m = 0 := by
  funext j
  exact model.score_centered theta m j

/-- Conditional Fisher information of one selected setting. -/
def conditionalInformation
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) : Matrix D D ℝ :=
  ∑ y, model.outcome.mass (theta, m) y •
    Matrix.vecMulVec (model.score theta m y) (model.score theta m y)

theorem conditionalInformation_apply
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (j k : D) :
    conditionalInformation model theta m j k =
      ∑ y, model.outcome.mass (theta, m) y *
        (model.score theta m y j * model.score theta m y k) := by
  simp only [conditionalInformation, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]

/-- Sum of realized score increments along a recorded history. -/
def historyScore {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta) :
    SequentialHistory M Y -> D -> ℝ
  | [] => 0
  | (m, y) :: h => historyScore model theta h + model.score theta m y

/-- Predictable accumulated information along the realized settings. -/
def accumulatedInformation {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta) :
    SequentialHistory M Y -> Matrix D D ℝ
  | [] => 0
  | (m, _y) :: h =>
      accumulatedInformation model theta h + conditionalInformation model theta m

/-- Realized normalized Fisher information. -/
def empiricalInformation {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (h : SequentialHistory M Y) : Matrix D D ℝ :=
  (h.length : ℝ)⁻¹ • accumulatedInformation model theta h

/-- Martingale central sequence associated with the full recorded history. -/
def centralSequence {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (h : SequentialHistory M Y) : D -> ℝ :=
  (Real.sqrt (h.length : ℝ))⁻¹ • historyScore model theta h

end

end QubitOracle.Paper
