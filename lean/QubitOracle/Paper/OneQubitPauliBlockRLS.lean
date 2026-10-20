import QubitOracle.Paper.OneQubitAPSRLSContract

/-!
# Three-Pauli-block RLS reduction for a mixed qubit

This file proves the deterministic and one-step probabilistic identities that
connect mixed-qubit Born observations to the finite-dimensional RLS model.
The design is deliberately concrete: every pilot block measures the three
Cartesian Pauli axes once.
-/

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

def rlsDot {d : ℕ} (x y : RLSVector d) : ℝ :=
  ∑ i, x i * y i

def pauliBasis (j : Fin 3) : RLSVector 3 :=
  fun i => if i = j then 1 else 0

def pauliIdentity : RLSMatrix 3 :=
  fun i j => if i = j then 1 else 0

def pauliOneBlockGram : RLSMatrix 3 :=
  ∑ j : Fin 3, rlsOuter (pauliBasis j)

theorem pauliOneBlockGram_apply (i k : Fin 3) :
    pauliOneBlockGram i k = pauliIdentity i k := by
  classical
  by_cases hik : i = k
  · subst k
    simp [pauliOneBlockGram, pauliIdentity, rlsOuter, pauliBasis,
      Matrix.sum_apply]
  · simp [pauliOneBlockGram, pauliIdentity, rlsOuter, pauliBasis,
      Matrix.sum_apply, hik]

theorem pauliOneBlockGram_eq_identity :
    pauliOneBlockGram = pauliIdentity := by
  funext i k
  exact pauliOneBlockGram_apply i k

/-- The Gram matrix after `q` complete three-measurement pilot blocks. -/
def pauliCompleteBlockGram (q : ℕ) : RLSMatrix 3 :=
  ∑ b ∈ Finset.range q, pauliOneBlockGram

theorem pauliCompleteBlockGram_apply (q : ℕ) (i k : Fin 3) :
    pauliCompleteBlockGram q i k =
      (q : ℝ) * pauliIdentity i k := by
  classical
  simp [pauliCompleteBlockGram, Matrix.sum_apply,
    pauliOneBlockGram_apply]

theorem pauliCompleteBlockGram_eq (q : ℕ) :
    pauliCompleteBlockGram q = (q : ℝ) • pauliIdentity := by
  funext i k
  simp [pauliCompleteBlockGram_apply]

theorem pauliCompleteBlock_quadratic (q : ℕ) (x : RLSVector 3) :
    rlsQuadratic (pauliCompleteBlockGram q) x =
      (q : ℝ) * ∑ i, x i ^ 2 := by
  classical
  unfold rlsQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pauliCompleteBlockGram_apply, pauliIdentity]
  ring

/-- A Boolean outcome is encoded as the plus-or-minus-one Pauli eigenvalue. -/
def pauliOutcomeSign (outcome : Bool) : ℝ :=
  if outcome then 1 else -1

/-- Born probability for the `+1` result when measuring Cartesian axis `j`. -/
def pauliBornProbability
    (theta : RLSVector 3) (j : Fin 3) (outcome : Bool) : ℝ :=
  if outcome then (1 + theta j) / 2 else (1 - theta j) / 2

def pauliRegressionNoise
    (theta : RLSVector 3) (j : Fin 3) (outcome : Bool) : ℝ :=
  pauliOutcomeSign outcome - theta j

/-- Every one-qubit Pauli observation is exactly a linear regression
observation with regressor `e_j`. -/
theorem pauli_observation_regression_identity
    (theta : RLSVector 3) (j : Fin 3) (outcome : Bool) :
    pauliOutcomeSign outcome =
      rlsDot (pauliBasis j) theta + pauliRegressionNoise theta j outcome := by
  classical
  simp [rlsDot, pauliBasis, pauliRegressionNoise]

/-- The Born residual is exactly conditionally centered. -/
theorem pauliRegressionNoise_born_centered
    (theta : RLSVector 3) (j : Fin 3) :
    ∑ outcome : Bool,
      pauliBornProbability theta j outcome *
        pauliRegressionNoise theta j outcome = 0 := by
  simp [pauliBornProbability, pauliRegressionNoise, pauliOutcomeSign]
  ring

theorem pauliBornProbability_nonnegative
    (theta : RLSVector 3) (j : Fin 3)
    (hlower : -1 ≤ theta j) (hupper : theta j ≤ 1)
    (outcome : Bool) :
    0 ≤ pauliBornProbability theta j outcome := by
  cases outcome <;> simp [pauliBornProbability] <;> linarith

theorem pauliBornProbability_sum_one
    (theta : RLSVector 3) (j : Fin 3) :
    ∑ outcome : Bool, pauliBornProbability theta j outcome = 1 := by
  simp [pauliBornProbability]
  ring

/-- Physical Bloch coordinates imply a uniform residual bound. -/
theorem abs_pauliRegressionNoise_le_two
    (theta : RLSVector 3) (j : Fin 3)
    (hlower : -1 ≤ theta j) (hupper : theta j ≤ 1)
    (outcome : Bool) :
    |pauliRegressionNoise theta j outcome| ≤ 2 := by
  cases outcome <;>
    simp [pauliRegressionNoise, pauliOutcomeSign, abs_le] <;>
    constructor <;> linarith

end

end QubitOracle.Paper
