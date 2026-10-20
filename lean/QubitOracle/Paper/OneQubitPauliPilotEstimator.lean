import QubitOracle.Paper.OneQubitPauliBlockRLS

/-!
# Explicit three-Pauli pilot estimator

For `q` complete pilot blocks, each Cartesian Bloch coordinate is estimated by
the average of its `q` Pauli signs.  This is the ordinary least-squares
estimator for the exact Born linear regression and is a deterministic special
case of RLS.
-/

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

abbrev PauliPilotPath (q : ℕ) := Fin q → Fin 3 → Bool

def pauliPilotCoordinateSum
    {q : ℕ} (path : PauliPilotPath q) (j : Fin 3) : ℝ :=
  ∑ b : Fin q, pauliOutcomeSign (path b j)

def pauliPilotEstimate
    {q : ℕ} (path : PauliPilotPath q) : RLSVector 3 :=
  fun j => (q : ℝ)⁻¹ * pauliPilotCoordinateSum path j

/-- The coordinate normal equation for ordinary least squares. -/
theorem pauliPilotEstimate_normalEquation
    {q : ℕ} (hq : 0 < q) (path : PauliPilotPath q) (j : Fin 3) :
    ∑ b : Fin q,
      (pauliOutcomeSign (path b j) - pauliPilotEstimate path j) = 0 := by
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold pauliPilotEstimate pauliPilotCoordinateSum
  field_simp
  ring

/-- The estimation error is exactly the average of the centered Born
regression noises. -/
theorem pauliPilotEstimate_sub_truth
    {q : ℕ} (hq : 0 < q) (path : PauliPilotPath q)
    (theta : RLSVector 3) (j : Fin 3) :
    pauliPilotEstimate path j - theta j =
      (q : ℝ)⁻¹ *
        ∑ b : Fin q, pauliRegressionNoise theta j (path b j) := by
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  unfold pauliPilotEstimate pauliPilotCoordinateSum
  simp only [pauliRegressionNoise, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem pauliOutcomeSign_lower (outcome : Bool) :
    (-1 : ℝ) ≤ pauliOutcomeSign outcome := by
  cases outcome <;> simp [pauliOutcomeSign]

theorem pauliOutcomeSign_upper (outcome : Bool) :
    pauliOutcomeSign outcome ≤ 1 := by
  cases outcome <;> simp [pauliOutcomeSign]

/-- Every coordinate of the unprojected sample-mean pilot already lies in the
physical coordinate interval `[-1,1]`. -/
theorem pauliPilotEstimate_coordinate_bounds
    {q : ℕ} (hq : 0 < q) (path : PauliPilotPath q) (j : Fin 3) :
    -1 ≤ pauliPilotEstimate path j ∧ pauliPilotEstimate path j ≤ 1 := by
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hlower : -(q : ℝ) ≤ pauliPilotCoordinateSum path j := by
    calc
      -(q : ℝ) = ∑ _b : Fin q, (-1 : ℝ) := by simp
      _ ≤ ∑ b : Fin q, pauliOutcomeSign (path b j) :=
        Finset.sum_le_sum (fun b hb => pauliOutcomeSign_lower (path b j))
  have hupper : pauliPilotCoordinateSum path j ≤ (q : ℝ) := by
    calc
      ∑ b : Fin q, pauliOutcomeSign (path b j) ≤
          ∑ _b : Fin q, (1 : ℝ) :=
        Finset.sum_le_sum (fun b hb => pauliOutcomeSign_upper (path b j))
      _ = (q : ℝ) := by simp
  constructor
  · unfold pauliPilotEstimate
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hqReal).2 (by simpa using hlower)
  · unfold pauliPilotEstimate
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hqReal).2 (by simpa using hupper)

/-- The explicit estimator is the unique solution of the three coordinate
normal equations when at least one complete block is observed. -/
theorem pauliPilot_normalEquation_unique
    {q : ℕ} (hq : 0 < q) (path : PauliPilotPath q)
    (candidate : RLSVector 3)
    (hNormal : ∀ j : Fin 3,
      ∑ b : Fin q, (pauliOutcomeSign (path b j) - candidate j) = 0) :
    candidate = pauliPilotEstimate path := by
  funext j
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hCandidate := hNormal j
  have hEstimate := pauliPilotEstimate_normalEquation hq path j
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hCandidate hEstimate
  nlinarith

end

end QubitOracle.Paper
