import QubitOracle.AdaptiveDesign.FiniteRegularOracle

/-!
# Exact composition of regular finite adaptive experiments

The second experiment is allowed to depend arbitrarily on the first record.
Its probabilities are differentiated with that record held fixed. This
proves the score-energy chain rule for an actual joint probability law.
-/

namespace QubitOracle.AdaptiveDesign.FiniteRegularOracle

open scoped BigOperators
noncomputable section

variable {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Ξ]

namespace RegularModel

/-- The joint law of an experiment followed by a record-dependent experiment. -/
def bind (P : RegularModel ι Ω) (Q : Ω → RegularModel ι Ξ)
    (hθ : ∀ w, (Q w).theta = P.theta) : RegularModel ι (Ω × Ξ) where
  theta := P.theta
  mass theta wv := P.mass theta wv.1 * (Q wv.1).mass theta wv.2
  nonneg theta wv := mul_nonneg (P.nonneg _ _) ((Q wv.1).nonneg _ _)
  total theta := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (Q _).total, mul_one, P.total]
  derivative wv j := P.derivative wv.1 j * (Q wv.1).mass P.theta wv.2 +
    P.mass P.theta wv.1 * (Q wv.1).derivative wv.2 j
  hasDerivative wv j := by
    have hq := (Q wv.1).hasDerivative wv.2 j
    rw [hθ] at hq
    convert (P.hasDerivative wv.1 j).mul hq using 1 <;>
      first | rfl | simp [shift]

theorem bind_score (P : RegularModel ι Ω) (Q : Ω → RegularModel ι Ξ)
    (hθ : ∀ w, (Q w).theta = P.theta) (w : Ω) (v : Ξ)
    (hp : P.mass P.theta w ≠ 0) (hq : (Q w).mass P.theta v ≠ 0) (j : ι) :
    (P.bind Q hθ).score (w,v) j = P.score w j + (Q w).score v j := by
  simp only [score, bind, hθ]
  field_simp

theorem linear_score_centered (P : RegularModel ι Ω) (b : ι → ℝ) :
    P.expectation (fun w => ∑ j, b j * P.score w j) = 0 := by
  unfold expectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, b j * P.expectation (fun w => P.score w j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 0 := by simp [P.score_centered]

theorem expectation_square_add (P : RegularModel ι Ω) (a : ℝ) (f : Ω → ℝ)
    (hf : P.expectation f = 0) :
    P.expectation (fun w => (a + f w)^2) = a^2 + P.expectation (fun w => (f w)^2) := by
  unfold expectation at *
  calc
    _ = a^2 * (∑ w, P.mass P.theta w) +
        2*a*(∑ w, P.mass P.theta w * f w) + ∑ w, P.mass P.theta w * (f w)^2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [P.total, hf]; ring

theorem expectation_vector_square_add (P : RegularModel ι Ω)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) :
    P.expectation (fun w => ∑ i, (a i + ∑ j, B i j * P.score w j)^2) =
      (∑ i, (a i)^2) + P.scoreEnergy B := by
  unfold expectation scoreEnergy
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ((a i)^2 + P.expectation (fun w => (∑ j, B i j * P.score w j)^2)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact P.expectation_square_add (a i) _ (P.linear_score_centered (B i))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      unfold expectation
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- The exact adaptive chain rule for the whitened information trace. -/
theorem bind_scoreEnergy (P : RegularModel ι Ω) (Q : Ω → RegularModel ι Ξ)
    (hθ : ∀ w, (Q w).theta = P.theta) (B : Matrix ι ι ℝ) :
    (P.bind Q hθ).scoreEnergy B = P.scoreEnergy B +
      P.expectation (fun w => (Q w).scoreEnergy B) := by
  unfold scoreEnergy expectation
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ w, P.mass P.theta w * (Q w).expectation (fun v =>
        ∑ i, ((∑ j, B i j * P.score w j) +
          ∑ j, B i j * (Q w).score v j)^2) := by
      apply Finset.sum_congr rfl
      intro w _
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hp : P.mass P.theta w = 0
      · simp [bind, hp]
      by_cases hq : (Q w).mass P.theta v = 0
      · simp [bind, hq, hθ]
      change (P.mass P.theta w * (Q w).mass P.theta v) *
        (∑ i, (∑ j, B i j * (P.bind Q hθ).score (w,v) j)^2) =
        P.mass P.theta w * ((Q w).mass (Q w).theta v * _)
      rw [hθ]
      rw [mul_assoc]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [P.bind_score Q hθ w v hp hq, mul_add, Finset.sum_add_distrib]
    _ = ∑ w, P.mass P.theta w * ((∑ i, (∑ j, B i j * P.score w j)^2) +
        (Q w).scoreEnergy B) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [(Q w).expectation_vector_square_add]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, scoreEnergy, expectation]

theorem bind_scoreEnergy_le (P : RegularModel ι Ω) (Q : Ω → RegularModel ι Ξ)
    (hθ : ∀ w, (Q w).theta = P.theta) (B : Matrix ι ι ℝ)
    (a b : ℝ) (hP : P.scoreEnergy B ≤ a) (hQ : ∀ w, (Q w).scoreEnergy B ≤ b) :
    (P.bind Q hθ).scoreEnergy B ≤ a + b := by
  rw [P.bind_scoreEnergy]
  apply add_le_add hP
  calc
    P.expectation (fun w => (Q w).scoreEnergy B) ≤ ∑ w, P.mass P.theta w * b := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (hQ w) (P.nonneg _ _)
    _ = b := by rw [← Finset.sum_mul, P.total, one_mul]

end RegularModel

/-- A regular model whose truth is the specified common coordinate value. -/
def AtTruth (theta : ι → ℝ) (Y : Type*) [Fintype Y] :=
  {P : RegularModel ι Y // P.theta = theta}

def emptyExperiment (theta : ι → ℝ) : AtTruth theta Unit :=
  ⟨{ theta := theta
     mass := fun _ _ => 1
     nonneg := by intros; norm_num
     total := by intros; simp
     derivative := fun _ _ => 0
     hasDerivative := by intros; exact hasDerivAt_const _ _ }, rfl⟩

def bindAt (theta : ι → ℝ) (P : AtTruth theta Ω)
    (Q : Ω → AtTruth theta Ξ) : AtTruth theta (Ω × Ξ) :=
  ⟨P.val.bind (fun w => (Q w).val) (fun w => (Q w).property.trans P.property.symm),
    P.property⟩

def Record (Y : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => Y × Record Y n

instance recordFintype {Y : Type} [Fintype Y] (n : ℕ) : Fintype (Record Y n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Y × Record Y n))

/-- The literal product law of an arbitrary finite adaptive decision tree.
The record determines the next model; no differentiability of the policy
as a function of the record is required. -/
def adaptiveExperiment {Y : Type} [Fintype Y] (theta : ι → ℝ)
    (step : List Y → AtTruth theta Y) :
    (n : ℕ) → List Y → AtTruth theta (Record Y n)
  | 0, _ => emptyExperiment theta
  | n+1, history => bindAt theta (step history)
      (fun y => adaptiveExperiment theta step n (y :: history))

/-- Summation of one-copy information budgets is a theorem of the product
law, rather than an assumption about the joint experiment. -/
theorem adaptive_scoreEnergy_le {Y : Type} [Fintype Y]
    (theta : ι → ℝ) (step : List Y → AtTruth theta Y)
    (B : Matrix ι ι ℝ) (budget : ℝ)
    (hstep : ∀ history, (step history).val.scoreEnergy B ≤ budget)
    (n : ℕ) (history : List Y) :
    (adaptiveExperiment theta step n history).val.scoreEnergy B ≤ (n : ℝ) * budget := by
  induction n generalizing history with
  | zero => simp [adaptiveExperiment, emptyExperiment, RegularModel.scoreEnergy,
      RegularModel.expectation, RegularModel.score]
  | succ n ih =>
      change ((step history).val.bind
        (fun y => (adaptiveExperiment theta step n (y :: history)).val)
        (fun y => (adaptiveExperiment theta step n (y :: history)).property.trans
          (step history).property.symm)).scoreEnergy B ≤ _
      have h := RegularModel.bind_scoreEnergy_le (step history).val
        (fun y => (adaptiveExperiment theta step n (y :: history)).val)
        (fun y => (adaptiveExperiment theta step n (y :: history)).property.trans
          (step history).property.symm) B
        budget ((n : ℝ) * budget) (hstep history) (fun y => ih (y :: history))
      convert h using 1 <;> push_cast <;> ring

/-- General finite adaptive oracle theorem, for arbitrary loss and score
factors, with explicitly differentiated probability laws and local unbiasedness. -/
theorem adaptive_oracle_bound {Y : Type} [Fintype Y]
    (theta : ι → ℝ) (step : List Y → AtTruth theta Y)
    (R B : Matrix ι ι ℝ) (budget : ℝ) (hbudget : 0 < budget)
    (hstep : ∀ history, (step history).val.scoreEnergy B ≤ budget)
    (n : ℕ) (T : Record Y n → ι → ℝ)
    (hT : (adaptiveExperiment theta step n []).val.LocallyUnbiased T) :
    (Matrix.trace (R * B.transpose))^2 / budget ≤
      (n : ℝ) * (adaptiveExperiment theta step n []).val.factorRisk R T := by
  exact RegularModel.oracle_bound_of_information_budget _ R B T hT n budget hbudget
    (adaptive_scoreEnergy_le theta step B budget hstep n [])

end
end QubitOracle.AdaptiveDesign.FiniteRegularOracle
