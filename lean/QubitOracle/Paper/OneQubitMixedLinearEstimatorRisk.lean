import QubitOracle.Paper.OneQubitPauliPilotBornProductLaw

/-!
# Exact mixed-qubit linear-estimator risk for complete Pauli blocks

This file is entirely finite and deterministic at the probability-law layer.
For `q > 0` complete blocks, it derives the first and second moments of the
three coordinate sample means from the explicit Pauli Born product mass.

The final section is only the canonical oracle calculation at the aligned
truth `(r, 0, 0)`.  It contains no pilot-adaptive or controller-transfer claim.
-/

open MeasureTheory
open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

local instance mixedLinearRiskPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedLinearRiskPathMeasurableSingletonClass (q : ℕ) :
    MeasurableSingletonClass (PauliPilotPath q) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-- Finite expectation under the explicit Pauli product mass.  Under the
physical Bloch condition this equals integration against
`pauliPilotBornProductMeasure`. -/
def pauliPilotFiniteExpectation
    {q : ℕ} (theta : RLSVector 3) (f : PauliPilotPath q → ℝ) : ℝ :=
  ∑ path : PauliPilotPath q, pauliPilotPathMass theta path * f path

/-- One-block version of the finite expectation. -/
def pauliPilotBlockFiniteExpectation
    (theta : RLSVector 3) (f : PauliPilotBlock → ℝ) : ℝ :=
  ∑ block : PauliPilotBlock, pauliPilotBlockMass theta block * f block

private theorem finite_product_expectation_factorization
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (p g : ι → α → ℝ) :
    (∑ x : ι → α,
        (∏ i : ι, p i (x i)) * (∏ i : ι, g i (x i))) =
      ∏ i : ι, ∑ a : α, p i a * g i a := by
  classical
  calc
    (∑ x : ι → α,
        (∏ i : ι, p i (x i)) * (∏ i : ι, g i (x i))) =
      ∑ x : ι → α, ∏ i : ι, p i (x i) * g i (x i) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.prod_mul_distrib]
    _ = ∏ i : ι, ∑ a : α, p i a * g i a := by
      exact (Fintype.prod_sum (fun i a => p i a * g i a)).symm

private theorem pauliPilotBlockFiniteExpectation_product
    (theta : RLSVector 3) (g : Fin 3 → Bool → ℝ) :
    pauliPilotBlockFiniteExpectation theta
        (fun block => ∏ j : Fin 3, g j (block j)) =
      ∏ j : Fin 3,
        ∑ outcome : Bool,
          pauliBornProbability theta j outcome * g j outcome := by
  simpa [pauliPilotBlockFiniteExpectation, pauliPilotBlockMass] using
    (finite_product_expectation_factorization
      (p := fun j : Fin 3 => pauliBornProbability theta j) g)

private theorem pauliPilotFiniteExpectation_blockProduct
    {q : ℕ} (theta : RLSVector 3)
    (g : Fin q → PauliPilotBlock → ℝ) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path => ∏ b : Fin q, g b (path b)) =
      ∏ b : Fin q,
        pauliPilotBlockFiniteExpectation theta (g b) := by
  simpa [pauliPilotFiniteExpectation, pauliPilotPathMass,
    pauliPilotBlockFiniteExpectation] using
    (finite_product_expectation_factorization
      (p := fun _b : Fin q => pauliPilotBlockMass theta) g)

private theorem finite_prod_single_selector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (v : ι → ℝ) :
    (∏ i : ι, if i = a then v i else 1) = v a := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro i hi hia
    simp [hia]
  · simp

/-! ## Elementary finite-expectation calculus -/

theorem pauliPilotFiniteExpectation_const
    {q : ℕ} (theta : RLSVector 3) (c : ℝ) :
    pauliPilotFiniteExpectation (q := q) theta (fun _path : PauliPilotPath q => c) = c := by
  unfold pauliPilotFiniteExpectation
  rw [← Finset.sum_mul, pauliPilotPathMass_sum_one, one_mul]

theorem pauliPilotFiniteExpectation_add
    {q : ℕ} (theta : RLSVector 3)
    (f g : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation (q := q) theta (fun path => f path + g path) =
      pauliPilotFiniteExpectation (q := q) theta f +
        pauliPilotFiniteExpectation (q := q) theta g := by
  simp only [pauliPilotFiniteExpectation, mul_add, Finset.sum_add_distrib]

theorem pauliPilotFiniteExpectation_sub
    {q : ℕ} (theta : RLSVector 3)
    (f g : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation (q := q) theta (fun path => f path - g path) =
      pauliPilotFiniteExpectation (q := q) theta f -
        pauliPilotFiniteExpectation (q := q) theta g := by
  simp only [pauliPilotFiniteExpectation, mul_sub, Finset.sum_sub_distrib]

theorem pauliPilotFiniteExpectation_const_mul
    {q : ℕ} (theta : RLSVector 3) (c : ℝ)
    (f : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation (q := q) theta (fun path => c * f path) =
      c * pauliPilotFiniteExpectation (q := q) theta f := by
  unfold pauliPilotFiniteExpectation
  calc
    (∑ path : PauliPilotPath q,
        pauliPilotPathMass theta path * (c * f path)) =
      ∑ path : PauliPilotPath q,
        c * (pauliPilotPathMass theta path * f path) := by
          apply Finset.sum_congr rfl
          intro path hpath
          ring
    _ = c * ∑ path : PauliPilotPath q,
        pauliPilotPathMass theta path * f path := by
          rw [Finset.mul_sum]

theorem pauliPilotFiniteExpectation_fintype_sum
    {q : ℕ} {ι : Type*} [Fintype ι]
    (theta : RLSVector 3) (f : ι → PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation (q := q) theta (fun path => ∑ i : ι, f i path) =
      ∑ i : ι, pauliPilotFiniteExpectation (q := q) theta (fun path => f i path) := by
  classical
  unfold pauliPilotFiniteExpectation
  calc
    (∑ path : PauliPilotPath q,
        pauliPilotPathMass theta path * ∑ i : ι, f i path) =
      ∑ path : PauliPilotPath q,
        ∑ i : ι, pauliPilotPathMass theta path * f i path := by
          apply Finset.sum_congr rfl
          intro path hpath
          rw [Finset.mul_sum]
    _ = ∑ i : ι,
        ∑ path : PauliPilotPath q,
          pauliPilotPathMass theta path * f i path := by
          rw [Finset.sum_comm]

/-! ## Exact one- and two-sign moments from product independence -/

theorem pauliOutcomeSign_mul_self (outcome : Bool) :
    pauliOutcomeSign outcome * pauliOutcomeSign outcome = 1 := by
  cases outcome <;> norm_num [pauliOutcomeSign]

private def pauliBlockPairAxisFactor
    (j k i : Fin 3) (outcome : Bool) : ℝ :=
  (if i = j then pauliOutcomeSign outcome else 1) *
    (if i = k then pauliOutcomeSign outcome else 1)

private theorem pauliBlockPairAxisFactor_product
    (j k : Fin 3) (block : PauliPilotBlock) :
    (∏ i : Fin 3, pauliBlockPairAxisFactor j k i (block i)) =
      pauliOutcomeSign (block j) * pauliOutcomeSign (block k) := by
  unfold pauliBlockPairAxisFactor
  rw [Finset.prod_mul_distrib]
  simp only [finite_prod_single_selector]

private theorem pauliPilotBlock_twoSign_mean_of_ne
    (theta : RLSVector 3) (j k : Fin 3) (hjk : j ≠ k) :
    pauliPilotBlockFiniteExpectation theta
        (fun block =>
          pauliOutcomeSign (block j) * pauliOutcomeSign (block k)) =
      theta j * theta k := by
  calc
    pauliPilotBlockFiniteExpectation theta
        (fun block =>
          pauliOutcomeSign (block j) * pauliOutcomeSign (block k)) =
      pauliPilotBlockFiniteExpectation theta
        (fun block =>
          ∏ i : Fin 3, pauliBlockPairAxisFactor j k i (block i)) := by
            unfold pauliPilotBlockFiniteExpectation
            apply Finset.sum_congr rfl
            intro block hblock
            exact congrArg
              (fun x : ℝ => pauliPilotBlockMass theta block * x)
              (pauliBlockPairAxisFactor_product j k block).symm
    _ = ∏ i : Fin 3,
        ∑ outcome : Bool,
          pauliBornProbability theta i outcome *
            pauliBlockPairAxisFactor j k i outcome :=
      pauliPilotBlockFiniteExpectation_product theta
        (pauliBlockPairAxisFactor j k)
    _ = ∏ i : Fin 3,
        (if i = j then theta j else 1) *
          (if i = k then theta k else 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hij : i = j
            · subst i
              simpa [pauliBlockPairAxisFactor, hjk] using
                (pauliBornProbability_sign_mean theta j)
            · by_cases hik : i = k
              · subst i
                simpa [pauliBlockPairAxisFactor, Ne.symm hjk] using
                  (pauliBornProbability_sign_mean theta k)
              · simpa [pauliBlockPairAxisFactor, hij, hik] using
                  (pauliBornProbability_sum_one theta i)
    _ = theta j * theta k := by
      rw [Finset.prod_mul_distrib]
      simp only [finite_prod_single_selector]

/-- Within one complete block, distinct Pauli axes are independent and an
identical signed outcome has second moment one. -/
theorem pauliPilotBlock_twoSign_mean
    (theta : RLSVector 3) (j k : Fin 3) :
    pauliPilotBlockFiniteExpectation theta
        (fun block =>
          pauliOutcomeSign (block j) * pauliOutcomeSign (block k)) =
      if j = k then 1 else theta j * theta k := by
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    unfold pauliPilotBlockFiniteExpectation
    calc
      (∑ block : PauliPilotBlock,
          pauliPilotBlockMass theta block *
            (pauliOutcomeSign (block j) * pauliOutcomeSign (block j))) =
        ∑ block : PauliPilotBlock, pauliPilotBlockMass theta block := by
          apply Finset.sum_congr rfl
          intro block hblock
          rw [pauliOutcomeSign_mul_self, mul_one]
      _ = 1 := pauliPilotBlockMass_sum_one theta
  · rw [if_neg hjk]
    exact pauliPilotBlock_twoSign_mean_of_ne theta j k hjk

private def pauliPathPairBlockFactor
    {q : ℕ} (b : Fin q) (j : Fin 3) (c : Fin q) (k : Fin 3)
    (i : Fin q) (block : PauliPilotBlock) : ℝ :=
  (if i = b then pauliOutcomeSign (block j) else 1) *
    (if i = c then pauliOutcomeSign (block k) else 1)

private theorem pauliPathPairBlockFactor_product
    {q : ℕ} (b : Fin q) (j : Fin 3) (c : Fin q) (k : Fin 3)
    (path : PauliPilotPath q) :
    (∏ i : Fin q, pauliPathPairBlockFactor b j c k i (path i)) =
      pauliOutcomeSign (path b j) * pauliOutcomeSign (path c k) := by
  unfold pauliPathPairBlockFactor
  rw [Finset.prod_mul_distrib]
  simp only [finite_prod_single_selector]

/-- Raw two-sign moment for arbitrary block-axis slots.  The only repeated
random variable is the identical pair `b = c ∧ j = k`; all other pairs factor. -/
theorem pauliPilotPath_twoSign_mean
    {q : ℕ} (theta : RLSVector 3)
    (b : Fin q) (j : Fin 3) (c : Fin q) (k : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path =>
          pauliOutcomeSign (path b j) * pauliOutcomeSign (path c k)) =
      if b = c ∧ j = k then 1 else theta j * theta k := by
  by_cases hbc : b = c
  · subst c
    calc
      pauliPilotFiniteExpectation (q := q) theta
          (fun path =>
            pauliOutcomeSign (path b j) * pauliOutcomeSign (path b k)) =
        pauliPilotFiniteExpectation (q := q) theta
          (fun path =>
            ∏ i : Fin q, pauliPathPairBlockFactor b j b k i (path i)) := by
              unfold pauliPilotFiniteExpectation
              apply Finset.sum_congr rfl
              intro path hpath
              exact congrArg
                (fun x : ℝ => pauliPilotPathMass theta path * x)
                (pauliPathPairBlockFactor_product b j b k path).symm
      _ = ∏ i : Fin q,
          pauliPilotBlockFiniteExpectation theta
            (pauliPathPairBlockFactor b j b k i) :=
        pauliPilotFiniteExpectation_blockProduct theta
          (pauliPathPairBlockFactor b j b k)
      _ = ∏ i : Fin q,
          if i = b then
            pauliPilotBlockFiniteExpectation theta
              (fun block =>
                pauliOutcomeSign (block j) * pauliOutcomeSign (block k))
          else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hib : i = b
            · subst i
              simp only [if_pos rfl]
              apply congrArg (pauliPilotBlockFiniteExpectation theta)
              funext block
              simp [pauliPathPairBlockFactor]
            · simpa [pauliPilotBlockFiniteExpectation,
                pauliPathPairBlockFactor, hib] using
                (pauliPilotBlockMass_sum_one theta)
      _ = pauliPilotBlockFiniteExpectation theta
            (fun block =>
              pauliOutcomeSign (block j) * pauliOutcomeSign (block k)) := by
            exact finite_prod_single_selector b
              (fun _i : Fin q =>
                pauliPilotBlockFiniteExpectation theta
                  (fun block =>
                    pauliOutcomeSign (block j) * pauliOutcomeSign (block k)))
      _ = if j = k then 1 else theta j * theta k :=
        pauliPilotBlock_twoSign_mean theta j k
      _ = if b = b ∧ j = k then 1 else theta j * theta k := by simp
  · calc
      pauliPilotFiniteExpectation (q := q) theta
          (fun path =>
            pauliOutcomeSign (path b j) * pauliOutcomeSign (path c k)) =
        pauliPilotFiniteExpectation (q := q) theta
          (fun path =>
            ∏ i : Fin q, pauliPathPairBlockFactor b j c k i (path i)) := by
              unfold pauliPilotFiniteExpectation
              apply Finset.sum_congr rfl
              intro path hpath
              exact congrArg
                (fun x : ℝ => pauliPilotPathMass theta path * x)
                (pauliPathPairBlockFactor_product b j c k path).symm
      _ = ∏ i : Fin q,
          pauliPilotBlockFiniteExpectation theta
            (pauliPathPairBlockFactor b j c k i) :=
        pauliPilotFiniteExpectation_blockProduct theta
          (pauliPathPairBlockFactor b j c k)
      _ = ∏ i : Fin q,
          (if i = b then theta j else 1) *
            (if i = c then theta k else 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hib : i = b
            · subst i
              simpa [pauliPilotBlockFiniteExpectation,
                pauliPathPairBlockFactor, hbc] using
                (pauliPilotBlock_sign_mean theta j)
            · by_cases hic : i = c
              · subst i
                simpa [pauliPilotBlockFiniteExpectation,
                    pauliPathPairBlockFactor, Ne.symm hbc] using
                  (pauliPilotBlock_sign_mean theta k)
              · simpa [pauliPilotBlockFiniteExpectation,
                  pauliPathPairBlockFactor, hib, hic] using
                  (pauliPilotBlockMass_sum_one theta)
      _ = theta j * theta k := by
        rw [Finset.prod_mul_distrib]
        simp only [finite_prod_single_selector]
      _ = if b = c ∧ j = k then 1 else theta j * theta k := by
        simp [hbc]

/-- Exact mean of every signed Pauli observation. -/
theorem pauliPilotCoordinateSign_mean
    {q : ℕ} (theta : RLSVector 3) (b : Fin q) (j : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path => pauliOutcomeSign (path b j)) = theta j := by
  unfold pauliPilotFiniteExpectation
  calc
    (∑ path : PauliPilotPath q,
        pauliPilotPathMass theta path * pauliOutcomeSign (path b j)) =
      ∑ block : PauliPilotBlock,
        pauliPilotBlockMass theta block * pauliOutcomeSign (block j) := by
          simpa using
            (pauliPilotPath_singleBlock_mean theta b
              (fun block => pauliOutcomeSign (block j)))
    _ = theta j := pauliPilotBlock_sign_mean theta j

/-- Centered two-sign moments.  Every off-slot term is exactly zero. -/
theorem pauliPilotCenteredCoordinateProduct_mean
    {q : ℕ} (theta : RLSVector 3)
    (b : Fin q) (j : Fin 3) (c : Fin q) (k : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path =>
          (pauliOutcomeSign (path b j) - theta j) *
            (pauliOutcomeSign (path c k) - theta k)) =
      if b = c ∧ j = k then 1 - theta j ^ 2 else 0 := by
  have hexpand :
      (fun path : PauliPilotPath q =>
        (pauliOutcomeSign (path b j) - theta j) *
          (pauliOutcomeSign (path c k) - theta k)) =
      (fun path : PauliPilotPath q =>
        pauliOutcomeSign (path b j) * pauliOutcomeSign (path c k) -
          theta k * pauliOutcomeSign (path b j) -
          theta j * pauliOutcomeSign (path c k) + theta j * theta k) := by
    funext path
    ring
  rw [hexpand, pauliPilotFiniteExpectation_add,
    pauliPilotFiniteExpectation_sub, pauliPilotFiniteExpectation_sub,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const]
  rw [pauliPilotPath_twoSign_mean,
    pauliPilotCoordinateSign_mean,
    pauliPilotCoordinateSign_mean]
  by_cases hbc : b = c
  · subst c
    by_cases hjk : j = k
    · subst k
      simp
      ring
    · simp [hjk]
      ring
  · simp [hbc]
    ring

private theorem finite_pair_diagonal_sum
    {q : ℕ} (a : ℝ) :
    (∑ b : Fin q, ∑ c : Fin q, if b = c then a else 0) = (q : ℝ) * a := by
  calc
    (∑ b : Fin q, ∑ c : Fin q, if b = c then a else 0) =
      ∑ b : Fin q, a := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_eq_single b]
        · simp
        · intro c hc hcb
          simp [Ne.symm hcb]
        · simp
    _ = (q : ℝ) * a := by simp

/-! ## Exact moments of the linear estimator -/

/-- Exact unbiasedness of each Pauli sample-mean coordinate. -/
theorem pauliPilotEstimate_unbiased
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3) (j : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta (fun path => pauliPilotEstimate (q := q) path j) =
      theta j := by
  have hqReal : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  unfold pauliPilotEstimate pauliPilotCoordinateSum
  rw [pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_fintype_sum]
  simp_rw [pauliPilotCoordinateSign_mean theta]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- Exact covariance matrix of the three-coordinate sample mean. -/
theorem pauliPilotEstimate_covariance
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3) (j k : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path =>
          (pauliPilotEstimate (q := q) path j - theta j) *
            (pauliPilotEstimate (q := q) path k - theta k)) =
      if j = k then (1 - theta j ^ 2) / (q : ℝ) else 0 := by
  have herror :
      (fun path : PauliPilotPath q =>
        (pauliPilotEstimate (q := q) path j - theta j) *
          (pauliPilotEstimate (q := q) path k - theta k)) =
      (fun path : PauliPilotPath q =>
        ((q : ℝ)⁻¹) ^ 2 *
          ∑ b : Fin q, ∑ c : Fin q,
            (pauliOutcomeSign (path b j) - theta j) *
              (pauliOutcomeSign (path c k) - theta k)) := by
    funext path
    rw [pauliPilotEstimate_sub_truth hq path theta j,
      pauliPilotEstimate_sub_truth hq path theta k]
    simp only [pauliRegressionNoise]
    calc
      ((q : ℝ)⁻¹ *
          ∑ b : Fin q, (pauliOutcomeSign (path b j) - theta j)) *
          ((q : ℝ)⁻¹ *
            ∑ c : Fin q, (pauliOutcomeSign (path c k) - theta k)) =
        ((q : ℝ)⁻¹) ^ 2 *
          ((∑ b : Fin q, (pauliOutcomeSign (path b j) - theta j)) *
            (∑ c : Fin q, (pauliOutcomeSign (path c k) - theta k))) := by
              ring
      _ = ((q : ℝ)⁻¹) ^ 2 *
          ∑ b : Fin q, ∑ c : Fin q,
            (pauliOutcomeSign (path b j) - theta j) *
              (pauliOutcomeSign (path c k) - theta k) := by
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
  rw [herror, pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_fintype_sum]
  simp_rw [pauliPilotFiniteExpectation_fintype_sum]
  simp_rw [pauliPilotCenteredCoordinateProduct_mean]
  by_cases hjk : j = k
  · subst k
    simp only [and_true]
    rw [finite_pair_diagonal_sum]
    simp only [if_true]
    have hqReal : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hq)
    field_simp [hqReal]
    <;> ring
  · simp [hjk]

/-- Coordinate variance `(1 - theta_j^2) / q`. -/
theorem pauliPilotEstimate_coordinateVariance
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3) (j : Fin 3) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path => (pauliPilotEstimate (q := q) path j - theta j) ^ 2) =
      (1 - theta j ^ 2) / (q : ℝ) := by
  simpa [pow_two] using
    (pauliPilotEstimate_covariance hq theta j j)

/-- Distinct estimator coordinates have exactly zero covariance. -/
theorem pauliPilotEstimate_crossCovariance_zero
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3)
    (j k : Fin 3) (hjk : j ≠ k) :
    pauliPilotFiniteExpectation (q := q) theta
        (fun path =>
          (pauliPilotEstimate (q := q) path j - theta j) *
            (pauliPilotEstimate (q := q) path k - theta k)) = 0 := by
  simpa [hjk] using pauliPilotEstimate_covariance hq theta j k

/-! ## Integral forms under the physical product probability law -/

theorem integral_pauliPilotEstimate_unbiased
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) (j : Fin 3) :
    (∫ path, pauliPilotEstimate (q := q) path j
      ∂pauliPilotBornProductMeasure (q := q) theta) = theta j := by
  rw [integral_pauliPilotBornProductMeasure (q := q) theta hphysical]
  simpa [pauliPilotFiniteExpectation] using
    (pauliPilotEstimate_unbiased hq theta j)

theorem integral_pauliPilotEstimate_coordinateVariance
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) (j : Fin 3) :
    (∫ path, (pauliPilotEstimate (q := q) path j - theta j) ^ 2
      ∂pauliPilotBornProductMeasure (q := q) theta) =
      (1 - theta j ^ 2) / (q : ℝ) := by
  rw [integral_pauliPilotBornProductMeasure (q := q) theta hphysical]
  simpa [pauliPilotFiniteExpectation] using
    (pauliPilotEstimate_coordinateVariance hq theta j)

theorem integral_pauliPilotEstimate_crossCovariance_zero
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (j k : Fin 3) (hjk : j ≠ k) :
    (∫ path,
      (pauliPilotEstimate (q := q) path j - theta j) *
        (pauliPilotEstimate (q := q) path k - theta k)
      ∂pauliPilotBornProductMeasure (q := q) theta) = 0 := by
  rw [integral_pauliPilotBornProductMeasure (q := q) theta hphysical]
  simpa [pauliPilotFiniteExpectation] using
    (pauliPilotEstimate_crossCovariance_zero hq theta j k hjk)

/-! ## Canonical truth-aligned mixed-qubit oracle calculation

This section deliberately stops before any pilot-estimator or adaptive-frame
transfer.  It is the exact calculation for a fixed oracle-aligned frame.
-/

namespace CanonicalMixedOracle

/-- Canonical aligned Bloch truth `(r, 0, 0)`. -/
def truthAlignedMixedBloch (r : ℝ) : RLSVector 3 :=
  fun j => if j = (0 : Fin 3) then r else 0

theorem truthAlignedMixedBloch_normSq (r : ℝ) :
    (∑ j : Fin 3, truthAlignedMixedBloch r j ^ 2) = r ^ 2 := by
  simp [truthAlignedMixedBloch, Fin.sum_univ_succ]

theorem truthAlignedMixedBloch_strictInterior
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∑ j : Fin 3, truthAlignedMixedBloch r j ^ 2) < 1 := by
  rw [truthAlignedMixedBloch_normSq]
  nlinarith

theorem truthAlignedMixedBloch_physical
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    PauliPilotPhysicalBloch (truthAlignedMixedBloch r) := by
  unfold PauliPilotPhysicalBloch
  exact le_of_lt (truthAlignedMixedBloch_strictInterior r hr0 hr1)

/-- Local squared-Bures quadratic metric with diagonal
`(1 / (4 * (1-r^2)), 1/4, 1/4)`. -/
def truthAlignedMixedSquaredBuresQuadratic
    (r : ℝ) (delta : RLSVector 3) : ℝ :=
  (4 * (1 - r ^ 2))⁻¹ * delta (0 : Fin 3) ^ 2 +
    (4 : ℝ)⁻¹ * delta (1 : Fin 3) ^ 2 +
    (4 : ℝ)⁻¹ * delta (2 : Fin 3) ^ 2

/-- Exact expected local quadratic Bures risk for `q` measurements of each
of the three Pauli axes. -/
theorem pauliPilot_truthAligned_buresRisk_exact
    {q : ℕ} (hq : 0 < q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    pauliPilotFiniteExpectation (q := q) (truthAlignedMixedBloch r)
        (fun path =>
          truthAlignedMixedSquaredBuresQuadratic r
            (fun j =>
              pauliPilotEstimate (q := q) path j - truthAlignedMixedBloch r j)) =
      3 / (4 * (q : ℝ)) := by
  unfold truthAlignedMixedSquaredBuresQuadratic
  rw [pauliPilotFiniteExpectation_add,
    pauliPilotFiniteExpectation_add,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const_mul]
  rw [pauliPilotEstimate_coordinateVariance hq
      (truthAlignedMixedBloch r) (0 : Fin 3),
    pauliPilotEstimate_coordinateVariance hq
      (truthAlignedMixedBloch r) (1 : Fin 3),
    pauliPilotEstimate_coordinateVariance hq
      (truthAlignedMixedBloch r) (2 : Fin 3)]
  have hOne : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
  have hTwo : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
  simp only [truthAlignedMixedBloch, if_pos, if_neg hOne, if_neg hTwo]
  have hqReal : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hradial : 1 - r ^ 2 ≠ 0 := by
    nlinarith
  field_simp [hqReal, hradial]
  <;> ring

/-- Integral form of the exact oracle risk under the physical Born law. -/
theorem integral_pauliPilot_truthAligned_buresRisk_exact
    {q : ℕ} (hq : 0 < q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ path,
      truthAlignedMixedSquaredBuresQuadratic r
        (fun j =>
          pauliPilotEstimate (q := q) path j - truthAlignedMixedBloch r j)
      ∂pauliPilotBornProductMeasure (q := q) (truthAlignedMixedBloch r)) =
      3 / (4 * (q : ℝ)) := by
  rw [integral_pauliPilotBornProductMeasure
    (truthAlignedMixedBloch r)
    (truthAlignedMixedBloch_physical r hr0 hr1)]
  simpa [pauliPilotFiniteExpectation] using
    (pauliPilot_truthAligned_buresRisk_exact hq r hr0 hr1)

/-- Total number of shots in `q` complete three-Pauli blocks. -/
def pauliPilotTotalShots (q : ℕ) : ℕ := 3 * q

/-- With `N = 3q` total shots, the exact oracle-scaled quadratic Bures risk is
`9/4`. -/
theorem pauliPilot_truthAligned_totalShots_buresRisk
    {q : ℕ} (hq : 0 < q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (pauliPilotTotalShots q : ℝ) *
        (∫ path,
          truthAlignedMixedSquaredBuresQuadratic r
            (fun j =>
              pauliPilotEstimate (q := q) path j - truthAlignedMixedBloch r j)
          ∂pauliPilotBornProductMeasure (q := q) (truthAlignedMixedBloch r)) =
      9 / 4 := by
  rw [integral_pauliPilot_truthAligned_buresRisk_exact hq r hr0 hr1]
  have hqReal : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  norm_num [pauliPilotTotalShots, Nat.cast_mul]
  field_simp [hqReal]
  norm_num

namespace Label

/-- Canonical fixed-frame mixed-qubit oracle risk identity.  This is not an
adaptive-transfer theorem. -/
theorem eq_mixed_linear_oracle_bures_risk_qubit
    {q : ℕ} (hq : 0 < q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (pauliPilotTotalShots q : ℝ) *
        (∫ path,
          truthAlignedMixedSquaredBuresQuadratic r
            (fun j =>
              pauliPilotEstimate (q := q) path j - truthAlignedMixedBloch r j)
          ∂pauliPilotBornProductMeasure (q := q) (truthAlignedMixedBloch r)) =
      9 / 4 :=
  pauliPilot_truthAligned_totalShots_buresRisk hq r hr0 hr1

end Label

end CanonicalMixedOracle

end

end QubitOracle.Paper
