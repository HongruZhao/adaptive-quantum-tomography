import QubitOracle.Paper.OneQubitMixedExactCycleFiltrationBridge

/-!
# Exact-cycle Mathlib conditional-expectation closure

This file closes the finite-row bridge left by
`OneQubitMixedExactCycleFiltrationBridge`.  The probability measure is the
finite Dirac sum with coefficients equal to the explicit joint row mass.  A
split of a final path into its current bit and all remaining coordinates proves
the prefix-atom identity directly from the product Born law.  The resulting
atom identities are then summed over the finite history space and passed to
Mathlib's conditional-expectation uniqueness theorem.

Everything here concerns one fixed row.  No cross-row filtration nesting or
Gaussian convergence is asserted.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace QubitOracle.Paper
namespace MixedExactCycleScalarTriangularArrayData

attribute [local instance] Classical.propDecidable

/-! ## Splitting a finite final path at its current coordinate -/

abbrev CurrentDeletedFinalPath (n : ℕ) (t : Fin n) :=
  {path : MixedTwoStageFinalPath n // path t = false}

/-- A final path is equivalently its current bit together with the path whose
current coordinate has been reset to `false`. -/
def finalPathSplitAt (n : ℕ) (t : Fin n) :
    MixedTwoStageFinalPath n ≃ CurrentDeletedFinalPath n t × Bool where
  toFun path :=
    (⟨fun i => if i = t then false else path i, by simp⟩, path t)
  invFun qb := fun i => if i = t then qb.2 else qb.1.1 i
  left_inv path := by
    funext i
    by_cases hit : i = t
    · subst i
      simp
    · simp [hit]
  right_inv qb := by
    rcases qb with ⟨q, b⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      by_cases hit : i = t
      · subst i
        simp [q.property]
      · simp [hit]
    · simp

/-- Restore the current outcome into a path whose current coordinate is reset. -/
def restoreCurrentOutcome {n : ℕ} {t : Fin n}
    (q : CurrentDeletedFinalPath n t) (outcome : Bool) :
    MixedTwoStageFinalPath n :=
  (finalPathSplitAt n t).symm (q, outcome)

@[simp]
theorem restoreCurrentOutcome_apply_self {n : ℕ} {t : Fin n}
    (q : CurrentDeletedFinalPath n t) (outcome : Bool) :
    restoreCurrentOutcome q outcome t = outcome := by
  simp [restoreCurrentOutcome, finalPathSplitAt]

@[simp]
theorem restoreCurrentOutcome_apply_of_ne {n : ℕ} {t i : Fin n}
    (q : CurrentDeletedFinalPath n t) (outcome : Bool) (hit : i ≠ t) :
    restoreCurrentOutcome q outcome i = q.1 i := by
  simp [restoreCurrentOutcome, finalPathSplitAt, hit]

/-- Finite summation after exposing the current Boolean outcome. -/
theorem sum_finalPath_splitAt {n : ℕ} (t : Fin n)
    (F : MixedTwoStageFinalPath n → ℝ) :
    (∑ path, F path) =
      ∑ q : CurrentDeletedFinalPath n t,
        ∑ outcome : Bool, F (restoreCurrentOutcome q outcome) := by
  calc
    (∑ path, F path) =
        ∑ qb : CurrentDeletedFinalPath n t × Bool,
          F ((finalPathSplitAt n t).symm qb) :=
      Fintype.sum_equiv (finalPathSplitAt n t) _ _ (fun path => by simp)
    _ = ∑ q : CurrentDeletedFinalPath n t,
          ∑ outcome : Bool, F (restoreCurrentOutcome q outcome) := by
      rw [Fintype.sum_prod_type]
      rfl

/-! ## Product-law calculation on every prefix atom -/

variable (A : MixedExactCycleScalarTriangularArrayData)

/-- Product of all conditional Born factors except the current one. -/
noncomputable def offCurrentFinalMass (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (q : CurrentDeletedFinalPath (3 * r) t) : ℝ :=
  (Finset.univ.erase t).prod fun i =>
    mixedTwoStageFinalBornProbability
      A.theta (A.selected r) pilot i (q.1 i)

/-- The final-path product law factors into the current Born probability and
the product over all other coordinates. -/
theorem conditionalFinalPathMass_restoreCurrent (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (q : CurrentDeletedFinalPath (3 * r) t) (outcome : Bool) :
    mixedTwoStageConditionalFinalPathMass
        A.theta (A.selected r) pilot (restoreCurrentOutcome q outcome) =
      mixedTwoStageFinalBornProbability
          A.theta (A.selected r) pilot t outcome *
        A.offCurrentFinalMass r pilot t q := by
  unfold mixedTwoStageConditionalFinalPathMass offCurrentFinalMass
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    have hit : i ≠ t := (Finset.mem_erase.mp hi).1
    simp [hit]

/-- Revealing coordinates strictly before `t` does not reveal the outcome at
coordinate `t`. -/
theorem revealedFinalPrefix_restoreCurrent (r : ℕ)
    (t : Fin (3 * r)) (q : CurrentDeletedFinalPath (3 * r) t)
    (outcome : Bool) :
    A.revealedFinalPrefix r t.1 (restoreCurrentOutcome q outcome) =
      A.revealedFinalPrefix r t.1 q.1 := by
  funext i
  by_cases hi : i.1 < t.1
  · have hit : i ≠ t := by
      intro hit
      subst i
      exact (Nat.lt_irrefl t.1) hi
    simp [revealedFinalPrefix, hi, hit]
  · simp [revealedFinalPrefix, hi]

/-- All paths obtained by restoring the current outcome lie in the same
time-`t` prefix-history atom. -/
theorem historyProjection_restoreCurrent (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (q : CurrentDeletedFinalPath (3 * r) t) (outcome : Bool) :
    A.historyProjection r t.1
        (pilot, restoreCurrentOutcome q outcome) =
      A.historyProjection r t.1 (pilot, q.1) := by
  apply Prod.ext
  · rfl
  · exact A.revealedFinalPrefix_restoreCurrent r t q outcome

/-- The explicit joint row mass factors at the current coordinate. -/
theorem jointRowMass_restoreCurrent (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (q : CurrentDeletedFinalPath (3 * r) t) (outcome : Bool) :
    A.jointRowMass r (pilot, restoreCurrentOutcome q outcome) =
      pauliPilotPathMass A.theta pilot *
        (mixedTwoStageFinalBornProbability
            A.theta (A.selected r) pilot t outcome *
          A.offCurrentFinalMass r pilot t q) := by
  simp [jointRowMass, mixedTwoStageFiniteRowMass,
    A.conditionalFinalPathMass_restoreCurrent]

/-- The finite product law turns every exact one-step Born-kernel identity into
the corresponding prefix-atom integral identity.  This is the finite
calculation previously named by `MixedExactCycleMathlibCondExpAPIBridge`. -/
theorem exactFiniteStepConditionalExpectation_prefixAtomIntegralIdentity
    (r : ℕ) (t : Fin (3 * r))
    (observable : A.PilotSpace r → Bool → ℝ)
    (candidate : A.RowSpace r → ℝ)
    (hCE : A.ExactFiniteStepConditionalExpectation
      r t observable candidate) :
    A.PrefixAtomIntegralIdentity r t
      (A.currentCoordinateObservable r t observable) candidate := by
  classical
  intro baseRow
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pilot _
  rw [sum_finalPath_splitAt, sum_finalPath_splitAt]
  apply Finset.sum_congr rfl
  intro q _
  let p : Bool → ℝ := fun outcome =>
    mixedTwoStageFinalBornProbability
      A.theta (A.selected r) pilot t outcome
  let c : ℝ :=
    pauliPilotPathMass A.theta pilot * A.offCurrentFinalMass r pilot t q
  let m : ℝ := ∑ outcome : Bool, p outcome * observable pilot outcome
  have hMass (outcome : Bool) :
      A.jointRowMass r (pilot, restoreCurrentOutcome q outcome) =
        c * p outcome := by
    dsimp [c, p]
    rw [A.jointRowMass_restoreCurrent]
    cases outcome <;>
      simp [mixedTwoStageFinalBornProbability,
        mixedTwoStageAxisBornProbability,
        mixedTwoStageScore_blochDot_comm] <;> ring
  have hCandidate (outcome : Bool) :
      candidate (pilot, restoreCurrentOutcome q outcome) = m := by
    calc
      candidate (pilot, restoreCurrentOutcome q outcome) =
          candidate (pilot, q.1) :=
        hCE.prefixInvariant _ _
          (A.historyProjection_restoreCurrent r pilot t q outcome)
      _ = ∑ result : Bool,
          mixedTwoStageFinalBornProbability
              A.theta (A.selected r) pilot t result *
            observable pilot result :=
        hCE.bornKernelIdentity (pilot, q.1)
      _ = m := by rfl
  have hProbability : (∑ outcome : Bool, p outcome) = 1 := by
    simpa [p] using
      (mixedTwoStageFinalBornProbability_sum_one
        A.theta (A.selected r) pilot t)
  by_cases hHistory :
      A.historyProjection r t.1 (pilot, q.1) =
        A.historyProjection r t.1 baseRow
  · simp_rw [A.historyProjection_restoreCurrent, hHistory, if_true,
      hMass, hCandidate]
    simp only [currentCoordinateObservable,
      restoreCurrentOutcome_apply_self]
    change (∑ outcome : Bool, c * p outcome * m) =
      ∑ outcome : Bool, c * p outcome * observable pilot outcome
    calc
      (∑ outcome : Bool, c * p outcome * m) =
          c * m * (∑ outcome : Bool, p outcome) := by
        simp only [Fintype.sum_bool]
        ring
      _ = c * m := by rw [hProbability, mul_one]
      _ = ∑ outcome : Bool,
          c * p outcome * observable pilot outcome := by
        dsimp [m]
        rw [Finset.mul_sum]
        simp only [mul_assoc]
  · simp_rw [A.historyProjection_restoreCurrent]
    simp [hHistory]

/-- The previously named finite-row bridge is now a theorem, not a premise. -/
theorem mixedExactCycleMathlibCondExpAPIBridge_closed (r : ℕ) :
    A.MixedExactCycleMathlibCondExpAPIBridge r := by
  intro t observable candidate hCE
  exact A.exactFiniteStepConditionalExpectation_prefixAtomIntegralIdentity
    r t observable candidate hCE

/-! ## The explicit Mathlib probability measure -/

section MathlibProbability

variable (r : ℕ)

local instance rowSpaceMeasurableSpace : MeasurableSpace (A.RowSpace r) := ⊤

local instance historyKeyMeasurableSpace : MeasurableSpace (A.HistoryKey r) := ⊤

local instance rowSpaceMeasurableSingletonClass :
    MeasurableSingletonClass (A.RowSpace r) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-- The nonnegative real weight carried by one finite row atom. -/
noncomputable def rowNNRealWeight (row : A.RowSpace r) : NNReal := by
  exact ⟨A.jointRowMass r row, A.jointRowMass_nonnegative r row⟩

@[simp]
theorem rowNNRealWeight_coe (row : A.RowSpace r) :
    ((A.rowNNRealWeight r row : NNReal) : ℝ) = A.jointRowMass r row := by
  change (A.rowProbabilityMass r).atomMass row = A.jointRowMass r row
  rfl

theorem sum_rowNNRealWeight :
    (∑ row : A.RowSpace r, A.rowNNRealWeight r row) = 1 := by
  apply NNReal.eq
  simp only [NNReal.coe_sum, rowNNRealWeight_coe, NNReal.coe_one]
  exact A.jointRowMass_sum_one r

/-- Mathlib measure associated with the exact finite joint row law. -/
noncomputable def mathlibRowMeasure : Measure (A.RowSpace r) :=
  Measure.sum fun row : A.RowSpace r =>
    ENNReal.ofNNReal (A.rowNNRealWeight r row) • Measure.dirac row

/-- Event probabilities are finite sums over the row atoms. -/
theorem mathlibRowMeasure_apply (s : Set (A.RowSpace r)) :
    A.mathlibRowMeasure r s =
      ∑ row : A.RowSpace r,
        if row ∈ s then ENNReal.ofNNReal (A.rowNNRealWeight r row) else 0 := by
  classical
  rw [mathlibRowMeasure,
    Measure.sum_apply
      (fun row : A.RowSpace r =>
        ENNReal.ofNNReal (A.rowNNRealWeight r row) • Measure.dirac row)
      MeasurableSet.of_discrete,
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hrow : row ∈ s <;> simp [hrow]

@[simp]
theorem mathlibRowMeasure_univ :
    A.mathlibRowMeasure r Set.univ = 1 := by
  rw [A.mathlibRowMeasure_apply]
  simp only [Set.mem_univ, if_true]
  calc
    (∑ row : A.RowSpace r,
        ENNReal.ofNNReal (A.rowNNRealWeight r row)) =
        ENNReal.ofNNReal
          (∑ row : A.RowSpace r, A.rowNNRealWeight r row) := by
      symm
      simpa using ENNReal.coe_finset_sum
        (Finset.univ : Finset (A.RowSpace r))
        (fun row => A.rowNNRealWeight r row)
    _ = 1 := by
      rw [sum_rowNNRealWeight (A := A) (r := r)]
      rfl

noncomputable instance mathlibRowMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (A.mathlibRowMeasure r) where
  measure_univ := A.mathlibRowMeasure_univ r

/-- Every real function on a finite row is integrable for the explicit row
measure. -/
theorem integrable_mathlibRowMeasure (f : A.RowSpace r → ℝ) :
    Integrable f (A.mathlibRowMeasure r) := by
  exact Integrable.of_finite

/-- Bochner integration under the row measure is the expected finite weighted
sum. -/
theorem integral_mathlibRowMeasure (f : A.RowSpace r → ℝ) :
    (∫ row, f row ∂A.mathlibRowMeasure r) =
      ∑ row : A.RowSpace r, A.jointRowMass r row * f row := by
  simpa [mathlibRowMeasure, tsum_fintype, smul_eq_mul] using
    (MeasureTheory.integral_sum_dirac
      (f := f)
      (x := fun row : A.RowSpace r => row)
      (c := fun row : A.RowSpace r =>
        ENNReal.ofNNReal (A.rowNNRealWeight r row))
      (fun _ => by simp))

/-- Set integration under the row measure is the finite weighted sum with the
event indicator. -/
theorem setIntegral_mathlibRowMeasure (s : Set (A.RowSpace r))
    (f : A.RowSpace r → ℝ) :
    (∫ row in s, f row ∂A.mathlibRowMeasure r) =
      ∑ row : A.RowSpace r,
        if row ∈ s then A.jointRowMass r row * f row else 0 := by
  classical
  rw [← MeasureTheory.integral_indicator MeasurableSet.of_discrete,
    A.integral_mathlibRowMeasure]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hrow : row ∈ s <;> simp [hrow]

/-! ## Prefix atoms and finite-history summation -/

/-- The atom of rows sharing the time-`k` prefix history of `baseRow`. -/
def prefixHistoryAtom (k : ℕ) (baseRow : A.RowSpace r) :
    Set (A.RowSpace r) :=
  {row | A.historyProjection r k row =
    A.historyProjection r k baseRow}

/-- Measurable sets of the prefix comap sigma algebra are exactly preimages of
sets of finite history keys. -/
theorem measurableSet_rowFiltrationSigma_iff (k : ℕ)
    (s : Set (A.RowSpace r)) :
    MeasurableSet[A.rowFiltrationSigma r k] s ↔
      ∃ u : Set (A.HistoryKey r),
        s = (A.historyProjection r k) ⁻¹' u := by
  change (∃ u : Set (A.HistoryKey r),
      MeasurableSet[(⊤ : MeasurableSpace (A.HistoryKey r))] u ∧
        (A.historyProjection r k) ⁻¹' u = s) ↔ _
  constructor
  · rintro ⟨u, hu, hus⟩
    exact ⟨u, hus.symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, MeasurableSet.of_discrete, rfl⟩

/-- Every prefix-history atom is measurable in the corresponding row
filtration sigma algebra. -/
theorem prefixHistoryAtom_measurable (k : ℕ)
    (baseRow : A.RowSpace r) :
    MeasurableSet[A.rowFiltrationSigma r k]
      (A.prefixHistoryAtom r k baseRow) := by
  apply (A.measurableSet_rowFiltrationSigma_iff r k _).2
  refine ⟨{A.historyProjection r k baseRow}, ?_⟩
  ext row
  simp [prefixHistoryAtom]

/-- Finite weighted sum over one fiber of the history projection. -/
noncomputable def prefixFiberWeightedSum (k : ℕ) (key : A.HistoryKey r)
    (f : A.RowSpace r → ℝ) : ℝ := by
  classical
  exact ∑ row : A.RowSpace r,
    if A.historyProjection r k row = key then
      A.jointRowMass r row * f row
    else 0

/-- Finite weighted sum over the preimage of a set of histories. -/
noncomputable def historyPreimageWeightedSum (k : ℕ)
    (u : Set (A.HistoryKey r)) (f : A.RowSpace r → ℝ) : ℝ := by
  classical
  exact ∑ row : A.RowSpace r,
    if A.historyProjection r k row ∈ u then
      A.jointRowMass r row * f row
    else 0

/-- Regroup a finite row sum by the finite fibers of its history projection. -/
theorem historyPreimageWeightedSum_eq_sum_prefixFiber
    (k : ℕ) (u : Set (A.HistoryKey r))
    (f : A.RowSpace r → ℝ) :
    A.historyPreimageWeightedSum r k u f =
      ∑ key : A.HistoryKey r,
        if key ∈ u then A.prefixFiberWeightedSum r k key f else 0 := by
  classical
  unfold historyPreimageWeightedSum prefixFiberWeightedSum
  calc
    (∑ row : A.RowSpace r,
        if A.historyProjection r k row ∈ u then
          A.jointRowMass r row * f row else 0) =
      ∑ row : A.RowSpace r,
        ∑ key : A.HistoryKey r,
          if key = A.historyProjection r k row ∧ key ∈ u then
            A.jointRowMass r row * f row else 0 := by
      apply Finset.sum_congr rfl
      intro row _
      by_cases hrow : A.historyProjection r k row ∈ u
      · rw [if_pos hrow]
        symm
        calc
          (∑ key : A.HistoryKey r,
              if key = A.historyProjection r k row ∧ key ∈ u then
                A.jointRowMass r row * f row else 0) =
              (if A.historyProjection r k row =
                    A.historyProjection r k row ∧
                  A.historyProjection r k row ∈ u then
                A.jointRowMass r row * f row else 0) := by
            apply Fintype.sum_eq_single (A.historyProjection r k row)
            intro key hne
            simp [hne]
          _ = A.jointRowMass r row * f row := by simp [hrow]
      · rw [if_neg hrow]
        symm
        apply Fintype.sum_eq_zero
        intro key
        by_cases hkey : key = A.historyProjection r k row
        · subst key
          simp [hrow]
        · simp [hkey]
    _ = ∑ key : A.HistoryKey r,
        ∑ row : A.RowSpace r,
          if key = A.historyProjection r k row ∧ key ∈ u then
            A.jointRowMass r row * f row else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ key : A.HistoryKey r,
        if key ∈ u then
          ∑ row : A.RowSpace r,
            if A.historyProjection r k row = key then
              A.jointRowMass r row * f row else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro key _
      by_cases hkey : key ∈ u <;> simp [hkey, eq_comm]

/-- A prefix-atom identity yields equality on every fiber, including unrealized
history keys whose two fiber sums are both zero. -/
theorem prefixFiberWeightedSum_eq_of_prefixAtomIdentity
    (t : Fin (3 * r)) (randomVariable candidate : A.RowSpace r → ℝ)
    (hAtom : A.PrefixAtomIntegralIdentity
      r t randomVariable candidate) (key : A.HistoryKey r) :
    A.prefixFiberWeightedSum r t.1 key candidate =
      A.prefixFiberWeightedSum r t.1 key randomVariable := by
  classical
  by_cases hrealized :
      ∃ baseRow : A.RowSpace r,
        A.historyProjection r t.1 baseRow = key
  · rcases hrealized with ⟨baseRow, hbase⟩
    simpa [prefixFiberWeightedSum, hbase] using hAtom baseRow
  · have hnone : ∀ row : A.RowSpace r,
        A.historyProjection r t.1 row ≠ key := by
      intro row hrow
      exact hrealized ⟨row, hrow⟩
    simp [prefixFiberWeightedSum, hnone]

/-- Prefix-atom identities extend to every preimage of a set of history keys. -/
theorem historyPreimageWeightedSum_eq_of_prefixAtomIdentity
    (t : Fin (3 * r)) (randomVariable candidate : A.RowSpace r → ℝ)
    (hAtom : A.PrefixAtomIntegralIdentity
      r t randomVariable candidate) (u : Set (A.HistoryKey r)) :
    A.historyPreimageWeightedSum r t.1 u candidate =
      A.historyPreimageWeightedSum r t.1 u randomVariable := by
  rw [A.historyPreimageWeightedSum_eq_sum_prefixFiber,
    A.historyPreimageWeightedSum_eq_sum_prefixFiber]
  apply Finset.sum_congr rfl
  intro key _
  by_cases hkey : key ∈ u
  · simp only [hkey, if_true]
    exact A.prefixFiberWeightedSum_eq_of_prefixAtomIdentity
      r t randomVariable candidate hAtom key
  · simp [hkey]

/-- The finite bridge gives literal equality of the two Mathlib set integrals
on each measurable prefix-history event. -/
theorem setIntegral_eq_of_prefixAtomIdentity
    (t : Fin (3 * r)) (randomVariable candidate : A.RowSpace r → ℝ)
    (hAtom : A.PrefixAtomIntegralIdentity
      r t randomVariable candidate)
    (s : Set (A.RowSpace r))
    (hs : MeasurableSet[A.rowFiltrationSigma r t.1] s) :
    (∫ row in s, candidate row ∂A.mathlibRowMeasure r) =
      ∫ row in s, randomVariable row ∂A.mathlibRowMeasure r := by
  rcases (A.measurableSet_rowFiltrationSigma_iff r t.1 s).1 hs with
    ⟨u, rfl⟩
  rw [A.setIntegral_mathlibRowMeasure,
    A.setIntegral_mathlibRowMeasure]
  simpa [historyPreimageWeightedSum] using
    A.historyPreimageWeightedSum_eq_of_prefixAtomIdentity
      r t randomVariable candidate hAtom u

/-! ## Measurability of prefix-invariant candidates -/

/-- A chosen value on a history fiber, with zero on unrealized histories. -/
noncomputable def historyLift (k : ℕ) (g : A.RowSpace r → ℝ)
    (key : A.HistoryKey r) : ℝ :=
  if h : ∃ row : A.RowSpace r,
      A.historyProjection r k row = key then
    g (Classical.choose h)
  else 0

theorem historyLift_historyProjection (k : ℕ)
    (g : A.RowSpace r → ℝ)
    (hinvariant : ∀ row₁ row₂,
      A.historyProjection r k row₁ = A.historyProjection r k row₂ →
        g row₁ = g row₂)
    (row : A.RowSpace r) :
    A.historyLift r k g (A.historyProjection r k row) = g row := by
  classical
  unfold historyLift
  split
  · rename_i h
    exact hinvariant (Classical.choose h) row (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨row, rfl⟩).elim

/-- A real function constant on prefix-history fibers is measurable in the
prefix comap sigma algebra. -/
theorem measurable_of_history_invariant (k : ℕ)
    (g : A.RowSpace r → ℝ)
    (hinvariant : ∀ row₁ row₂,
      A.historyProjection r k row₁ = A.historyProjection r k row₂ →
        g row₁ = g row₂) :
    Measurable[A.rowFiltrationSigma r k] g := by
  intro s hs
  change ∃ u : Set (A.HistoryKey r),
    MeasurableSet[(⊤ : MeasurableSpace (A.HistoryKey r))] u ∧
      (A.historyProjection r k) ⁻¹' u = g ⁻¹' s
  refine ⟨(A.historyLift r k g) ⁻¹' s,
    MeasurableSet.of_discrete, ?_⟩
  ext row
  simp only [Set.mem_preimage]
  rw [A.historyLift_historyProjection r k g hinvariant row]

/-! ## Literal Mathlib conditional expectations -/

/-- Exact finite conditional expectation, now identified with Mathlib's
literal a.e. conditional expectation. -/
theorem exactFiniteStepConditionalExpectation_ae_eq_condExp
    (t : Fin (3 * r))
    (observable : A.PilotSpace r → Bool → ℝ)
    (candidate : A.RowSpace r → ℝ)
    (hCE : A.ExactFiniteStepConditionalExpectation
      r t observable candidate) :
    candidate =ᵐ[A.mathlibRowMeasure r]
      (A.mathlibRowMeasure r)[
        A.currentCoordinateObservable r t observable |
        A.rowFiltrationSigma r t.1] := by
  let randomVariable := A.currentCoordinateObservable r t observable
  have hAtom : A.PrefixAtomIntegralIdentity
      r t randomVariable candidate :=
    A.exactFiniteStepConditionalExpectation_prefixAtomIntegralIdentity
      r t observable candidate hCE
  apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (m₀ := (⊤ : MeasurableSpace (A.RowSpace r)))
    (m := A.rowFiltrationSigma r t.1)
    (μ := A.mathlibRowMeasure r)
    (f := randomVariable)
    (g := candidate)
    (hm := le_top)
  · exact A.integrable_mathlibRowMeasure r randomVariable
  · intro s hs hfinite
    exact (A.integrable_mathlibRowMeasure r candidate).integrableOn
  · intro s hs hfinite
    exact A.setIntegral_eq_of_prefixAtomIdentity
      r t randomVariable candidate hAtom s hs
  · exact (A.measurable_of_history_invariant
      r t.1 candidate hCE.prefixInvariant).aestronglyMeasurable

/-- Literal martingale-difference identity for one normalized score increment. -/
theorem scoreIncrement_literal_condExp_zero (t : Fin (3 * r)) :
    (A.mathlibRowMeasure r)[
      A.currentCoordinateObservable r t (A.scoreObservable r t) |
      A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
      (fun _ : A.RowSpace r => (0 : ℝ)) := by
  exact (A.exactFiniteStepConditionalExpectation_ae_eq_condExp
    r t (A.scoreObservable r t) (fun _ => 0)
    (A.scoreIncrement_finiteConditionalExpectation_zero r t)).symm

/-- Literal conditional squared-score identity for one time step. -/
theorem squaredScore_literal_condExp_eq_oneShotFisher
    (hr : 0 < r) (t : Fin (3 * r)) :
    (A.mathlibRowMeasure r)[
      A.currentCoordinateObservable r t (A.squaredScoreObservable r t) |
      A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
      A.oneShotFisherKernel r t := by
  exact (A.exactFiniteStepConditionalExpectation_ae_eq_condExp
    r t (A.squaredScoreObservable r t) (A.oneShotFisherKernel r t)
    (A.squaredScore_finiteConditionalExpectation_eq_oneShotFisher
      r hr t)).symm

/-- Literal conditional Lindeberg identity for one time step. -/
theorem lindebergObservable_literal_condExp_eq_kernel
    (t : Fin (3 * r)) (epsilon : ℝ) :
    (A.mathlibRowMeasure r)[
      A.currentCoordinateObservable r t
        (A.lindebergObservable r t epsilon) |
      A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
      A.oneShotLindebergKernel r t epsilon := by
  exact (A.exactFiniteStepConditionalExpectation_ae_eq_condExp
    r t (A.lindebergObservable r t epsilon)
      (A.oneShotLindebergKernel r t epsilon)
    (A.lindeberg_finiteConditionalExpectation_eq_kernel
      r t epsilon)).symm

/-- The row score is a literal Mathlib martingale-difference row. -/
theorem literal_martingaleDifference_row :
    ∀ t : Fin (3 * r),
      (A.mathlibRowMeasure r)[
        A.currentCoordinateObservable r t (A.scoreObservable r t) |
        A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
        (fun _ : A.RowSpace r => (0 : ℝ)) := by
  intro t
  exact A.scoreIncrement_literal_condExp_zero r t

/-- Literal predictable-quadratic-variation statement: every predictable
summand is the corresponding Mathlib conditional squared expectation, and the
finite sum of those kernels is the explicit normalized Fisher expression. -/
theorem literal_predictableQuadraticVariation (hr : 0 < r) :
    (∀ t : Fin (3 * r),
      (A.mathlibRowMeasure r)[
        A.currentCoordinateObservable r t (A.squaredScoreObservable r t) |
        A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
        A.oneShotFisherKernel r t) ∧
      A.predictableQuadraticVariation r =
        (fun row => A.explicitNormalizedFisher r row.1) := by
  constructor
  · intro t
    exact A.squaredScore_literal_condExp_eq_oneShotFisher r hr t
  · funext row
    exact A.predictableQuadraticVariation_eq_explicitNormalizedFisher r row

/-- Literal conditional Lindeberg statement together with the already proved
finite identity for the summed predictable Lindeberg expression. -/
theorem literal_predictableLindebergExpression (epsilon : ℝ) :
    (∀ t : Fin (3 * r),
      (A.mathlibRowMeasure r)[
        A.currentCoordinateObservable r t
          (A.lindebergObservable r t epsilon) |
        A.rowFiltrationSigma r t.1] =ᵐ[A.mathlibRowMeasure r]
        A.oneShotLindebergKernel r t epsilon) ∧
      A.predictableLindebergExpression r epsilon =
        (fun row => A.conditionalLindebergSum r row.1 epsilon) := by
  constructor
  · intro t
    exact A.lindebergObservable_literal_condExp_eq_kernel r t epsilon
  · funext row
    exact A.predictableLindebergExpression_eq_conditionalLindebergSum
      r epsilon row

end MathlibProbability

end MixedExactCycleScalarTriangularArrayData
end QubitOracle.Paper
