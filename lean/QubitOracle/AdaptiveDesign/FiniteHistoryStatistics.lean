import QubitOracle.AdaptiveDesign.TangentGLSEstimator

/-! Measurability of arbitrary finite-history statistics. This includes the
chosen nearest ray and the GLS solve, without requiring a continuous global
choice of eigenvector or orthogonal complement. -/

namespace QubitOracle.AdaptiveDesign.FiniteHistoryStatistics

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian
open MeasureTheory SequentialRidgeController TangentGLS
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {O : Type} {E : Type*} [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O]

def extendPrefix (n : ℕ) (pref : Fin n → O) : AdaptiveInfinitePath O := by
  classical
  exact fun k => if hk : k < n then pref ⟨k,hk⟩ else Classical.choice inferInstance

theorem extendPrefix_agrees (n : ℕ) (path : AdaptiveInfinitePath O) (k : ℕ) (hk : k<n) :
    extendPrefix n (fun i : Fin n => path i) k = path k := by
  simp [extendPrefix, hk]

theorem prefix_eq_of_agrees (n : ℕ) (path path' : AdaptiveInfinitePath O)
    (h : ∀ k<n, path k = path' k) :
    adaptiveInfinitePathPrefix n path = adaptiveInfinitePathPrefix n path' := by
  apply AdaptiveTrajectory.outcomes_injective
  rw [adaptiveInfinitePathPrefix_outcomes, adaptiveInfinitePathPrefix_outcomes]
  congr 1
  funext i
  exact h i i.isLt

theorem stronglyMeasurable_of_past [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (f : AdaptiveInfinitePath O → E)
    (hf : ∀ path path', (∀ k<n, path k = path' k) → f path = f path') :
    StronglyMeasurable f := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hg : Measurable (fun pref : Fin n → O => f (extendPrefix n pref)) := measurable_of_countable _
  have hp : Measurable (fun path : AdaptiveInfinitePath O => fun i : Fin n => path i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))
  convert (hg.comp hp).stronglyMeasurable using 1
  funext path
  exact hf _ _ (fun k hk => (extendPrefix_agrees n path k hk).symm)

variable {d : ℕ}

theorem actualState_eq_of_agrees
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath O) (h : ∀ k<n, path k = path' k) :
    GeneralPOVM.actualState P hI regularization hr batchSize path n =
      GeneralPOVM.actualState P hI regularization hr batchSize path' n := by
  unfold GeneralPOVM.actualState pathState
  rw [prefix_eq_of_agrees n path path' h]

theorem rawEstimator_eq_of_agrees
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath O) (h : ∀ k<n, path k = path' k) :
    GeneralPOVM.rawEstimator P hI regularization hr batchSize path n =
      GeneralPOVM.rawEstimator P hI regularization hr batchSize path' n := by
  unfold GeneralPOVM.rawEstimator
  rw [actualState_eq_of_agrees P hI regularization hr batchSize n path path' h]

theorem actualRecords_eq_of_agrees
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath O) (h : ∀ k<n, path k = path' k) :
    actualRecords P hI regularization hr batchSize path n =
      actualRecords P hI regularization hr batchSize path' n := by
  funext t
  unfold actualRecords
  rw [actualState_eq_of_agrees P hI regularization hr batchSize t path path'
    (fun k hk => h k (hk.trans t.isLt)), h t t.isLt]

/-- Any function of the raw estimate and the complete records is measurable.
Its definition may use a noncomputable deterministic selector or linear solve. -/
theorem actualStatistic_stronglyMeasurable
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (n : ℕ)
    (statistic : HermitianSpace (d+1) → (Fin n → Record d O) → E) :
    StronglyMeasurable (fun path => statistic
      (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n)
      (actualRecords P hI regularization hr batchSize path n)) := by
  apply stronglyMeasurable_of_past n
  intro path path' h
  rw [rawEstimator_eq_of_agrees P hI regularization hr batchSize n path path' h,
    actualRecords_eq_of_agrees P hI regularization hr batchSize n path path' h]

end
end QubitOracle.AdaptiveDesign.FiniteHistoryStatistics
