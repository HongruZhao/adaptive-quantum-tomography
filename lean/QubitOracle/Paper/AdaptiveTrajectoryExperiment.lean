import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import QubitOracle.Paper.MartingaleCLT
namespace QubitOracle.Paper

open Filter Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v w

/-- A finite observed outcome history.  The law at horizon `n` is supported on
histories of length `n`; using one common sample type avoids artificial
identifications between differently parenthesized finite products. -/
structure AdaptiveTrajectory (Outcome : Type v) where
  outcomes : List Outcome

theorem AdaptiveTrajectory.outcomes_injective {Outcome : Type v} :
    Function.Injective (AdaptiveTrajectory.outcomes : AdaptiveTrajectory Outcome → List Outcome) := by
  intro x y h
  cases x
  cases y
  cases h
  rfl

instance {Outcome : Type v} [Countable Outcome] : Countable (AdaptiveTrajectory Outcome) :=
  AdaptiveTrajectory.outcomes_injective.countable

/-- Histories carry the discrete measurable space.  This matches the finite
or countable outcome spaces of the protocols in the paper. -/
instance adaptiveTrajectoryMeasurableSpace {Outcome : Type v} :
    MeasurableSpace (AdaptiveTrajectory Outcome) := ⊤

instance adaptiveTrajectoryMeasurableSingletonClass {Outcome : Type v} :
    MeasurableSingletonClass (AdaptiveTrajectory Outcome) where
  measurableSet_singleton _ := by trivial

def AdaptiveTrajectory.empty {Outcome : Type v} : AdaptiveTrajectory Outcome :=
  ⟨[]⟩

def AdaptiveTrajectory.snoc {Outcome : Type v}
    (history : AdaptiveTrajectory Outcome) (outcome : Outcome) : AdaptiveTrajectory Outcome :=
  ⟨history.outcomes ++ [outcome]⟩

/-- Appending one outcome is measurable for a countable measurable outcome
space with measurable singletons. -/
theorem measurable_adaptiveTrajectory_snoc
    {Outcome : Type v} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    [Countable Outcome] :
    Measurable
      (fun pair : AdaptiveTrajectory Outcome × Outcome => pair.1.snoc pair.2) :=
  measurable_of_countable _

/-- A predictable adaptive quantum/classical protocol after applying the Born
rule.  `Action` can be a POVM or any classical measurement setting,
`response h` is its outcome kernel at parameter `h`, and `design n` chooses
the next action measurably from only the observed past.

The absence of a future-outcome argument in `design n` is the formal
predictability condition. -/
structure PredictableAdaptiveProtocol
    (H : Type u) (Action : Type w) (Outcome : Type v)
    [MeasurableSpace Action] [MeasurableSpace Outcome] where
  response : H → Kernel Action Outcome
  response_isMarkov : ∀ h, IsMarkovKernel (response h)
  design : ℕ → AdaptiveTrajectory Outcome → Action
  design_measurable : ∀ n, Measurable (design n)

/-- The conditional law of the next outcome given the observed past. -/
def adaptiveStepKernel
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : Kernel (AdaptiveTrajectory Outcome) Outcome :=
  (protocol.response h).comap (protocol.design n) (protocol.design_measurable n)

@[simp]
theorem adaptiveStepKernel_apply
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) (history : AdaptiveTrajectory Outcome) :
    adaptiveStepKernel protocol h n history =
      protocol.response h (protocol.design n history) :=
  rfl

/-- Every induced history-dependent one-step law is a Markov kernel. -/
theorem adaptiveStepKernel_isMarkov
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : IsMarkovKernel (adaptiveStepKernel protocol h n) := by
  letI : IsMarkovKernel (protocol.response h) := protocol.response_isMarkov h
  simpa [adaptiveStepKernel] using
    Kernel.IsMarkovKernel.comap (protocol.response h) (protocol.design_measurable n)

/-- Jointly retain the past and sample the next outcome. -/
def trajectoryExperiment_adaptiveJointKernel
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) :
    Kernel (AdaptiveTrajectory Outcome) (AdaptiveTrajectory Outcome × Outcome) :=
  Kernel.id ×ₖ adaptiveStepKernel protocol h n

theorem adaptiveJointKernel_isMarkov
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : IsMarkovKernel (trajectoryExperiment_adaptiveJointKernel protocol h n) := by
  letI : IsMarkovKernel (adaptiveStepKernel protocol h n) :=
    adaptiveStepKernel_isMarkov protocol h n
  unfold trajectoryExperiment_adaptiveJointKernel
  infer_instance

/-- One adaptive transition: sample the next outcome and append it to the
observed history. -/
def adaptiveAppendKernel
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : Kernel (AdaptiveTrajectory Outcome) (AdaptiveTrajectory Outcome) :=
  (trajectoryExperiment_adaptiveJointKernel protocol h n).map
    (fun pair => pair.1.snoc pair.2)

theorem adaptiveAppendKernel_isMarkov
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : IsMarkovKernel (adaptiveAppendKernel protocol h n) := by
  letI : IsMarkovKernel (trajectoryExperiment_adaptiveJointKernel protocol h n) :=
    adaptiveJointKernel_isMarkov protocol h n
  exact Kernel.IsMarkovKernel.map _ measurable_adaptiveTrajectory_snoc

/-- Pointwise source-shaped description of the append transition. -/
theorem adaptiveAppendKernel_apply
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) (history : AdaptiveTrajectory Outcome) :
    adaptiveAppendKernel protocol h n history =
      ((Measure.dirac history).prod
        (protocol.response h (protocol.design n history))).map
          (fun pair => pair.1.snoc pair.2) := by
  letI : IsMarkovKernel (adaptiveStepKernel protocol h n) :=
    adaptiveStepKernel_isMarkov protocol h n
  rw [adaptiveAppendKernel, Kernel.map_apply _ measurable_adaptiveTrajectory_snoc,
    trajectoryExperiment_adaptiveJointKernel, Kernel.prod_apply]
  simp only [Kernel.id_apply, adaptiveStepKernel_apply]

/-- The finite trajectory law obtained by starting from the empty history and
successively composing the predictable append kernels. -/
noncomputable def trajectoryExperiment_adaptiveTrajectoryMeasure
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) : ℕ → Measure (AdaptiveTrajectory Outcome)
  | 0 => Measure.dirac AdaptiveTrajectory.empty
  | n + 1 => adaptiveAppendKernel protocol h n ∘ₘ trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n

@[simp]
theorem adaptiveTrajectoryMeasure_zero
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (h : H) :
    trajectoryExperiment_adaptiveTrajectoryMeasure protocol h 0 = Measure.dirac AdaptiveTrajectory.empty :=
  rfl

@[simp]
theorem adaptiveTrajectoryMeasure_succ
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (h : H) (n : ℕ) :
    trajectoryExperiment_adaptiveTrajectoryMeasure protocol h (n + 1) =
      adaptiveAppendKernel protocol h n ∘ₘ trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n :=
  rfl

/-- The recursively constructed finite trajectory law has total mass one. -/
theorem trajectoryExperiment_adaptiveTrajectoryMeasure_isProbability
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) : IsProbabilityMeasure (trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n) := by
  induction n with
  | zero =>
      change IsProbabilityMeasure (Measure.dirac AdaptiveTrajectory.empty)
      infer_instance
  | succ n ih =>
      letI : IsProbabilityMeasure (trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n) := ih
      letI : IsMarkovKernel (adaptiveAppendKernel protocol h n) :=
        adaptiveAppendKernel_isMarkov protocol h n
      change IsProbabilityMeasure
        (adaptiveAppendKernel protocol h n ∘ₘ trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n)
      infer_instance

/-- Exact one-step integration formula for the adaptive trajectory law. -/
theorem adaptiveTrajectoryMeasure_succ_apply
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    (h : H) (n : ℕ) (s : Set (AdaptiveTrajectory Outcome)) :
    trajectoryExperiment_adaptiveTrajectoryMeasure protocol h (n + 1) s =
      ∫⁻ history, adaptiveAppendKernel protocol h n history s
        ∂trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n := by
  rw [adaptiveTrajectoryMeasure_succ,
    Measure.bind_apply (by trivial) (Kernel.aemeasurable _)]

/-- Pointwise domination of every physical response distribution. -/
def ResponseDominatedAt
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (h h0 : H) : Prop :=
  ∀ action, protocol.response h action ≪ protocol.response h0 action

/-- Response domination is preserved after inserting a predictable design. -/
theorem adaptiveStepKernel_absolutelyContinuous
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    {h h0 : H} (hdom : ResponseDominatedAt protocol h h0)
    (n : ℕ) (history : AdaptiveTrajectory Outcome) :
    adaptiveStepKernel protocol h n history ≪
      adaptiveStepKernel protocol h0 n history := by
  simpa [adaptiveStepKernel] using hdom (protocol.design n history)

/-- Domination is preserved by adjoining the unchanged past. -/
theorem adaptiveJointKernel_absolutelyContinuous
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    {h h0 : H} (hdom : ResponseDominatedAt protocol h h0)
    (n : ℕ) (history : AdaptiveTrajectory Outcome) :
    trajectoryExperiment_adaptiveJointKernel protocol h n history ≪
      trajectoryExperiment_adaptiveJointKernel protocol h0 n history := by
  letI : IsMarkovKernel (adaptiveStepKernel protocol h n) :=
    adaptiveStepKernel_isMarkov protocol h n
  letI : IsMarkovKernel (adaptiveStepKernel protocol h0 n) :=
    adaptiveStepKernel_isMarkov protocol h0 n
  rw [trajectoryExperiment_adaptiveJointKernel, Kernel.prod_apply, trajectoryExperiment_adaptiveJointKernel, Kernel.prod_apply]
  exact Measure.AbsolutelyContinuous.rfl.prod
    (adaptiveStepKernel_absolutelyContinuous protocol hdom n history)

/-- Domination is preserved by the measurable append map. -/
theorem adaptiveAppendKernel_absolutelyContinuous
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    {h h0 : H} (hdom : ResponseDominatedAt protocol h h0)
    (n : ℕ) (history : AdaptiveTrajectory Outcome) :
    adaptiveAppendKernel protocol h n history ≪
      adaptiveAppendKernel protocol h0 n history := by
  rw [adaptiveAppendKernel, Kernel.map_apply _ measurable_adaptiveTrajectory_snoc,
    adaptiveAppendKernel, Kernel.map_apply _ measurable_adaptiveTrajectory_snoc]
  exact (adaptiveJointKernel_absolutelyContinuous protocol hdom n history).map
    measurable_adaptiveTrajectory_snoc

/-- If each selected one-step response at `h` is dominated by its response at
`h0`, then the complete finite adaptive trajectory law is dominated as well. -/
theorem adaptiveTrajectoryMeasure_absolutelyContinuous
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    {h h0 : H} (hdom : ResponseDominatedAt protocol h h0) (n : ℕ) :
    trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n ≪ trajectoryExperiment_adaptiveTrajectoryMeasure protocol h0 n := by
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ n ih =>
      rw [adaptiveTrajectoryMeasure_succ, adaptiveTrajectoryMeasure_succ]
      exact ih.comp <| Filter.Eventually.of_forall fun history =>
        adaptiveAppendKernel_absolutelyContinuous protocol hdom n history






/-! Supporting definitions and proved lemmas used by the manuscript. -/





/-! ## A common Ionescu-Tulcea path space -/

/-- Constant state family used by Mathlib's Ionescu-Tulcea construction. -/
abbrev AdaptiveOutcomeProcess (Outcome : Type v) : ℕ → Type v :=
  fun _ => Outcome

/-- Infinite outcome paths generated by the adaptive protocol. -/
abbrev AdaptiveInfinitePath (Outcome : Type v) :=
  (n : ℕ) → AdaptiveOutcomeProcess Outcome n

/-- Convert coordinates `0, ..., n` into the chronological observed history. -/
def iicToAdaptiveTrajectory
    {Outcome : Type v} {n : ℕ}
    (path : (i : Finset.Iic n) → AdaptiveOutcomeProcess Outcome i) :
    AdaptiveTrajectory Outcome :=
  ⟨List.ofFn fun i : Fin (n + 1) =>
    path ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩⟩

theorem measurable_iicToAdaptiveTrajectory
    {Outcome : Type v} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome] (n : ℕ) :
    Measurable
      (iicToAdaptiveTrajectory (Outcome := Outcome) (n := n)) :=
  measurable_of_countable _

/-- Distribution of the first outcome, selected from the empty history. -/
def adaptiveInitialOutcomeMeasure
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    Measure Outcome :=
  protocol.response theta (protocol.design 0 AdaptiveTrajectory.empty)

instance adaptiveInitialOutcomeMeasure_isProbability
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    IsProbabilityMeasure (adaptiveInitialOutcomeMeasure protocol theta) := by
  exact (protocol.response_isMarkov theta).isProbabilityMeasure _

/-- Ionescu-Tulcea transition from outcomes `0, ..., n` to outcome `n + 1`.
The measurement setting is the predictable design evaluated on that prefix. -/
def adaptiveIonescuStepKernel
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → AdaptiveOutcomeProcess Outcome i)
      (AdaptiveOutcomeProcess Outcome (n + 1)) :=
  (adaptiveStepKernel protocol theta (n + 1)).comap
    (iicToAdaptiveTrajectory (Outcome := Outcome) (n := n))
    (measurable_iicToAdaptiveTrajectory n)

theorem adaptiveIonescuStepKernel_isMarkov
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (n : ℕ) :
    IsMarkovKernel (adaptiveIonescuStepKernel protocol theta n) := by
  letI : IsMarkovKernel (adaptiveStepKernel protocol theta (n + 1)) :=
    adaptiveStepKernel_isMarkov protocol theta (n + 1)
  unfold adaptiveIonescuStepKernel
  infer_instance

/-- The common infinite-path law supplied by Mathlib's Ionescu-Tulcea theorem. -/
noncomputable def adaptiveInfiniteTrajectoryMeasure
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    Measure (AdaptiveInfinitePath Outcome) :=
  letI : ∀ n, IsMarkovKernel (adaptiveIonescuStepKernel protocol theta n) :=
    fun n => adaptiveIonescuStepKernel_isMarkov protocol theta n
  Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
    (adaptiveInitialOutcomeMeasure protocol theta)
    (adaptiveIonescuStepKernel protocol theta)

instance adaptiveInfiniteTrajectoryMeasure_isProbability
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    IsProbabilityMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta) := by
  letI : IsProbabilityMeasure (adaptiveInitialOutcomeMeasure protocol theta) :=
    adaptiveInitialOutcomeMeasure_isProbability protocol theta
  letI : ∀ n, IsMarkovKernel (adaptiveIonescuStepKernel protocol theta n) :=
    fun n => adaptiveIonescuStepKernel_isMarkov protocol theta n
  change IsProbabilityMeasure
    (Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
      (adaptiveInitialOutcomeMeasure protocol theta)
      (adaptiveIonescuStepKernel protocol theta))
  infer_instance


/-- Under the infinite law, the conditional distribution of outcome `n + 1`
given coordinates `0, ..., n` is the protocol's predictable transition. -/
theorem adaptiveInfiniteTrajectory_conditionalStep
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    [StandardBorelSpace Outcome] [Nonempty Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (n : ℕ) :
    condDistrib (fun path : AdaptiveInfinitePath Outcome => path (n + 1))
        (frestrictLe n) (adaptiveInfiniteTrajectoryMeasure protocol theta)
      =ᵐ[(adaptiveInfiniteTrajectoryMeasure protocol theta).map (frestrictLe n)]
        adaptiveIonescuStepKernel protocol theta n := by
  letI : IsProbabilityMeasure (adaptiveInitialOutcomeMeasure protocol theta) :=
    adaptiveInitialOutcomeMeasure_isProbability protocol theta
  letI : ∀ k, IsMarkovKernel (adaptiveIonescuStepKernel protocol theta k) :=
    fun k => adaptiveIonescuStepKernel_isMarkov protocol theta k
  change
    condDistrib (fun path : AdaptiveInfinitePath Outcome => path (n + 1))
        (frestrictLe n)
        (Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
          (adaptiveInitialOutcomeMeasure protocol theta)
          (adaptiveIonescuStepKernel protocol theta))
      =ᵐ[(Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
        (adaptiveInitialOutcomeMeasure protocol theta)
        (adaptiveIonescuStepKernel protocol theta)).map (frestrictLe n)]
        adaptiveIonescuStepKernel protocol theta n
  exact Kernel.condDistrib_trajMeasure

/-- The first `n` outcomes of an infinite path as a finite observed history. -/
def adaptiveInfinitePathPrefix
    {Outcome : Type v} : ℕ → AdaptiveInfinitePath Outcome → AdaptiveTrajectory Outcome
  | 0, _ => AdaptiveTrajectory.empty
  | n + 1, path =>
      iicToAdaptiveTrajectory (Outcome := Outcome) (n := n) (frestrictLe n path)

theorem measurable_adaptiveInfinitePathPrefix
    {Outcome : Type v} [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome] (n : ℕ) :
    Measurable (adaptiveInfinitePathPrefix (Outcome := Outcome) n) := by
  cases n with
  | zero =>
      change Measurable
        (fun _ : AdaptiveInfinitePath Outcome =>
          (AdaptiveTrajectory.empty : AdaptiveTrajectory Outcome))
      exact measurable_const
  | succ n =>
      exact (measurable_iicToAdaptiveTrajectory (Outcome := Outcome) n).comp
        (measurable_frestrictLe n)

/-- Lift any finite-prefix score to the common infinite sample space. -/
def adaptiveInfinitePathScore
    {Outcome : Type v} {Score : Type*}
    (finiteScore : ℕ → AdaptiveTrajectory Outcome → Score) (n : ℕ) :
    AdaptiveInfinitePath Outcome → Score :=
  finiteScore n ∘ adaptiveInfinitePathPrefix n

theorem measurable_adaptiveInfinitePathScore
    {Outcome : Type v} {Score : Type*}
    [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome] [Countable Outcome]
    [MeasurableSpace Score]
    (finiteScore : ℕ → AdaptiveTrajectory Outcome → Score)
    (hscore : ∀ n, Measurable (finiteScore n)) (n : ℕ) :
    Measurable (adaptiveInfinitePathScore finiteScore n) :=
  (hscore n).comp (measurable_adaptiveInfinitePathPrefix n)






/-! ## Hybrid full-path experiments on one fixed sample space -/




















/-- The terminal martingale score on the common infinite path. -/
def hybridInfiniteTerminalScore
    {D : Type*} [Fintype D] {Outcome : Type v}
    (increment : ℕ → ℕ → AdaptiveInfinitePath Outcome → MartingaleScoreSpace D)
    (n : ℕ) (path : AdaptiveInfinitePath Outcome) : MartingaleScoreSpace D :=
  ∑ k ∈ Finset.range n, increment n k path



end

end QubitOracle.Paper
