import QubitOracle.Paper.SourceFaithfulMinimax
import QubitOracle.Paper.AdaptiveLANExperimentBridge
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

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

/-- The finite-horizon adaptive protocol as an actual statistical experiment. -/
def adaptiveTrajectoryExperiment
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (n : ℕ) :
    StatisticalExperiment H where
  Sample := AdaptiveTrajectory Outcome
  measurableSpace := inferInstance
  measure h := trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n
  probabilityMeasure h := trajectoryExperiment_adaptiveTrajectoryMeasure_isProbability protocol h n

/-- The sequence of finite-horizon experiments generated by one protocol. -/
def adaptiveTrajectoryExperimentSequence
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) :
    ℕ → StatisticalExperiment H :=
  fun n => adaptiveTrajectoryExperiment protocol n

@[simp]
theorem adaptiveTrajectoryExperiment_measure
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (n : ℕ) (h : H) :
    (adaptiveTrajectoryExperiment protocol n).measure h =
      trajectoryExperiment_adaptiveTrajectoryMeasure protocol h n :=
  rfl

/-- Concrete local domination for the experiment sequence.  This is exactly
the first component required by `IsLANSequence` when `h0` is its base point. -/
theorem adaptiveTrajectoryExperimentSequence_localDomination
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome) (h0 : H)
    (hdom : ∀ h, ResponseDominatedAt protocol h h0) :
    ∀ n h,
      (adaptiveTrajectoryExperimentSequence protocol n).measure h ≪
        (adaptiveTrajectoryExperimentSequence protocol n).measure h0 := by
  intro n h
  exact adaptiveTrajectoryMeasure_absolutelyContinuous protocol (hdom h) n

/-- Specialization of local domination to the zero base point used by the LAN
experiment interface. -/
theorem adaptiveTrajectoryLAN_localDomination
    {D : Type*} [Fintype D]
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol (LANParameter D) Action Outcome)
    (hdom : ∀ h, ResponseDominatedAt protocol h 0) :
    ∀ n h,
      (adaptiveTrajectoryExperimentSequence protocol n).measure h ≪
        (adaptiveTrajectoryExperimentSequence protocol n).measure 0 :=
  adaptiveTrajectoryExperimentSequence_localDomination protocol 0 hdom

/-! ## Localized finite-horizon experiments -/

/-- Reparameterize the physical model by a horizon-dependent LAN localization
`h ↦ localize n h`.  Thus the measure at local parameter `h` is exactly the
`n`-step adaptive trajectory law at physical parameter `localize n h`. -/
def localizedAdaptiveTrajectoryExperiment
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (n : ℕ) :
    StatisticalExperiment (LANParameter D) where
  Sample := AdaptiveTrajectory Outcome
  measurableSpace := inferInstance
  measure h := trajectoryExperiment_adaptiveTrajectoryMeasure protocol (localize n h) n
  probabilityMeasure h :=
    trajectoryExperiment_adaptiveTrajectoryMeasure_isProbability protocol (localize n h) n

/-- The localized triangular sequence of adaptive experiments. -/
def localizedAdaptiveTrajectoryExperimentSequence
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) :
    ℕ → StatisticalExperiment (LANParameter D) :=
  fun n => localizedAdaptiveTrajectoryExperiment protocol localize n

@[simp]
theorem localizedAdaptiveTrajectoryExperiment_measure
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (n : ℕ) (h : LANParameter D) :
    (localizedAdaptiveTrajectoryExperiment protocol localize n).measure h =
      trajectoryExperiment_adaptiveTrajectoryMeasure protocol (localize n h) n :=
  rfl

/-- Local domination of the localized experiment reduces exactly to
pointwise domination of every selected physical response kernel. -/
theorem localizedAdaptiveTrajectoryExperiment_localDomination
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta)
    (hresponse : ∀ n h,
      ResponseDominatedAt protocol (localize n h) (localize n 0)) :
    ∀ n h,
      (localizedAdaptiveTrajectoryExperimentSequence protocol localize n).measure h ≪
        (localizedAdaptiveTrajectoryExperimentSequence protocol localize n).measure 0 := by
  intro n h
  exact adaptiveTrajectoryMeasure_absolutelyContinuous protocol (hresponse n h) n

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

/-- The infinite-path law as an actual statistical experiment. -/
def adaptiveInfiniteTrajectoryExperiment
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) :
    StatisticalExperiment Theta where
  Sample := AdaptiveInfinitePath Outcome
  measurableSpace := inferInstance
  measure theta := adaptiveInfiniteTrajectoryMeasure protocol theta
  probabilityMeasure theta :=
    adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta

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

/-- The finite-prefix marginal of the common infinite-path experiment. -/
def adaptiveInfinitePrefixExperiment
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (n : ℕ) :
    StatisticalExperiment Theta where
  Sample := AdaptiveTrajectory Outcome
  measurableSpace := inferInstance
  measure theta := (adaptiveInfiniteTrajectoryMeasure protocol theta).map
    (adaptiveInfinitePathPrefix n)
  probabilityMeasure theta := by
    letI : IsProbabilityMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta) :=
      adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta
    exact Measure.isProbabilityMeasure_map
      (measurable_adaptiveInfinitePathPrefix n).aemeasurable

/-- Localized finite-prefix marginals of the Ionescu-Tulcea experiment. -/
def localizedAdaptiveInfinitePrefixExperiment
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (n : ℕ) :
    StatisticalExperiment (LANParameter D) where
  Sample := AdaptiveTrajectory Outcome
  measurableSpace := inferInstance
  measure h := (adaptiveInfiniteTrajectoryMeasure protocol (localize n h)).map
    (adaptiveInfinitePathPrefix n)
  probabilityMeasure h := by
    letI : IsProbabilityMeasure
        (adaptiveInfiniteTrajectoryMeasure protocol (localize n h)) :=
      adaptiveInfiniteTrajectoryMeasure_isProbability protocol (localize n h)
    exact Measure.isProbabilityMeasure_map
      (measurable_adaptiveInfinitePathPrefix n).aemeasurable

/-- Concrete condition under which the triangular localization has one fixed
physical base parameter and hence one common base path law. -/
def HasFixedLocalizedBase
    {D : Type*} [Fintype D] {Theta : Type u}
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) : Prop :=
  ∀ n, localize n 0 = theta0

/-- If the localized base parameter is constant, every base prefix law is the
corresponding marginal of one fixed Ionescu-Tulcea measure. -/
theorem localizedAdaptiveInfinitePrefix_baseMeasure_eq_fixedBase
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0) (n : ℕ) :
    (localizedAdaptiveInfinitePrefixExperiment protocol localize n).measure 0 =
      (adaptiveInfiniteTrajectoryMeasure protocol theta0).map
        (adaptiveInfinitePathPrefix n) := by
  simp only [localizedAdaptiveInfinitePrefixExperiment]
  rw [hbase n]

/-- Consequently, every measurable first-`n` score has the same law as its
lift to the one fixed base path measure.  This is the interface needed by a
fixed-base martingale CLT such as the Hall-Heyde wrapper. -/
theorem localizedAdaptiveInfinitePrefix_scoreLaw_eq_fixedBase
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v} {Score : Type*}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    [MeasurableSpace Score]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0)
    (finiteScore : ℕ → AdaptiveTrajectory Outcome → Score)
    (hscore : ∀ n, Measurable (finiteScore n)) (n : ℕ) :
    ((localizedAdaptiveInfinitePrefixExperiment protocol localize n).measure 0).map
        (finiteScore n) =
      (adaptiveInfiniteTrajectoryMeasure protocol theta0).map
        (adaptiveInfinitePathScore finiteScore n) := by
  rw [localizedAdaptiveInfinitePrefix_baseMeasure_eq_fixedBase
    protocol localize theta0 hbase n]
  exact Measure.map_map (hscore n) (measurable_adaptiveInfinitePathPrefix n)

/-! ## Hybrid full-path experiments on one fixed sample space -/

/-- Physical parameter used at stage `t` of the horizon-`n` hybrid law.
Stages `t < n` use the localized alternative and every later stage uses the
fixed physical base parameter. -/
def hybridStageParameter
    {D : Type*} [Fintype D] {Theta : Type u}
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) (t : ℕ) : Theta :=
  if t < n then localize n h else theta0

theorem hybridStageParameter_eq_base_of_tail
    {D : Type*} [Fintype D] {Theta : Type u}
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) {t : ℕ} (ht : n ≤ t) :
    hybridStageParameter localize theta0 n h t = theta0 := by
  simp [hybridStageParameter, Nat.not_lt.mpr ht]

theorem hybridStageParameter_zero_eq_base
    {D : Type*} [Fintype D] {Theta : Type u}
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0) (n t : ℕ) :
    hybridStageParameter localize theta0 n 0 t = theta0 := by
  simp [hybridStageParameter, hbase n]

/-- Initial outcome law for the hybrid path.  It uses the localized parameter
exactly when the requested horizon is positive. -/
def hybridInitialOutcomeMeasure
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) : Measure Outcome :=
  adaptiveInitialOutcomeMeasure protocol
    (hybridStageParameter localize theta0 n h 0)

instance hybridInitialOutcomeMeasure_isProbability
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) :
    IsProbabilityMeasure
      (hybridInitialOutcomeMeasure protocol localize theta0 n h) :=
  adaptiveInitialOutcomeMeasure_isProbability _ _

/-- The Ionescu-Tulcea kernel producing outcome `k + 1` in the hybrid path. -/
def hybridIonescuStepKernel
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) (k : ℕ) :=
  adaptiveIonescuStepKernel protocol
    (hybridStageParameter localize theta0 n h (k + 1)) k

instance hybridIonescuStepKernel_isMarkov
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) (k : ℕ) :
    IsMarkovKernel
      (hybridIonescuStepKernel protocol localize theta0 n h k) :=
  adaptiveIonescuStepKernel_isMarkov _ _ _

/-- Every kernel producing a stage at or after the terminal horizon is exactly
the fixed-base transition kernel. -/
theorem hybridIonescuStepKernel_eq_base_of_tail
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) (k : ℕ) (hk : n ≤ k + 1) :
    hybridIonescuStepKernel protocol localize theta0 n h k =
      adaptiveIonescuStepKernel protocol theta0 k := by
  simp [hybridIonescuStepKernel, hybridStageParameter, Nat.not_lt.mpr hk]

theorem hybridIonescuStepKernel_zero_eq_base
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0) (n k : ℕ) :
    hybridIonescuStepKernel protocol localize theta0 n 0 k =
      adaptiveIonescuStepKernel protocol theta0 k := by
  simp [hybridIonescuStepKernel, hybridStageParameter, hbase n]

/-- The hybrid infinite law: its first `n` outcome stages use `localize n h`
and its complete tail uses `theta0`. -/
noncomputable def hybridInfiniteTrajectoryMeasure
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) : Measure (AdaptiveInfinitePath Outcome) :=
  letI : ∀ k, IsMarkovKernel
      (hybridIonescuStepKernel protocol localize theta0 n h k) :=
    fun k => hybridIonescuStepKernel_isMarkov protocol localize theta0 n h k
  Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
    (hybridInitialOutcomeMeasure protocol localize theta0 n h)
    (hybridIonescuStepKernel protocol localize theta0 n h)

instance hybridInfiniteTrajectoryMeasure_isProbability
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (n : ℕ) (h : LANParameter D) :
    IsProbabilityMeasure
      (hybridInfiniteTrajectoryMeasure protocol localize theta0 n h) := by
  letI : ∀ k, IsMarkovKernel
      (hybridIonescuStepKernel protocol localize theta0 n h k) :=
    fun k => hybridIonescuStepKernel_isMarkov protocol localize theta0 n h k
  change IsProbabilityMeasure
    (Kernel.trajMeasure (X := AdaptiveOutcomeProcess Outcome)
      (hybridInitialOutcomeMeasure protocol localize theta0 n h)
      (hybridIonescuStepKernel protocol localize theta0 n h))
  infer_instance

/-- Under a fixed localized base, the complete hybrid null law, not merely its
finite-prefix marginal, is exactly one common infinite-path measure. -/
theorem hybridInfiniteTrajectoryMeasure_zero_eq_base
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0) (n : ℕ) :
    hybridInfiniteTrajectoryMeasure protocol localize theta0 n 0 =
      adaptiveInfiniteTrajectoryMeasure protocol theta0 := by
  simp only [hybridInfiniteTrajectoryMeasure, adaptiveInfiniteTrajectoryMeasure]
  congr 1
  · simp [hybridInitialOutcomeMeasure, hybridStageParameter, hbase n]
  · funext k
    exact hybridIonescuStepKernel_zero_eq_base
      protocol localize theta0 hbase n k

/-- Horizon-indexed hybrid measures on the one fixed infinite sample type. -/
def localizedHybridInfinitePathMeasureFamily
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) :
    ℕ → LANParameter D → Measure (AdaptiveInfinitePath Outcome) :=
  fun n h => hybridInfiniteTrajectoryMeasure protocol localize theta0 n h

theorem localizedHybridInfinitePathMeasureFamily_isProbability
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) :
    ∀ n h, IsProbabilityMeasure
      (localizedHybridInfinitePathMeasureFamily protocol localize theta0 n h) :=
  fun n h => hybridInfiniteTrajectoryMeasure_isProbability
    protocol localize theta0 n h

/-- The hybrid sequence is definitionally a `fixedSampleExperiment`, with the
full infinite path as its sample space for every horizon. -/
abbrev localizedHybridInfinitePathExperimentSequence
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) :
    ℕ → StatisticalExperiment (LANParameter D) :=
  fixedSampleExperiment
    (localizedHybridInfinitePathMeasureFamily protocol localize theta0)
    (localizedHybridInfinitePathMeasureFamily_isProbability protocol localize theta0)

/-- Constructor for one member of the hybrid full-path experiment sequence. -/
def localizedHybridInfinitePathExperiment
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) (n : ℕ) :
    StatisticalExperiment (LANParameter D) :=
  localizedHybridInfinitePathExperimentSequence protocol localize theta0 n

/-- Exact `hbase` endpoint required by
`adaptiveLANSequence_of_martingale_conditions`. -/
theorem localizedHybridInfinitePathMeasureFamily_base
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0) :
    ∀ n,
      localizedHybridInfinitePathMeasureFamily protocol localize theta0 n 0 =
        adaptiveInfiniteTrajectoryMeasure protocol theta0 :=
  hybridInfiniteTrajectoryMeasure_zero_eq_base protocol localize theta0 hbase

/-- Concrete response-level premise for the desired full-path domination
transfer. -/
def HybridResponseDominatedByBase
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) : Prop :=
  ∀ n h, ResponseDominatedAt protocol (localize n h) theta0

/-- Exact remaining full-path domination statement.  Its proof requires a
finite-prefix/common-tail factorization theorem for `Kernel.traj`; it is kept
as an explicit premise rather than introduced as an axiom. -/
def HybridFullPathDominatedByBase
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta) : Prop :=
  ∀ n h,
    localizedHybridInfinitePathMeasureFamily protocol localize theta0 n h ≪
      adaptiveInfiniteTrajectoryMeasure protocol theta0

/-- The terminal martingale score on the common infinite path. -/
def hybridInfiniteTerminalScore
    {D : Type*} [Fintype D] {Outcome : Type v}
    (increment : ℕ → ℕ → AdaptiveInfinitePath Outcome → MartingaleScoreSpace D)
    (n : ℕ) (path : AdaptiveInfinitePath Outcome) : MartingaleScoreSpace D :=
  ∑ k ∈ Finset.range n, increment n k path

theorem hybridInfiniteTerminalScore_eq_fixedSample_terminalSum
    {D : Type*} [Fintype D] {Outcome : Type} [MeasurableSpace Outcome]
    (mu : Measure (AdaptiveInfinitePath Outcome)) (hmu : IsProbabilityMeasure mu)
    (filtration : ℕ → Filtration ℕ
      (inferInstance : MeasurableSpace (AdaptiveInfinitePath Outcome)))
    (increment : ℕ → ℕ → AdaptiveInfinitePath Outcome → MartingaleScoreSpace D) :
    hybridInfiniteTerminalScore increment =
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum :=
  rfl

/-- Final fixed-sample endpoint.  Once the concrete full-path domination
statement is supplied, the existing Hall-Heyde/Cramer-Wold LAN theorem applies
without changing sample spaces or base measures across `n`. -/
theorem adaptiveLANSequence_of_hybrid_martingale_conditions
    {D : Type*} [Fintype D] [DecidableEq D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hbase : HasFixedLocalizedBase localize theta0)
    (hPathDomination : HybridFullPathDominatedByBase protocol localize theta0)
    (filtration : ℕ → Filtration ℕ
      (inferInstance : MeasurableSpace (AdaptiveInfinitePath Outcome)))
    (increment : ℕ → ℕ → AdaptiveInfinitePath Outcome → MartingaleScoreSpace D)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem
        (D := D)
        (adaptiveInfiniteTrajectoryMeasure protocol theta0)
        (adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta0)
        filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem
        (D := D)
        (adaptiveInfiniteTrajectoryMeasure protocol theta0)
        (adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta0)
        filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem
        (D := D)
        (adaptiveInfiniteTrajectoryMeasure protocol theta0)
        (adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta0)
        filtration increment) M)
    (hTerminalMeasurable : ∀ n,
      AEMeasurable (hybridInfiniteTerminalScore increment n)
        (adaptiveInfiniteTrajectoryMeasure protocol theta0))
    (hRemainder : LANRemainderConvergesInProbability
      (localizedHybridInfinitePathExperimentSequence protocol localize theta0) M
      (hybridInfiniteTerminalScore increment)) :
    IsLANSequence
      (localizedHybridInfinitePathExperimentSequence protocol localize theta0) M
      (hybridInfiniteTerminalScore increment) := by
  let P := localizedHybridInfinitePathMeasureFamily protocol localize theta0
  let hP := localizedHybridInfinitePathMeasureFamily_isProbability
    protocol localize theta0
  let mu := adaptiveInfiniteTrajectoryMeasure protocol theta0
  let hmu : IsProbabilityMeasure mu :=
    adaptiveInfiniteTrajectoryMeasure_isProbability protocol theta0
  have hfixed : ∀ n, P n 0 = mu :=
    localizedHybridInfinitePathMeasureFamily_base protocol localize theta0 hbase
  have hdom : ∀ n h, P n h ≪ P n 0 := by
    intro n h
    rw [hfixed n]
    exact hPathDomination n h
  have hscore :
      hybridInfiniteTerminalScore increment =
        (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum :=
    hybridInfiniteTerminalScore_eq_fixedSample_terminalSum
      (D := D) mu hmu filtration increment
  have hTerminalMeasurable' : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum n)
        mu := by
    rw [← hscore]
    exact hTerminalMeasurable
  have hRemainder' :
      LANRemainderConvergesInProbability
        (fixedSampleExperiment P hP) M
        (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum := by
    rw [← hscore]
    simpa [localizedHybridInfinitePathExperimentSequence, P, hP] using hRemainder
  have hLAN :=
    adaptiveLANSequence_of_martingale_conditions P hP mu hmu hfixed
      filtration increment M hM hMDS hLindeberg hCovariance
      hTerminalMeasurable' hdom hRemainder'
  rw [← hscore] at hLAN
  simpa [localizedHybridInfinitePathExperimentSequence, P, hP] using hLAN

end

end QubitOracle.Paper
