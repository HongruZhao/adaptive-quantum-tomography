import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-!
# A literal all-observation ridge controller with frozen batches

Sufficient statistics are updated after every observed outcome. A prescribed
refresh predicate decides when the measurement action is recomputed from the
new ridge estimate. Between refresh times the action is unchanged. The policy
is a fold of the actual finite history, so it cannot depend on future data.

The controller map may include nearest-pure projection and unitary completion;
it need not be globally continuous or measurable on the ambient matrix space.
For finite outcomes its composition with finite histories is measurable.
-/

namespace QubitOracle.AdaptiveDesign.SequentialRidgeController

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares
open scoped BigOperators Topology InnerProductSpace

noncomputable section

variable {E Action Outcome Theta : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Stored sufficient statistics, the current frozen action, and the number
of observations already processed. -/
structure State (E Action : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (regularization : ℝ) where
  count : ℕ
  gram : E →ₗ[ℝ] E
  gram_coercive : Coercive gram regularization
  responseSum : E
  action : Action

def State.estimate {regularization : ℝ} (hregularization : 0 < regularization)
    (s : State E Action regularization) : E :=
  (LinearEquiv.ofInjectiveEndo s.gram
    (injective_of_coercive s.gram regularization hregularization s.gram_coercive)).symm
      s.responseSum

theorem State.estimate_normalEquation {regularization : ℝ}
    (hregularization : 0 < regularization) (s : State E Action regularization) :
    s.gram (s.estimate hregularization) = s.responseSum :=
  (LinearEquiv.ofInjectiveEndo s.gram
    (injective_of_coercive s.gram regularization hregularization s.gram_coercive)).apply_symm_apply _

def initialState (controller : E → Action) (regularization : ℝ) :
    State E Action regularization where
  count := 0
  gram := regularization • LinearMap.id
  gram_coercive := by
    intro x
    simp [inner_smul_right, real_inner_self_eq_norm_sq]
  responseSum := 0
  action := controller 0

/-- Update every sufficient statistic, then refresh the action exactly at
the prescribed cumulative shot boundaries. -/
def updateState
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (s : State E Action regularization) (y : Outcome) : State E Action regularization :=
  let next : State E Action regularization := {
    count := s.count + 1
    gram := s.gram + frame s.action
    gram_coercive := by
      intro x
      have hs := s.gram_coercive x
      have hf := hframe s.action x
      simp only [LinearMap.add_apply, inner_add_right]
      nlinarith [mul_nonneg hκ (sq_nonneg ‖x‖)]
    responseSum := s.responseSum + response s.action y
    action := s.action }
  { next with action := if refresh next.count then controller (next.estimate hregularization)
      else s.action }

def historyState
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (history : AdaptiveTrajectory Outcome) : State E Action regularization :=
  history.outcomes.foldl
    (updateState frame response controller refresh regularization κ hregularization hκ hframe)
    (initialState controller regularization)

theorem historyState_snoc
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (history : AdaptiveTrajectory Outcome) (y : Outcome) :
    historyState frame response controller refresh regularization κ hregularization hκ hframe
        (history.snoc y) =
      updateState frame response controller refresh regularization κ hregularization hκ hframe
        (historyState frame response controller refresh regularization κ hregularization hκ hframe
          history) y := by
  simp [historyState, AdaptiveTrajectory.snoc, List.foldl_append]

theorem adaptiveInfinitePathPrefix_outcomes
    (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
    (adaptiveInfinitePathPrefix n path).outcomes = List.ofFn (fun i : Fin n => path i) := by
  cases n <;> rfl

theorem adaptiveInfinitePathPrefix_snoc
    (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
    adaptiveInfinitePathPrefix (n+1) path = (adaptiveInfinitePathPrefix n path).snoc (path n) := by
  apply AdaptiveTrajectory.outcomes_injective
  rw [adaptiveInfinitePathPrefix_outcomes]
  change List.ofFn (fun i : Fin (n+1) => path i) =
    (adaptiveInfinitePathPrefix n path).outcomes ++ [path n]
  rw [adaptiveInfinitePathPrefix_outcomes, List.ofFn_succ']
  simp [List.concat_eq_append]

def pathState
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) : State E Action regularization :=
  historyState frame response controller refresh regularization κ hregularization hκ hframe
    (adaptiveInfinitePathPrefix n path)

theorem pathState_succ
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1) =
      updateState frame response controller refresh regularization κ hregularization hκ hframe
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path n)
        (path n) := by
  simp only [pathState, adaptiveInfinitePathPrefix_snoc, historyState_snoc]

theorem pathState_count
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).count = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pathState_succ]; simpa [updateState] using congrArg Nat.succ ih

variable [MeasurableSpace Action] [MeasurableSpace Outcome]
variable [Fintype Outcome] [MeasurableSingletonClass Outcome]

/-- A concrete history-fold policy combined with the genuine action-dependent
physical response kernel. -/
def protocol
    (kernel : Theta → Kernel Action Outcome) (hkernel : ∀ theta, IsMarkovKernel (kernel theta))
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ) :
    PredictableAdaptiveProtocol Theta Action Outcome where
  response := kernel
  response_isMarkov := hkernel
  design _ history :=
    (historyState frame response controller refresh regularization κ hregularization hκ hframe history).action
  design_measurable _ := measurable_of_countable _

theorem pathState_gram
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).gram =
      ridgeGram (fun t => frame
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action)
        regularization n := by
  induction n with
  | zero => simp [pathState, historyState, initialState, adaptiveInfinitePathPrefix, AdaptiveTrajectory.empty, ridgeGram]
  | succ n ih =>
    rw [pathState_succ]
    change (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).gram + _ = _
    rw [ih]
    simp only [ridgeGram, Finset.sum_range_succ]
    abel

theorem pathState_responseSum
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).responseSum =
      ∑ t ∈ Finset.range n, response
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action
        (path t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pathState_succ]
    change (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).responseSum + _ = _
    rw [ih, Finset.sum_range_succ]

/-- The estimate really computed by the history fold is exactly the
all-observation inverse-Gram estimator used in the statistical theorem. -/
theorem pathState_estimate_eq_ridgeEstimate
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).estimate hregularization =
      ridgeEstimate
        (fun t => frame (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action)
        (fun t => response (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action (path t))
        regularization κ hregularization hκ (fun t => hframe _) n := by
  let s := pathState frame response controller refresh regularization κ hregularization hκ hframe path n
  apply injective_of_coercive s.gram regularization hregularization s.gram_coercive
  change s.gram (s.estimate hregularization) = _
  rw [State.estimate_normalEquation]
  dsimp [s]
  rw [pathState_gram, ridgeEstimate_normalEquation, pathState_responseSum]

theorem pathState_action_succ
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1)).action =
      if refresh (n+1) then
        controller ((pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1)).estimate hregularization)
      else (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).action := by
  rw [pathState_succ]
  simp only [updateState, pathState_count, State.estimate]

/-- Latest completed update boundary, including the known initialization at zero. -/
def lastRefresh (refresh : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => if refresh (n+1) then n+1 else lastRefresh refresh n

theorem pathState_action_eq_lastRefresh
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).action =
      controller ((pathState frame response controller refresh regularization κ hregularization hκ hframe path
        (lastRefresh refresh n)).estimate hregularization) := by
  induction n with
  | zero => simp [pathState, historyState, initialState, adaptiveInfinitePathPrefix,
      AdaptiveTrajectory.empty, lastRefresh, State.estimate]
  | succ n ih =>
    rw [pathState_action_succ]
    simp only [lastRefresh]
    split_ifs with h
    · rfl
    · exact ih

variable [StandardBorelSpace Outcome] [Nonempty Outcome]

/-- The implemented recursive estimator is strongly consistent on the
physical history-dependent experiment, for every deterministic refresh rule. -/
theorem pathState_estimate_tendsto_ae
    (kernel : Theta → Kernel Action Outcome) (hkernel : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (truth : E) (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 < κ)
    (hframe : ∀ action, Coercive (frame action) κ)
    (hmean : ∀ action, ∫ y, response action y ∂kernel theta action = frame action truth)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖response action outcome - frame action truth‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (protocol kernel hkernel frame response controller refresh regularization κ hregularization hκ.le hframe) theta,
      Tendsto
        (fun n => (pathState frame response controller refresh regularization κ hregularization hκ.le hframe path n).estimate hregularization)
        atTop (𝓝 truth) := by
  have hraw := AdaptiveRidgeConsistency.actualRidgeEstimate_tendsto_ae
    (protocol kernel hkernel frame response controller refresh regularization κ hregularization hκ.le hframe)
    theta frame response truth regularization κ hregularization hκ hframe hmean C hC hbound
  filter_upwards [hraw] with path hpath
  have heq :
      (fun n => (pathState frame response controller refresh regularization κ hregularization hκ.le hframe path n).estimate hregularization) =
        AdaptiveRidgeConsistency.actualRidgeEstimate
          (protocol kernel hkernel frame response controller refresh regularization κ hregularization hκ.le hframe)
          frame response regularization κ hregularization hκ.le hframe path := by
    funext n
    exact pathState_estimate_eq_ridgeEstimate frame response controller refresh regularization κ hregularization hκ.le hframe path n
  rw [heq]
  exact hpath

end

end QubitOracle.AdaptiveDesign.SequentialRidgeController
