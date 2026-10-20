import QubitOracle.AdaptiveDesign.AdaptiveExplorationRate
import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.SequentialRidgeController
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

namespace QubitOracle.AdaptiveDesign.ScheduledRidgeController

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares SequentialRidgeController
open scoped BigOperators Topology InnerProductSpace

noncomputable section

variable {E Action Outcome Theta : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (s : State E Action regularization) (y : Outcome) : State E Action regularization :=
  let next : State E Action regularization := {
    count := s.count + 1
    gram := s.gram + frame s.count s.action
    gram_coercive := by
      intro x
      have hs := s.gram_coercive x
      have hf := hframe s.count s.action x
      simp only [LinearMap.add_apply, inner_add_right]
      nlinarith [mul_nonneg hκ (sq_nonneg ‖x‖)]
    responseSum := s.responseSum + response s.count s.action y
    action := s.action }
  { next with action := if refresh next.count then controller (next.estimate hregularization)
      else s.action }

def historyState
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (history : AdaptiveTrajectory Outcome) : State E Action regularization :=
  history.outcomes.foldl
    (updateState frame response controller refresh regularization κ hregularization hκ hframe)
    (initialState controller regularization)

theorem historyState_snoc
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
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
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) : State E Action regularization :=
  historyState frame response controller refresh regularization κ hregularization hκ hframe
    (adaptiveInfinitePathPrefix n path)

theorem pathState_succ
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1) =
      updateState frame response controller refresh regularization κ hregularization hκ hframe
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path n)
        (path n) := by
  simp only [pathState, adaptiveInfinitePathPrefix_snoc, historyState_snoc]

theorem pathState_count
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
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
    (kernel : Theta → Kernel (ℕ × Action) Outcome) (hkernel : ∀ theta, IsMarkovKernel (kernel theta))
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ) :
    PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome where
  response := kernel
  response_isMarkov := hkernel
  design n history :=
    (n, (historyState frame response controller refresh regularization κ hregularization hκ hframe history).action)
  design_measurable _ := measurable_of_countable _

theorem pathState_gram
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).gram =
      ridgeGram (fun t => frame t
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action)
        regularization n := by
  induction n with
  | zero => simp [pathState, historyState, initialState, adaptiveInfinitePathPrefix, AdaptiveTrajectory.empty, ridgeGram]
  | succ n ih =>
    rw [pathState_succ]
    change (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).gram + _ = _
    rw [pathState_count, ih]
    simp only [ridgeGram, Finset.sum_range_succ]
    abel

theorem pathState_responseSum
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).responseSum =
      ∑ t ∈ Finset.range n, response t
        (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action
        (path t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pathState_succ]
    change (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).responseSum + _ = _
    rw [pathState_count, ih, Finset.sum_range_succ]

/-- The estimate really computed by the history fold is exactly the
all-observation inverse-Gram estimator used in the statistical theorem. -/
theorem pathState_estimate_eq_ridgeEstimate
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).estimate hregularization =
      ridgeEstimate
        (fun t => frame t (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action)
        (fun t => response t (pathState frame response controller refresh regularization κ hregularization hκ hframe path t).action (path t))
        regularization κ hregularization hκ (fun t => hframe t _) n := by
  let s := pathState frame response controller refresh regularization κ hregularization hκ hframe path n
  apply injective_of_coercive s.gram regularization hregularization s.gram_coercive
  change s.gram (s.estimate hregularization) = _
  rw [State.estimate_normalEquation]
  dsimp [s]
  rw [pathState_gram, ridgeEstimate_normalEquation, pathState_responseSum]

theorem pathState_action_succ
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) :
    (pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1)).action =
      if refresh (n+1) then
        controller ((pathState frame response controller refresh regularization κ hregularization hκ hframe path (n+1)).estimate hregularization)
      else (pathState frame response controller refresh regularization κ hregularization hκ hframe path n).action := by
  rw [pathState_succ]
  simp only [updateState, pathState_count, State.estimate]

theorem pathState_action_eq_lastRefresh
    (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
    (controller : E → Action) (refresh : ℕ → Bool)
    (regularization κ : ℝ) (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ n action, Coercive (frame n action) κ)
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


end
end QubitOracle.AdaptiveDesign.ScheduledRidgeController
