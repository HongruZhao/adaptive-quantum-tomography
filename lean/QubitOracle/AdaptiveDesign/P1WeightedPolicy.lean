import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1AdaptiveRidgePolicy
/-! Literal observed-axis ridge statistics. Both the frame and its allocation
are recomputed only at prescribed batch boundaries; all records enter the fit. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def controllerAction (loss : Loss) (n : ℕ) (x : Fin 3 → ℝ) : Action :=
  referenceAction loss (controller loss n x) (controller_interior loss n x)

structure RidgeState where
  time : ℕ
  gram : Mat
  rhs : Fin 3 → ℝ
  action : Action

def initialState (loss : Loss) (ridge : ℝ) : RidgeState where
  time := 0
  gram := ridge • 1
  rhs := 0
  action := controllerAction loss 0 0

def step (loss : Loss) (refresh : ℕ → Bool) (s : RidgeState)
    (z : LabeledBinaryOutcome) : RidgeState :=
  let u := axis s.action z.1
  let G := s.gram + blochOuter u
  let b := s.rhs + z.2.sign • u
  { time := s.time+1
    gram := G
    rhs := b
    action := if refresh (s.time+1) then controllerAction loss (s.time+1) (G⁻¹.mulVec b)
      else s.action }

def historyState (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (history : AdaptiveTrajectory LabeledBinaryOutcome) : RidgeState :=
  history.outcomes.foldl (step loss refresh) (initialState loss ridge)

def policy (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) : Policy :=
  fun _ history => (historyState loss ridge refresh history).action

def pathState (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) : RidgeState :=
  historyState loss ridge refresh (adaptiveInfinitePathPrefix n path)

def estimate (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) : Fin 3 → ℝ :=
  (pathState loss ridge refresh n path).gram⁻¹.mulVec (pathState loss ridge refresh n path).rhs

def actualAxis (p : Policy) (n : ℕ) (path : Path) : Fin 3 → ℝ :=
  axis (actualAction p n path) (path n).1

private theorem prefix_outcomes (n : ℕ) (path : Path) :
    (adaptiveInfinitePathPrefix n path).outcomes = List.ofFn (fun k : Fin n => path k.1) := by
  cases n <;> rfl

private theorem prefix_snoc (n : ℕ) (path : Path) :
    adaptiveInfinitePathPrefix (n+1) path = (adaptiveInfinitePathPrefix n path).snoc (path n) := by
  apply AdaptiveTrajectory.outcomes_injective
  rw [AdaptiveTrajectory.snoc, prefix_outcomes, prefix_outcomes]
  exact List.ofFn_succ_last

theorem pathState_zero (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (path : Path) :
    pathState loss ridge refresh 0 path = initialState loss ridge := rfl

theorem pathState_succ (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    pathState loss ridge refresh (n+1) path = step loss refresh (pathState loss ridge refresh n path) (path n) := by
  simp only [pathState,prefix_snoc,historyState,AdaptiveTrajectory.snoc,
    List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem pathState_time (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).time = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pathState_succ]; simpa [step] using congrArg Nat.succ ih

theorem pathState_action (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).action = actualAction (policy loss ridge refresh) n path := rfl

theorem pathState_gram (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).gram = ridge • 1 +
      ∑ k ∈ Finset.range n, blochOuter (actualAxis (policy loss ridge refresh) k path) := by
  induction n with
  | zero => simp [pathState_zero,initialState]
  | succ n ih =>
    rw [pathState_succ,Finset.sum_range_succ]
    change (pathState loss ridge refresh n path).gram + _ = _
    rw [ih,add_assoc]
    rfl

theorem pathState_rhs (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).rhs =
      ∑ k ∈ Finset.range n, (path k).2.sign • actualAxis (policy loss ridge refresh) k path := by
  induction n with
  | zero => simp [pathState_zero,initialState]
  | succ n ih =>
    rw [pathState_succ,Finset.sum_range_succ]
    change (pathState loss ridge refresh n path).rhs + _ = _
    rw [ih]
    rfl

theorem action_at_refresh (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path)
    (hn : refresh (n+1) = true) :
    actualAction (policy loss ridge refresh) (n+1) path =
      controllerAction loss (n+1) (estimate loss ridge refresh (n+1) path) := by
  rw [← pathState_action,pathState_succ]
  simp only [step,pathState_time,hn,Bool.true_eq,↓reduceIte]
  rw [estimate,pathState_succ]
  rfl

theorem action_between_refresh (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path)
    (hn : refresh (n+1) = false) :
    actualAction (policy loss ridge refresh) (n+1) path = actualAction (policy loss ridge refresh) n path := by
  rw [← pathState_action,pathState_succ]
  simp [step,pathState_time,hn,pathState_action]

theorem action_eq_lastRefresh (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    actualAction (policy loss ridge refresh) n path =
      controllerAction loss (P1.lastRefresh refresh n)
        (estimate loss ridge refresh (P1.lastRefresh refresh n) path) := by
  induction n with
  | zero =>
    simp [actualAction,policy,historyState,adaptiveInfinitePathPrefix,AdaptiveTrajectory.empty,
      initialState,P1.lastRefresh,estimate,pathState_zero]
  | succ n ih =>
    cases hr : refresh (n+1) with
    | false => rw [action_between_refresh loss ridge refresh n path hr,ih]; simp [P1.lastRefresh,hr]
    | true => rw [action_at_refresh loss ridge refresh n path hr]; simp [P1.lastRefresh,hr]

theorem actual_weight_floor (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) (k : Fin 3) :
    ExplorationRidge.epsilon n / 3 ≤ (actualAction (policy loss ridge refresh) n path).weight k := by
  rw [action_eq_lastRefresh]
  have h := weight_floor loss (P1.lastRefresh refresh n)
    (estimate loss ridge refresh (P1.lastRefresh refresh n) path) k
  exact (div_le_div_of_nonneg_right (ExplorationRidge.epsilon_antitone (P1.lastRefresh_le refresh n))
    (by norm_num)).trans h

end
end QubitOracle.AdaptiveDesign.P1Weighted
