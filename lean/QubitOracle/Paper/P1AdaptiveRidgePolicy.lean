import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedStageStability
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1UniformFrameBorn
import QubitOracle.Paper.P1UniformFrameInformation
/-! # A concrete history-only adaptive ridge policy
The sufficient statistics contain every observation. Batch boundaries control
when the frame is refreshed, not which observations enter the ridge fit.
-/
namespace QubitOracle.AdaptiveDesign.P1
open QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

/-- A total physical controller. Interior estimates are untouched; exterior
finite-sample estimates use the center until the next update. -/
def interiorize (x : Fin 3 → Real) : Fin 3 → Real :=
  if QubitOracle.blochNormSq x < 1 then x else 0

theorem interiorize_interior (x : Fin 3 → Real) :
    QubitOracle.blochNormSq (interiorize x) < 1 := by
  unfold interiorize
  split_ifs with h
  · exact h
  · norm_num [QubitOracle.blochNormSq]

theorem interiorize_tendsto {theta : Fin 3 → Real}
    (ht : QubitOracle.blochNormSq theta < 1)
    {x : Nat → Fin 3 → Real} (hx : Tendsto x atTop (nhds theta)) :
    Tendsto (fun n => interiorize (x n)) atTop (nhds theta) := by
  have hn := continuous_blochNormSq.continuousAt.tendsto.comp hx
  apply hx.congr'
  filter_upwards [(tendsto_order.1 hn).2 1 ht] with n hn
  simp only [Function.comp_apply] at hn
  simp [interiorize, hn]

/-- Reconstructible sufficient statistics and the frame currently in use. -/
structure RidgeState where
  time : Nat
  gram : Matrix (Fin 3) (Fin 3) Real
  rhs : Fin 3 → Real
  frame : UniformFrame

def initialRidgeState (ridge : Real) : RidgeState where
  time := 0
  gram := ridge • 1
  rhs := 0
  frame := canonicalUniformFrame 0

/-- One update, using the axis label that was actually observed. `refresh n`
means the next frame is recomputed after exactly n observations. -/
def ridgeStep (refresh : Nat → Bool) (s : RidgeState)
    (z : LabeledBinaryOutcome) : RidgeState :=
  let axis := (s.frame.axis z.1).1
  let gram := s.gram + QubitOracle.blochOuter axis
  let rhs := s.rhs + z.2.sign • axis
  { time := s.time + 1
    gram := gram
    rhs := rhs
    frame := if refresh (s.time + 1) then
      canonicalUniformFrame (interiorize (gram⁻¹.mulVec rhs)) else s.frame }

/-- Fold over the complete observed history, with no discarded observations. -/
def historyRidgeState (ridge : Real) (refresh : Nat → Bool)
    (history : AdaptiveTrajectory LabeledBinaryOutcome) : RidgeState :=
  history.outcomes.foldl (ridgeStep refresh) (initialRidgeState ridge)

def adaptiveRidgePolicy (ridge : Real) (refresh : Nat → Bool) : FramePolicy :=
  fun _ history => (historyRidgeState ridge refresh history).frame

def pathRidgeState (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) : RidgeState :=
  historyRidgeState ridge refresh (adaptiveInfinitePathPrefix n path)

def pathRidgeEstimator (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) : Fin 3 → Real :=
  (pathRidgeState ridge refresh n path).gram⁻¹.mulVec
    (pathRidgeState ridge refresh n path).rhs

private theorem prefix_outcomes (n : Nat) (path : Path) :
    (adaptiveInfinitePathPrefix n path).outcomes =
      List.ofFn (fun k : Fin n => path k.1) := by
  cases n with
  | zero => rfl
  | succ n => rfl

private theorem prefix_snoc (n : Nat) (path : Path) :
    adaptiveInfinitePathPrefix (n+1) path =
      (adaptiveInfinitePathPrefix n path).snoc (path n) := by
  apply AdaptiveTrajectory.outcomes_injective
  rw [AdaptiveTrajectory.snoc, prefix_outcomes, prefix_outcomes]
  exact List.ofFn_succ_last

theorem pathRidgeState_zero (ridge : Real) (refresh : Nat → Bool) (path : Path) :
    pathRidgeState ridge refresh 0 path = initialRidgeState ridge := rfl

theorem pathRidgeState_succ (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) :
    pathRidgeState ridge refresh (n+1) path =
      ridgeStep refresh (pathRidgeState ridge refresh n path) (path n) := by
  simp only [pathRidgeState, prefix_snoc, historyRidgeState, AdaptiveTrajectory.snoc,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem pathRidgeState_time (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) : (pathRidgeState ridge refresh n path).time = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pathRidgeState_succ]; simpa [ridgeStep] using congrArg Nat.succ ih

theorem pathRidgeState_frame (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) :
    (pathRidgeState ridge refresh n path).frame =
      actualFrame (adaptiveRidgePolicy ridge refresh) n path := rfl

/-- Exact sufficient-statistic identity for the Gram matrix. -/
theorem pathRidgeState_gram (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) :
    (pathRidgeState ridge refresh n path).gram = ridge • 1 +
      ∑ k ∈ Finset.range n,
        QubitOracle.blochOuter (actualAxis (adaptiveRidgePolicy ridge refresh) k path) := by
  induction n with
  | zero => simp [pathRidgeState_zero, initialRidgeState]
  | succ n ih =>
    rw [pathRidgeState_succ, Finset.sum_range_succ]
    change (pathRidgeState ridge refresh n path).gram + _ = _
    rw [ih, add_assoc]
    rfl

/-- Exact sufficient-statistic identity for the signed-response vector. -/
theorem pathRidgeState_rhs (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) :
    (pathRidgeState ridge refresh n path).rhs =
      ∑ k ∈ Finset.range n,
        (path k).2.sign • actualAxis (adaptiveRidgePolicy ridge refresh) k path := by
  induction n with
  | zero => simp [pathRidgeState_zero, initialRidgeState]
  | succ n ih =>
    rw [pathRidgeState_succ, Finset.sum_range_succ]
    change (pathRidgeState ridge refresh n path).rhs + _ = _
    rw [ih]
    rfl

/-- Every prescribed refresh chooses the oracle frame of the actual current
all-observation ridge estimate. This is an exact identity, not an asymptotic premise. -/
theorem actualFrame_at_refresh (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) (hn : refresh (n+1) = true) :
    actualFrame (adaptiveRidgePolicy ridge refresh) (n+1) path =
      canonicalUniformFrame (interiorize (pathRidgeEstimator ridge refresh (n+1) path)) := by
  rw [← pathRidgeState_frame, pathRidgeState_succ]
  simp only [ridgeStep, pathRidgeState_time, hn, Bool.true_eq, ↓reduceIte]
  rw [pathRidgeEstimator, pathRidgeState_succ]
  rfl

/-- Between prescribed refresh times the selected frame is unchanged. -/
theorem actualFrame_between_refresh (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) (hn : refresh (n+1) = false) :
    actualFrame (adaptiveRidgePolicy ridge refresh) (n+1) path =
      actualFrame (adaptiveRidgePolicy ridge refresh) n path := by
  rw [← pathRidgeState_frame, pathRidgeState_succ]
  simp [ridgeStep, pathRidgeState_time, hn, pathRidgeState_frame]

/-- Most recent prescribed update time. -/
def lastRefresh (refresh : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => if refresh (n+1) then n+1 else lastRefresh refresh n

theorem lastRefresh_le (refresh : Nat → Bool) (n : Nat) : lastRefresh refresh n ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [lastRefresh]
    split_ifs <;> omega

theorem lastRefresh_monotone (refresh : Nat → Bool) : Monotone (lastRefresh refresh) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [lastRefresh]
  split_ifs
  · exact (lastRefresh_le refresh n).trans (Nat.le_succ n)
  · exact le_rfl

theorem lastRefresh_tendsto (refresh : Nat → Bool)
    (hrefresh : ∀ K : Nat, ∃ n, K ≤ n ∧ refresh n = true) :
    Tendsto (lastRefresh refresh) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  obtain ⟨n, hn, hr⟩ := hrefresh (K+1)
  have hn0 : 0 < n := by omega
  have heq : lastRefresh refresh n = n := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
    simp [lastRefresh, hr]
  refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  have hh := lastRefresh_monotone refresh hm
  rw [heq] at hh
  omega

/-- The frame used at any shot is the oracle frame computed from every
observation available at the most recent prescribed refresh. -/
theorem actualFrame_eq_lastRefresh (ridge : Real) (refresh : Nat → Bool)
    (n : Nat) (path : Path) :
    actualFrame (adaptiveRidgePolicy ridge refresh) n path =
      canonicalUniformFrame (interiorize
        (pathRidgeEstimator ridge refresh (lastRefresh refresh n) path)) := by
  induction n with
  | zero => simp [actualFrame, adaptiveRidgePolicy, historyRidgeState,
      adaptiveInfinitePathPrefix, AdaptiveTrajectory.empty, initialRidgeState,
      lastRefresh, pathRidgeEstimator, pathRidgeState_zero, interiorize,
      QubitOracle.blochNormSq]
  | succ n ih =>
    cases hr : refresh (n+1) with
    | false =>
      rw [actualFrame_between_refresh ridge refresh n path hr, ih]
      simp [lastRefresh, hr]
    | true =>
      rw [actualFrame_at_refresh ridge refresh n path hr]
      simp [lastRefresh, hr]

end
end QubitOracle.AdaptiveDesign.P1
