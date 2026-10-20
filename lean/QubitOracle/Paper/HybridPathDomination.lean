import QubitOracle.Paper.AdaptiveTrajectoryExperiment

namespace QubitOracle.Paper

open Filter Finset MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v w x

/-!
# Domination of hybrid Ionescu--Tulcea path laws

The main theorem in this file closes the measure-theoretic bridge left explicit
in `AdaptiveTrajectoryExperiment`: if a hybrid adaptive law differs from its
base law during only finitely many stages, and every changed response law is
dominated by the corresponding base response law, then the complete infinite
path law is dominated by the base path law.

The proof is internal to Lean and Mathlib.  It first proves domination of the
finite-prefix marginals, proves equality of the continuation kernels after the
last changed stage, and then uses `Kernel.traj_comp_partialTraj` to factor both
infinite laws through their common tail.  No theorem about infinite products
is assumed as an axiom.
-/

section GenericIonescuTulcea

variable {X : ℕ → Type x} [∀ n, MeasurableSpace (X n)]
variable (κ η : (n : ℕ) → Kernel ((i : Iic n) → X i) (X (n + 1)))
variable [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]

/-- Domination of a transition kernel is preserved by the one-step
`partialTraj` construction, which retains the prefix and appends one sample. -/
theorem partialTraj_succ_self_absolutelyContinuous
    {a : ℕ} (hκη : ∀ z, κ a z ≪ η a z)
    (z : (i : Iic a) → X i) :
    Kernel.partialTraj κ a (a + 1) z ≪
      Kernel.partialTraj η a (a + 1) z := by
  rw [Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self,
    Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.prod_apply, Kernel.prod_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton a).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton a).measurable]
  exact (Measure.AbsolutelyContinuous.rfl.prod
    ((hκη z).map (MeasurableEquiv.piSingleton a).measurable)).map
      measurable_IicProdIoc

/-- Pointwise domination of the transition kernels on the finite interval
`[a,b)` implies domination of the corresponding finite-prefix kernels. -/
theorem partialTraj_absolutelyContinuous_of_pointwise
    {a b : ℕ} (hab : a ≤ b)
    (hκη : ∀ k, a ≤ k → k < b → ∀ z, κ k z ≪ η k z) :
    ∀ z, Kernel.partialTraj κ a b z ≪ Kernel.partialTraj η a b z := by
  revert hκη
  induction b, hab using Nat.le_induction with
  | base =>
      intro _ z
      rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
  | succ k hak ih =>
      intro hκη z
      rw [Kernel.partialTraj_succ_eq_comp hak,
        Kernel.partialTraj_succ_eq_comp hak,
        Kernel.comp_apply, Kernel.comp_apply]
      exact
        (ih (fun j haj hjk => hκη j haj (Nat.lt_succ_of_lt hjk)) z).comp
          (Filter.Eventually.of_forall fun hist =>
            partialTraj_succ_self_absolutelyContinuous κ η
              (hκη k hak (Nat.lt_succ_self k)) hist)

/-- If two transition families agree from stage `a` onward, all their
finite continuation kernels starting at `a` agree. -/
theorem partialTraj_eq_of_eq_from
    {a b : ℕ} (hab : a ≤ b)
    (hκη : ∀ k, a ≤ k → κ k = η k) :
    Kernel.partialTraj κ a b = Kernel.partialTraj η a b := by
  induction b, hab using Nat.le_induction with
  | base =>
      rw [Kernel.partialTraj_self, Kernel.partialTraj_self]
  | succ k hak ih =>
      have hstep :
          Kernel.partialTraj κ k (k + 1) =
            Kernel.partialTraj η k (k + 1) := by
        rw [Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self,
          hκη k hak]
      rw [Kernel.partialTraj_succ_eq_comp hak,
        Kernel.partialTraj_succ_eq_comp hak, ih, hstep]

/-- Equality of all transition kernels from stage `a` onward implies equality
of the complete Ionescu--Tulcea continuation kernels given the prefix at `a`. -/
theorem traj_eq_of_eq_from
    {a : ℕ} (hκη : ∀ k, a ≤ k → κ k = η k) :
    Kernel.traj κ a = Kernel.traj η a := by
  refine Kernel.eq_traj' η a (Kernel.traj κ a) ?_
  intro b hab
  rw [Kernel.traj_map_frestrictLe]
  exact partialTraj_eq_of_eq_from κ η hab hκη

/-- The finite-prefix marginal of `trajMeasure` is the initial law, embedded as
an `Iic 0`-prefix, followed by `partialTraj`. -/
theorem map_frestrictLe_trajMeasure_eq_partialTraj_comp
    (μ : Measure (X 0)) (n : ℕ) :
    (Kernel.trajMeasure μ κ).map (frestrictLe n) =
      Kernel.partialTraj κ 0 n ∘ₘ
        μ.map (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm := by
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe]
  rfl

/-- Initial-law domination and transition domination through stage `n - 1`
imply domination of the marginal on coordinates `0,...,n`. -/
theorem map_frestrictLe_trajMeasure_absolutelyContinuous
    {μ ν : Measure (X 0)} (n : ℕ) (hμν : μ ≪ ν)
    (hκη : ∀ k, k < n → ∀ z, κ k z ≪ η k z) :
    (Kernel.trajMeasure μ κ).map (frestrictLe n) ≪
      (Kernel.trajMeasure ν η).map (frestrictLe n) := by
  rw [map_frestrictLe_trajMeasure_eq_partialTraj_comp κ μ n,
    map_frestrictLe_trajMeasure_eq_partialTraj_comp η ν n]
  exact
    (hμν.map (MeasurableEquiv.piUnique (fun i : Iic 0 => X i)).symm.measurable).comp
      (Filter.Eventually.of_forall fun initialPrefix =>
        partialTraj_absolutelyContinuous_of_pointwise κ η (Nat.zero_le n)
          (fun k _ hk => hκη k hk) initialPrefix)

/-- Exact finite-prefix/common-tail factorization of an Ionescu--Tulcea path
measure. -/
theorem trajMeasure_eq_traj_comp_prefix
    (μ : Measure (X 0)) (n : ℕ) :
    Kernel.trajMeasure μ κ =
      Kernel.traj κ n ∘ₘ
        (Kernel.trajMeasure μ κ).map (frestrictLe n) := by
  rw [map_frestrictLe_trajMeasure_eq_partialTraj_comp κ μ n,
    Measure.comp_assoc,
    Kernel.traj_comp_partialTraj (κ := κ) (Nat.zero_le n)]
  rfl

/-- A finite-modification theorem for Ionescu--Tulcea laws.  Coordinate zero
has law `μ`/`ν`; kernels with index `< n` may differ but are pointwise
dominated; all kernels with index `≥ n` are identical.  Under exactly these
hypotheses, the complete first path law is absolutely continuous with respect
to the second. -/
theorem trajMeasure_absolutelyContinuous_of_finite_modification
    {μ ν : Measure (X 0)} (n : ℕ) (hμν : μ ≪ ν)
    (hprefix : ∀ k, k < n → ∀ z, κ k z ≪ η k z)
    (htail : ∀ k, n ≤ k → κ k = η k) :
    Kernel.trajMeasure μ κ ≪ Kernel.trajMeasure ν η := by
  rw [trajMeasure_eq_traj_comp_prefix κ μ n,
    trajMeasure_eq_traj_comp_prefix η ν n,
    traj_eq_of_eq_from κ η htail]
  exact
    (map_frestrictLe_trajMeasure_absolutelyContinuous κ η n hμν hprefix).comp_right
      (Kernel.traj η n)

end GenericIonescuTulcea

section AdaptiveSpecialization

/-- The Ionescu--Tulcea transition inherits response-level domination after
the predictable design has been evaluated on the observed prefix. -/
theorem adaptiveIonescuStepKernel_absolutelyContinuous
    {Theta : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    {theta theta0 : Theta} (hdom : ResponseDominatedAt protocol theta theta0)
    (k : ℕ) (hist : (i : Iic k) → AdaptiveOutcomeProcess Outcome i) :
    adaptiveIonescuStepKernel protocol theta k hist ≪
      adaptiveIonescuStepKernel protocol theta0 k hist := by
  simpa [adaptiveIonescuStepKernel] using
    adaptiveStepKernel_absolutelyContinuous protocol hdom (k + 1)
      (iicToAdaptiveTrajectory hist)

/-- The hybrid initial outcome is either already the base outcome law (`n=0`)
or is dominated by it through the response-level hypothesis. -/
theorem hybridInitialOutcomeMeasure_absolutelyContinuous
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hresponse : HybridResponseDominatedByBase protocol localize theta0)
    (n : ℕ) (h : LANParameter D) :
    hybridInitialOutcomeMeasure protocol localize theta0 n h ≪
      adaptiveInitialOutcomeMeasure protocol theta0 := by
  by_cases hn : 0 < n
  · simp only [hybridInitialOutcomeMeasure, hybridStageParameter, hn, if_pos]
    exact hresponse n h (protocol.design 0 AdaptiveTrajectory.empty)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [hybridInitialOutcomeMeasure, hybridStageParameter]
    exact Measure.AbsolutelyContinuous.rfl

/-- Every hybrid transition is dominated by the base transition: before the
horizon this follows from response domination, and from the horizon onward the
two kernels are definitionally equal. -/
theorem hybridIonescuStepKernel_absolutelyContinuous
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hresponse : HybridResponseDominatedByBase protocol localize theta0)
    (n : ℕ) (h : LANParameter D) (k : ℕ)
    (hist : (i : Iic k) → AdaptiveOutcomeProcess Outcome i) :
    hybridIonescuStepKernel protocol localize theta0 n h k hist ≪
      adaptiveIonescuStepKernel protocol theta0 k hist := by
  by_cases hk : k + 1 < n
  · simpa [hybridIonescuStepKernel, hybridStageParameter, hk] using
      adaptiveIonescuStepKernel_absolutelyContinuous protocol
        (hresponse n h) k hist
  · rw [hybridIonescuStepKernel_eq_base_of_tail
      protocol localize theta0 n h k (Nat.le_of_not_gt hk)]

set_option maxHeartbeats 1000000 in
/-- Per-horizon specialization of the finite-modification theorem to the
hybrid adaptive path law. -/
theorem hybridInfiniteTrajectoryMeasure_absolutelyContinuous_of_responseDomination
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hresponse : HybridResponseDominatedByBase protocol localize theta0)
    (n : ℕ) (h : LANParameter D) :
    hybridInfiniteTrajectoryMeasure protocol localize theta0 n h ≪
      adaptiveInfiniteTrajectoryMeasure protocol theta0 := by
  let μh := hybridInitialOutcomeMeasure protocol localize theta0 n h
  let μ0 := adaptiveInitialOutcomeMeasure protocol theta0
  let κh := hybridIonescuStepKernel protocol localize theta0 n h
  let κ0 := adaptiveIonescuStepKernel protocol theta0
  letI : ∀ k, IsMarkovKernel
      (κh k) :=
    fun k => hybridIonescuStepKernel_isMarkov protocol localize theta0 n h k
  letI : ∀ k, IsMarkovKernel
      (κ0 k) :=
    fun k => adaptiveIonescuStepKernel_isMarkov protocol theta0 k
  have htraj : Kernel.trajMeasure μh κh ≪ Kernel.trajMeasure μ0 κ0 :=
    trajMeasure_absolutelyContinuous_of_finite_modification
      κh κ0 n
      (by
        dsimp only [μh, μ0]
        exact hybridInitialOutcomeMeasure_absolutelyContinuous
          protocol localize theta0 hresponse n h)
      (by
        intro k _ hist
        dsimp only [κh, κ0]
        exact hybridIonescuStepKernel_absolutelyContinuous
          protocol localize theta0 hresponse n h k hist)
      (by
        intro k hk
        dsimp only [κh, κ0]
        exact hybridIonescuStepKernel_eq_base_of_tail
          protocol localize theta0 n h k (hk.trans k.le_succ))
  simpa only [μh, μ0, κh, κ0, hybridInfiniteTrajectoryMeasure,
    adaptiveInfiniteTrajectoryMeasure] using htraj

/-- Response-level domination closes the exact full-path premise used by the
adaptive LAN theorem.  The finite number of changed stages is essential:
pointwise domination alone would not imply domination for arbitrary infinite
products. -/
theorem hybridFullPathDominatedByBase_of_responseDomination
    {D : Type*} [Fintype D] {Theta : Type u}
    {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : ℕ → LANParameter D → Theta) (theta0 : Theta)
    (hresponse : HybridResponseDominatedByBase protocol localize theta0) :
    HybridFullPathDominatedByBase protocol localize theta0 := by
  intro n h
  exact hybridInfiniteTrajectoryMeasure_absolutelyContinuous_of_responseDomination
    protocol localize theta0 hresponse n h

end AdaptiveSpecialization

end

end QubitOracle.Paper
