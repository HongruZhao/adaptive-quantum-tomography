import QubitOracle.Paper.InformationFullPathSLLN

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators ENNReal
open Filter MeasureTheory ProbabilityTheory

/-- Real-valued indicator of an exploration flag. -/
def explorationIndicator : Bool → ℝ
  | false => 0
  | true => 1

/-- The latent exploration flag is selected predictably with probability
`epsilon (history.length + 1)`.  Thus `epsilon` uses the paper's one-based shot
indexing. -/
def explorationFlagPolicy
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) : AdaptivePolicy Bool Unit where
  mass history z :=
    match z with
    | false => 1 - epsilon (history.length + 1)
    | true => epsilon (history.length + 1)
  mass_nonneg history z := by
    cases z with
    | false =>
        exact sub_nonneg.mpr (hepsilon1 (history.length + 1))
    | true =>
        exact hepsilon0 (history.length + 1)
  sum_mass history := by
    rw [Fintype.sum_bool]
    change epsilon (history.length + 1) +
      (1 - epsilon (history.length + 1)) = 1
    ring

/-- Deterministic dummy outcome kernel used to place the latent flags in the
already-verified adaptive path-space construction. -/
def explorationUnitOutcomeKernel : OutcomeKernel Unit Bool Unit where
  mass _ _ := 1
  mass_nonneg _ _ := zero_le_one
  sum_mass _ := by simp

/-- Probability law of the complete latent exploration-flag trajectory. -/
def explorationFlagTrajectoryMeasure
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    Measure (ℕ → Bool × Unit) :=
  adaptiveTrajectoryMeasure
    (explorationFlagPolicy epsilon hepsilon0 hepsilon1)
    explorationUnitOutcomeKernel ()

instance explorationFlagTrajectoryMeasure_isProbabilityMeasure
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    IsProbabilityMeasure
      (explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1) := by
  unfold explorationFlagTrajectoryMeasure adaptiveTrajectoryMeasure
  infer_instance

/-- A prefix through zero-based coordinate `n` contains exactly `n + 1`
observations. -/
@[simp] theorem trajectoryPrefixHistory_length
    {M Y : Type*} {n : ℕ} (pref : Finset.Iic n → M × Y) :
    (trajectoryPrefixHistory pref).length = n + 1 := by
  simp [trajectoryPrefixHistory]

/-- Centered exploration flag at the next coordinate after the prefix through
coordinate `n`. -/
def explorationTailInnovation
    (epsilon : ℕ → ℝ) (n : ℕ) (omega : ℕ → Bool × Unit) : ℝ :=
  explorationIndicator (omega (n + 1)).1 - epsilon (n + 2)

/-- The centered Bernoulli increment is uniformly bounded by one. -/
theorem explorationTailInnovation_norm_le_one
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (n : ℕ) (omega : ℕ → Bool × Unit) :
    ‖explorationTailInnovation epsilon n omega‖ ≤ 1 := by
  unfold explorationTailInnovation
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · cases hz : (omega (n + 1)).1 <;>
      simp [explorationIndicator, hz] <;>
      linarith [hepsilon0 (n + 2), hepsilon1 (n + 2)]
  · cases hz : (omega (n + 1)).1 <;>
      simp [explorationIndicator, hz] <;>
      linarith [hepsilon0 (n + 2), hepsilon1 (n + 2)]

private def explorationPrefixInnovation
    (epsilon : ℕ → ℝ) (n : ℕ)
    (pref : Finset.Iic (n + 1) → Bool × Unit) : ℝ :=
  explorationIndicator
      (pref ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1 -
    epsilon (n + 2)

private theorem explorationTailInnovation_eq_prefix_comp
    (epsilon : ℕ → ℝ) (n : ℕ) :
    explorationTailInnovation epsilon n =
      explorationPrefixInnovation epsilon n ∘
        Preorder.frestrictLe (n + 1) := by
  rfl

/-- The next centered flag is measurable at the next filtration time. -/
theorem explorationTailInnovation_stronglyMeasurable_succ
    (epsilon : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[MeasureTheory.Filtration.piLE (n + 1)]
      (explorationTailInnovation epsilon n) := by
  rw [explorationTailInnovation_eq_prefix_comp,
    MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  have hg : Measurable (explorationPrefixInnovation epsilon n) :=
    measurable_of_countable _
  simpa [Function.comp_def] using
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Every centered flag is integrable under any finite path law. -/
theorem explorationTailInnovation_integrable
    (mu : Measure (ℕ → Bool × Unit)) [IsFiniteMeasure mu]
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (n : ℕ) :
    Integrable (explorationTailInnovation epsilon n) mu := by
  refine Integrable.of_bound
    ((explorationTailInnovation_stronglyMeasurable_succ epsilon n).mono
      (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE (n + 1))).aestronglyMeasurable
    1 ?_
  exact ae_of_all mu fun omega =>
    explorationTailInnovation_norm_le_one epsilon hepsilon0 hepsilon1 n omega

/-- Exact one-step centering under the trajectory kernel of the latent flag
process. -/
theorem integral_explorationTailInnovation_adaptiveTrajectoryKernel_zero
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (n : ℕ) (pref : Finset.Iic n → Bool × Unit) :
    ∫ z, explorationIndicator z.1 - epsilon (n + 2)
      ∂ (adaptiveTrajectoryKernel
          (explorationFlagPolicy epsilon hepsilon0 hepsilon1)
          explorationUnitOutcomeKernel () n) pref = 0 := by
  change
    ∫ z, explorationIndicator z.1 - epsilon (n + 2)
      ∂ finiteMassMeasure
          ((adaptiveJointKernel
            (explorationFlagPolicy epsilon hepsilon0 hepsilon1)
            explorationUnitOutcomeKernel ()).mass
              (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel
            (explorationFlagPolicy epsilon hepsilon0 hepsilon1)
            explorationUnitOutcomeKernel ()).mass_nonneg
              (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel
            (explorationFlagPolicy epsilon hepsilon0 hepsilon1)
            explorationUnitOutcomeKernel ()).sum_mass
              (trajectoryPrefixHistory pref)) = 0
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [adaptiveJointKernel, explorationFlagPolicy,
    explorationUnitOutcomeKernel, explorationIndicator, smul_eq_mul]
  ring

/-- The partial sums of centered exploration flags are strongly adapted. -/
theorem explorationPartialSum_stronglyAdapted
    (epsilon : ℕ → ℝ) :
    StronglyAdapted MeasureTheory.Filtration.piLE
      (scalarMartingalePartialSum (explorationTailInnovation epsilon)) := by
  intro n
  unfold scalarMartingalePartialSum
  have hsum := Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
    (explorationTailInnovation_stronglyMeasurable_succ epsilon k).mono
      (MeasureTheory.Filtration.mono MeasureTheory.Filtration.piLE
        (Nat.succ_le_iff.2 (Finset.mem_range.1 hk)))
  have heq :
      (fun omega : ℕ → Bool × Unit =>
        ∑ k ∈ Finset.range n, explorationTailInnovation epsilon k omega) =
      ∑ k ∈ Finset.range n, explorationTailInnovation epsilon k := by
    funext omega
    simp
  rw [heq]
  exact hsum

/-- The centered-flag partial sums are integrable. -/
theorem explorationPartialSum_integrable
    (mu : Measure (ℕ → Bool × Unit)) [IsFiniteMeasure mu]
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    ∀ n, Integrable
      (scalarMartingalePartialSum (explorationTailInnovation epsilon) n) mu := by
  intro n
  induction n with
  | zero =>
      change Integrable (0 : (ℕ → Bool × Unit) → ℝ) mu
      exact integrable_zero (ℕ → Bool × Unit) ℝ mu
  | succ n ih =>
      rw [show scalarMartingalePartialSum (explorationTailInnovation epsilon) (n + 1) =
          scalarMartingalePartialSum (explorationTailInnovation epsilon) n +
            explorationTailInnovation epsilon n by
        funext omega
        simp [scalarMartingalePartialSum, Finset.sum_range_succ]]
      exact ih.add
        (explorationTailInnovation_integrable
          mu epsilon hepsilon0 hepsilon1 n)

/-- The next centered flag has conditional expectation zero under the actual
latent-flag trajectory law. -/
theorem explorationTailInnovation_condExp_zero
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1)
    (n : ℕ) :
    (explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1)[
      explorationTailInnovation epsilon n |
      MeasureTheory.Filtration.piLE n] =ᵐ[
        explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let q := explorationFlagPolicy epsilon hepsilon0 hepsilon1
  let p := explorationUnitOutcomeKernel
  let mu : Measure (ℕ → Bool × Unit) := adaptiveTrajectoryMeasure q p ()
  let X : (ℕ → Bool × Unit) → (Finset.Iic n → Bool × Unit) :=
    Preorder.frestrictLe (π := fun _ : ℕ => Bool × Unit) n
  let Ynext : (ℕ → Bool × Unit) → Bool × Unit := fun omega => omega (n + 1)
  let f : (Finset.Iic n → Bool × Unit) × (Bool × Unit) → ℝ := fun z =>
    explorationIndicator z.2.1 - epsilon (n + 2)
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hYnext : Measurable Ynext := measurable_pi_apply (n + 1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hf_int : Integrable (fun omega => f (X omega, Ynext omega)) mu := by
    refine Integrable.of_bound
      (((measurable_of_countable f).comp
        (hX.prodMk hYnext)).aestronglyMeasurable) 1 ?_
    exact ae_of_all mu fun omega =>
      explorationTailInnovation_norm_le_one
        epsilon hepsilon0 hepsilon1 n omega
  have hcondExp :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hX hYnext.aemeasurable hf hf_int
  have hcondPrefix :
      (fun pref => ProbabilityTheory.condDistrib Ynext X mu pref) =ᵐ[Measure.map X mu]
        (fun pref => adaptiveTrajectoryKernel q p () n pref) := by
    simpa only [mu, X, Ynext, q, p, adaptiveTrajectoryMeasure] using
      adaptiveTrajectory_condDistrib_next q p () n
  have hcondPath :
      (fun omega => ProbabilityTheory.condDistrib Ynext X mu (X omega)) =ᵐ[mu]
        (fun omega => adaptiveTrajectoryKernel q p () n (X omega)) := by
    refine (ae_map_iff hX.aemeasurable ?_).1 hcondPrefix
    exact Set.Finite.measurableSet (Set.toFinite _)
  have hzero :
      (fun omega =>
        ∫ y, f (X omega, y)
          ∂ ProbabilityTheory.condDistrib Ynext X mu (X omega)) =ᵐ[mu] 0 := by
    filter_upwards [hcondPath] with omega homega
    rw [homega]
    exact integral_explorationTailInnovation_adaptiveTrajectoryKernel_zero
      epsilon hepsilon0 hepsilon1 n (X omega)
  have hfinal := hcondExp.trans hzero
  change
    mu[(fun omega => f (X omega, Ynext omega)) |
      MeasurableSpace.comap X MeasurableSpace.pi] =ᵐ[mu] 0
  exact hfinal

/-- The centered exploration-flag partial sums form a martingale under their
actual trajectory law. -/
theorem explorationPartialSum_martingale
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    Martingale
      (scalarMartingalePartialSum (explorationTailInnovation epsilon))
      MeasureTheory.Filtration.piLE
      (explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1) := by
  let mu := explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  let increment := explorationTailInnovation epsilon
  let partialSum := scalarMartingalePartialSum increment
  have hadapted : StronglyAdapted MeasureTheory.Filtration.piLE partialSum := by
    simpa [partialSum, increment] using
      explorationPartialSum_stronglyAdapted epsilon
  have hintegrable : ∀ n, Integrable (partialSum n) mu := by
    simpa [partialSum, increment, mu] using
      explorationPartialSum_integrable
        (explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1)
        epsilon hepsilon0 hepsilon1
  refine martingale_nat hadapted hintegrable ?_
  intro n
  have hcenter :
      mu[increment n | MeasureTheory.Filtration.piLE n] =ᵐ[mu] 0 := by
    simpa [mu, increment] using
      explorationTailInnovation_condExp_zero
        epsilon hepsilon0 hepsilon1 n
  have hself :
      mu[partialSum n | MeasureTheory.Filtration.piLE n] = partialSum n :=
    condExp_of_stronglyMeasurable
      (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE n)
      (hadapted n) (hintegrable n)
  have hadd := condExp_add (hintegrable n)
    (explorationTailInnovation_integrable
      mu epsilon hepsilon0 hepsilon1 n)
    (MeasureTheory.Filtration.piLE n)
  have hrec : partialSum n + increment n = partialSum (n + 1) := by
    funext omega
    simp [partialSum, increment, scalarMartingalePartialSum,
      Finset.sum_range_succ]
  calc
    partialSum n =ᵐ[mu]
        mu[partialSum n | MeasureTheory.Filtration.piLE n] :=
      ae_of_all mu (congrFun hself.symm)
    _ =ᵐ[mu]
        mu[partialSum n | MeasureTheory.Filtration.piLE n] +
          mu[increment n | MeasureTheory.Filtration.piLE n] := by
            filter_upwards [hcenter] with omega homega
            simp [homega]
    _ =ᵐ[mu]
        mu[partialSum n + increment n |
          MeasureTheory.Filtration.piLE n] := hadd.symm
    _ =ᵐ[mu]
        mu[partialSum (n + 1) |
          MeasureTheory.Filtration.piLE n] :=
      condExp_congr_ae (ae_of_all mu (congrFun hrec))

/-- Almost-sure strong law for all post-initial centered flags. -/
theorem explorationTailInnovation_strongLaw
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n,
              explorationTailInnovation epsilon k omega)
        atTop (nhds 0) := by
  let mu := explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n omega,
      ‖explorationTailInnovation epsilon n omega‖ ≤ C := by
    refine ⟨1, zero_le_one, ?_⟩
    intro n omega
    exact
        explorationTailInnovation_norm_le_one
          epsilon hepsilon0 hepsilon1 n omega
  have h := hallHeyde1980_theorem2_18_of_uniform_bound
    mu MeasureTheory.Filtration.piLE
    (explorationTailInnovation epsilon)
    (by
      simpa [mu] using
        explorationPartialSum_martingale epsilon hepsilon0 hepsilon1)
    hbound
  simpa [mu, scalarMartingaleNormalizedSum,
    scalarMartingalePartialSum] using h

/-- Centered flag using the paper's one-based schedule and the trajectory's
zero-based coordinate. -/
def explorationAllShotInnovation
    (epsilon : ℕ → ℝ) (omega : ℕ → Bool × Unit) (k : ℕ) : ℝ :=
  explorationIndicator (omega k).1 - epsilon (k + 1)

/-- Prepending the initial centered flag gives exactly the all-shot sequence. -/
theorem explorationAllShotInnovation_eq_prepend
    (epsilon : ℕ → ℝ) (omega : ℕ → Bool × Unit) :
    explorationAllShotInnovation epsilon omega =
      prependSequence
        (explorationAllShotInnovation epsilon omega 0)
        (explorationTailInnovation epsilon · omega) := by
  funext k
  cases k <;> rfl

/-- Exact realized-exploration-fraction strong law, including the initial
shot. -/
theorem explorationFraction_realized_strongLaw
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n,
              explorationAllShotInnovation epsilon omega k)
        atTop (nhds 0) := by
  filter_upwards
    [explorationTailInnovation_strongLaw
      epsilon hepsilon0 hepsilon1] with omega homega
  have htail : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            explorationTailInnovation epsilon k omega)
      atTop (nhds 0) := by
    simpa only [smul_eq_mul] using homega
  have hfull := normalized_prependSequence_tendsto_zero
    (E := ℝ)
    (explorationAllShotInnovation epsilon omega 0)
    (explorationTailInnovation epsilon · omega)
    htail
  rw [explorationAllShotInnovation_eq_prepend]
  simpa only [smul_eq_mul] using hfull

namespace Label

/-- `eq:SI_exploration_fraction_realized`: the realized latent exploration
frequency differs from its predictable schedule average by `o(1)` almost
surely. -/
theorem eq_SI_exploration_fraction_realized
    (epsilon : ℕ → ℝ)
    (hepsilon0 : ∀ i, 0 ≤ epsilon i)
    (hepsilon1 : ∀ i, epsilon i ≤ 1) :
    ∀ᵐ omega ∂ explorationFlagTrajectoryMeasure epsilon hepsilon0 hepsilon1,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n,
              (explorationIndicator (omega k).1 - epsilon (k + 1)))
        atTop (nhds 0) := by
  exact explorationFraction_realized_strongLaw
    epsilon hepsilon0 hepsilon1

end Label

end QubitOracle.Paper
