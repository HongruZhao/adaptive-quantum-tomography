import QubitOracle.Paper.AdaptiveInformationPath

/-!
# History-dependent adaptive information martingales

The mixed-state path proof uses an information matrix indexed by a fixed axis
map.  Rank-one moving-frame protocols instead choose a basis, and hence an
information matrix, predictably from the observed history.  This module proves
the common finite adaptive-path theorem for an arbitrary history-dependent
information field.

The martingale is derived from the actual Ionescu--Tulcea trajectory law.  The
strong-law endpoint is available either under the exact Hall--Heyde weighted
conditional-moment premise or under a deterministic uniform increment bound,
whose Hall--Heyde premise is discharged in Lean.
-/

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

/-- Policy-conditional mean of a history-dependent information matrix. -/
def historyPolicyMeanInformation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (history : SequentialHistory M Y) : Matrix D D ℝ :=
  ∑ m, q.mass history m • information history m

/-- Centered information increment when both the design and its information
matrix may depend predictably on the observed history. -/
def historyInformationInnovation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (history : SequentialHistory M Y) (setting : M) : Matrix D D ℝ :=
  information history setting - historyPolicyMeanInformation q information history

/-- Pointwise predictable decomposition of a selected information matrix. -/
theorem historyInformation_eq_mean_add_innovation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (history : SequentialHistory M Y) (setting : M) :
    information history setting =
      historyPolicyMeanInformation q information history +
        historyInformationInnovation q information history setting := by
  simp [historyInformationInnovation]

/-- Exact one-step centering under the adaptive setting-outcome kernel. -/
theorem integral_historyInformationInnovation_adaptiveJointKernel_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (history : SequentialHistory M Y) (i j : D) :
    ∫ z, historyInformationInnovation q information history z.1 i j
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass history)
          ((adaptiveJointKernel q p theta).mass_nonneg history)
          ((adaptiveJointKernel q p theta).sum_mass history) = 0 := by
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type]
  change
    (∑ m : M, ∑ y : Y,
      (q.mass history m * p.mass (theta, m) y) *
        historyInformationInnovation q information history m i j) = 0
  calc
    (∑ m : M, ∑ y : Y,
        (q.mass history m * p.mass (theta, m) y) *
          historyInformationInnovation q information history m i j) =
        ∑ m : M,
          (q.mass history m *
              historyInformationInnovation q information history m i j) *
            (∑ y : Y, p.mass (theta, m) y) := by
              apply Finset.sum_congr rfl
              intro m _
              calc
                (∑ y : Y,
                    (q.mass history m * p.mass (theta, m) y) *
                      historyInformationInnovation q information history m i j) =
                    ∑ y : Y,
                      (q.mass history m *
                          historyInformationInnovation q information history m i j) *
                        p.mass (theta, m) y := by
                          apply Finset.sum_congr rfl
                          intro y _
                          ring
                _ =
                    (q.mass history m *
                        historyInformationInnovation q information history m i j) *
                      (∑ y : Y, p.mass (theta, m) y) := by
                        rw [Finset.mul_sum]
    _ = ∑ m : M, q.mass history m *
          historyInformationInnovation q information history m i j := by
            apply Finset.sum_congr rfl
            intro m _
            rw [p.sum_mass]
            ring
    _ = 0 := by
      simp only [historyInformationInnovation, historyPolicyMeanInformation,
        Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, q.sum_mass]
      ring

/-- Centering under the trajectory kernel conditional on a realized prefix. -/
theorem integral_historyInformationInnovation_adaptiveTrajectoryKernel_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (pref : Finset.Iic n → M × Y) (i j : D) :
    ∫ z,
        historyInformationInnovation q information
          (trajectoryPrefixHistory pref) z.1 i j
      ∂ (adaptiveTrajectoryKernel q p theta n) pref = 0 := by
  change
    ∫ z,
        historyInformationInnovation q information
          (trajectoryPrefixHistory pref) z.1 i j
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel q p theta).mass_nonneg (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel q p theta).sum_mass (trajectoryPrefixHistory pref)) = 0
  exact integral_historyInformationInnovation_adaptiveJointKernel_zero
    q p theta information (trajectoryPrefixHistory pref) i j

/-- Post-initial history-dependent information innovation on the canonical
trajectory. -/
def historyPathInformationInnovation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (omega : ℕ → M × Y) : Matrix D D ℝ :=
  historyInformationInnovation q information
    (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
    (omega (n + 1)).1

private def historyPrefixInformationInnovation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (pref : Finset.Iic (n + 1) → M × Y) : Matrix D D ℝ :=
  historyInformationInnovation q information
    (trajectoryPrefixHistory
      (fun k : Finset.Iic n =>
        pref ⟨k.1, Finset.mem_Iic.mpr
          ((Finset.mem_Iic.mp k.2).trans (Nat.le_succ n))⟩))
    (pref ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1

private theorem historyPathInformationInnovation_eq_prefix_comp
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) :
    historyPathInformationInnovation q information n =
      historyPrefixInformationInnovation q information n ∘
        Preorder.frestrictLe (n + 1) := by
  funext omega
  unfold historyPathInformationInnovation historyPrefixInformationInnovation
  apply congrArg (fun h =>
    historyInformationInnovation q information h (omega (n + 1)).1)
  apply congrArg trajectoryPrefixHistory
  funext k
  rfl

/-- Every scalar coordinate is measurable one step after the conditioning
prefix. -/
theorem historyPathInformationInnovation_stronglyMeasurable_succ
    {M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (i j : D) :
    StronglyMeasurable[MeasureTheory.Filtration.piLE (n + 1)]
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j) := by
  let g : (Finset.Iic (n + 1) → M × Y) → ℝ := fun pref =>
    historyPrefixInformationInnovation q information n pref i j
  rw [historyPathInformationInnovation_eq_prefix_comp,
    MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  have hg : Measurable g := measurable_of_countable g
  simpa [g, Function.comp_def] using
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- A direct coordinate bound gives integrability under every finite path
law. -/
theorem historyPathInformationInnovation_integrable_of_bound
    {M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (mu : Measure (ℕ → M × Y)) [IsFiniteMeasure mu]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (C : ℝ)
    (hbound : ∀ history setting i j,
      ‖historyInformationInnovation q information history setting i j‖ ≤ C)
    (n : ℕ) (i j : D) :
    Integrable
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j) mu := by
  refine Integrable.of_bound
    ((historyPathInformationInnovation_stronglyMeasurable_succ
      q information n i j).mono
        (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE (n + 1))).aestronglyMeasurable
    C ?_
  exact ae_of_all mu fun omega =>
    hbound
      (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
      (omega (n + 1)).1 i j

/-- Scalar partial sums are adapted to the canonical product filtration. -/
theorem historyPathInformationPartialSum_stronglyAdapted
    {M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (i j : D) :
    StronglyAdapted MeasureTheory.Filtration.piLE
      (scalarMartingalePartialSum fun n omega =>
        historyPathInformationInnovation q information n omega i j) := by
  intro n
  unfold scalarMartingalePartialSum
  have hsum := Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
    (historyPathInformationInnovation_stronglyMeasurable_succ
      q information k i j).mono
        (MeasureTheory.Filtration.mono MeasureTheory.Filtration.piLE
          (Nat.succ_le_iff.2 (Finset.mem_range.1 hk)))
  have heq :
      (fun omega : ℕ → M × Y =>
        ∑ k ∈ Finset.range n,
          historyPathInformationInnovation q information k omega i j) =
      ∑ k ∈ Finset.range n, fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information k omega i j := by
    funext omega
    simp
  rw [heq]
  exact hsum

/-- Integrability of the increments gives integrability of every partial sum. -/
theorem historyPathInformationPartialSum_integrable
    {M Y D : Type*} [Fintype M]
    [MeasurableSpace M] [MeasurableSpace Y]
    (mu : Measure (ℕ → M × Y))
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (i j : D)
    (hintegrable : ∀ n, Integrable
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j) mu) :
    ∀ n, Integrable
      (scalarMartingalePartialSum (fun k omega =>
        historyPathInformationInnovation q information k omega i j) n) mu := by
  intro n
  induction n with
  | zero =>
      change Integrable (0 : (ℕ → M × Y) → ℝ) mu
      exact integrable_zero (ℕ → M × Y) ℝ mu
  | succ n ih =>
      rw [show scalarMartingalePartialSum
          (fun k omega => historyPathInformationInnovation q information k omega i j)
          (n + 1) =
          scalarMartingalePartialSum
              (fun k omega => historyPathInformationInnovation q information k omega i j) n +
            (fun omega => historyPathInformationInnovation q information n omega i j) by
        funext omega
        simp [scalarMartingalePartialSum, Finset.sum_range_succ]]
      exact ih.add (hintegrable n)

/-- Conditional centering under the actual Ionescu--Tulcea trajectory law. -/
theorem historyPathInformationInnovation_condExp_zero
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (i j : D)
    (hintegrable : Integrable
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j)
      (adaptiveTrajectoryMeasure q p theta)) :
    (adaptiveTrajectoryMeasure q p theta)[
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j) |
      MeasureTheory.Filtration.piLE n] =ᵐ[adaptiveTrajectoryMeasure q p theta] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu : Measure (ℕ → M × Y) := adaptiveTrajectoryMeasure q p theta
  let X : (ℕ → M × Y) → (Finset.Iic n → M × Y) :=
    Preorder.frestrictLe (π := fun _ : ℕ => M × Y) n
  let Ynext : (ℕ → M × Y) → M × Y := fun omega => omega (n + 1)
  let f : (Finset.Iic n → M × Y) × (M × Y) → ℝ := fun z =>
    historyInformationInnovation q information
      (trajectoryPrefixHistory z.1) z.2.1 i j
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hYnext : Measurable Ynext := measurable_pi_apply (n + 1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hf_int : Integrable (fun omega => f (X omega, Ynext omega)) mu := by
    simpa only [mu, X, Ynext, f, historyPathInformationInnovation] using hintegrable
  have hcondExp :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hX hYnext.aemeasurable hf hf_int
  have hcondPrefix :
      (fun pref =>
        ProbabilityTheory.condDistrib Ynext X mu pref) =ᵐ[Measure.map X mu]
      (fun pref => adaptiveTrajectoryKernel q p theta n pref) := by
    simpa only [mu, adaptiveTrajectoryMeasure, X, Ynext] using
      adaptiveTrajectory_condDistrib_next q p theta n
  have hcondPath :
      (fun omega => ProbabilityTheory.condDistrib Ynext X mu (X omega)) =ᵐ[mu]
      (fun omega => adaptiveTrajectoryKernel q p theta n (X omega)) := by
    refine (ae_map_iff hX.aemeasurable ?_).1 hcondPrefix
    exact Set.Finite.measurableSet (Set.toFinite _)
  have hzero :
      (fun omega =>
        ∫ y, f (X omega, y)
          ∂ ProbabilityTheory.condDistrib Ynext X mu (X omega)) =ᵐ[mu]
      0 := by
    filter_upwards [hcondPath] with omega homega
    rw [homega]
    exact integral_historyInformationInnovation_adaptiveTrajectoryKernel_zero
      q p theta information n (X omega) i j
  have hfinal := hcondExp.trans hzero
  change
    mu[(fun omega => f (X omega, Ynext omega)) |
      MeasurableSpace.comap X MeasurableSpace.pi] =ᵐ[mu] 0
  exact hfinal

/-- Coordinate partial sums form a martingale under the actual adaptive law. -/
theorem historyPathInformationPartialSum_martingale
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (i j : D)
    (hintegrable : ∀ n, Integrable
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j)
      (adaptiveTrajectoryMeasure q p theta)) :
    Martingale
      (scalarMartingalePartialSum fun n omega =>
        historyPathInformationInnovation q information n omega i j)
      MeasureTheory.Filtration.piLE (adaptiveTrajectoryMeasure q p theta) := by
  let mu : Measure (ℕ → M × Y) := adaptiveTrajectoryMeasure q p theta
  let increment : ℕ → (ℕ → M × Y) → ℝ := fun n omega =>
    historyPathInformationInnovation q information n omega i j
  let partialSum := scalarMartingalePartialSum increment
  have hadapted : StronglyAdapted MeasureTheory.Filtration.piLE partialSum := by
    simpa [partialSum, increment] using
      historyPathInformationPartialSum_stronglyAdapted q information i j
  have hintegrableSum : ∀ n, Integrable (partialSum n) mu := by
    simpa [partialSum, increment, mu] using
      historyPathInformationPartialSum_integrable
        (adaptiveTrajectoryMeasure q p theta) q information i j hintegrable
  refine martingale_nat hadapted hintegrableSum ?_
  intro n
  have hcenter :
      mu[increment n | MeasureTheory.Filtration.piLE n] =ᵐ[mu] 0 := by
    simpa [mu, increment] using
      historyPathInformationInnovation_condExp_zero
        q p theta information n i j (hintegrable n)
  have hself :
      mu[partialSum n | MeasureTheory.Filtration.piLE n] = partialSum n :=
    condExp_of_stronglyMeasurable
      (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE n)
      (hadapted n) (hintegrableSum n)
  have hadd := condExp_add (hintegrableSum n) (hintegrable n)
    (MeasureTheory.Filtration.piLE n)
  have hrec : (partialSum n + increment n) = partialSum (n + 1) := by
    funext omega
    simp [partialSum, increment, scalarMartingalePartialSum, Finset.sum_range_succ]
  calc
    partialSum n =ᵐ[mu] mu[partialSum n | MeasureTheory.Filtration.piLE n] :=
      ae_of_all mu (congrFun hself.symm)
    _ =ᵐ[mu]
        mu[partialSum n | MeasureTheory.Filtration.piLE n] +
          mu[increment n | MeasureTheory.Filtration.piLE n] := by
            filter_upwards [hcenter] with omega homega
            simp [homega]
    _ =ᵐ[mu]
        mu[partialSum n + increment n | MeasureTheory.Filtration.piLE n] :=
          hadd.symm
    _ =ᵐ[mu]
        mu[partialSum (n + 1) | MeasureTheory.Filtration.piLE n] :=
          condExp_congr_ae (ae_of_all mu (congrFun hrec))

/-- Exact Hall--Heyde endpoint for history-dependent adaptive information. -/
theorem historyInformationInnovation_strongLaw_adaptiveTrajectory_of_conditionalMoments
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [Fintype D] [DecidableEq D]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (hL2 : ∀ n i j, MemLp
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j)
      2 (adaptiveTrajectoryMeasure q p theta))
    (hsummable : ∀ i j, ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Summable (fun n => hallHeydeWeightedSecondMoment
        (adaptiveTrajectoryMeasure q p theta)
        MeasureTheory.Filtration.piLE
        (fun n omega => historyPathInformationInnovation q information n omega i j)
        n omega)) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            historyPathInformationInnovation q information k omega)
        atTop (nhds 0) := by
  apply finiteMatrix_martingale_strongLaw
    (adaptiveTrajectoryMeasure q p theta)
    MeasureTheory.Filtration.piLE
    (historyPathInformationInnovation q information)
  · intro i j
    exact historyPathInformationPartialSum_martingale
      q p theta information i j
      (fun n => (hL2 n i j).integrable (by norm_num))
  · exact fun i j n => hL2 n i j
  · exact hsummable

/-- Uniformly bounded history-dependent innovations satisfy the exact
Hall--Heyde conditional-moment premise automatically. -/
theorem historyInformationInnovation_strongLaw_adaptiveTrajectory_of_uniform_bound
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [Fintype D] [DecidableEq D]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ history setting i j,
      ‖historyInformationInnovation q information history setting i j‖ ≤ C) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            historyPathInformationInnovation q information k omega)
        atTop (nhds 0) := by
  rcases hbound with ⟨C, hC, hbound⟩
  have hintegrable : ∀ n i j, Integrable
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j)
      (adaptiveTrajectoryMeasure q p theta) := by
    intro n i j
    exact historyPathInformationInnovation_integrable_of_bound
      (adaptiveTrajectoryMeasure q p theta) q information C hbound n i j
  apply finiteMatrix_martingale_strongLaw_of_uniform_bound
    (adaptiveTrajectoryMeasure q p theta)
    MeasureTheory.Filtration.piLE
    (historyPathInformationInnovation q information)
  · intro i j
    exact historyPathInformationPartialSum_martingale
      q p theta information i j (fun n => hintegrable n i j)
  · exact ⟨C, hC, fun n omega i j =>
      hbound
        (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
        (omega (n + 1)).1 i j⟩

end QubitOracle.Paper
