import QubitOracle.Paper.FiniteKernelPathSpace
import QubitOracle.Paper.MixedInformationMartingale
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Martingale.Basic

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

/-- The mixed-information innovation has exactly zero mean under the one-step
adaptive joint setting/outcome kernel.  This is a finite algebraic identity;
it does not use a limit theorem. -/
theorem integral_mixedInformationInnovation_adaptiveJointKernel_zero
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (history : SequentialHistory M Y) (i j : Fin 3) :
    ∫ z, mixedInformationInnovation q r axis history z.1 i j
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass history)
          ((adaptiveJointKernel q p theta).mass_nonneg history)
          ((adaptiveJointKernel q p theta).sum_mass history) = 0 := by
  rw [integral_finiteMassMeasure, Fintype.sum_prod_type]
  change
    (∑ m : M, ∑ y : Y,
      (q.mass history m * p.mass (theta, m) y) *
        mixedInformationInnovation q r axis history m i j) = 0
  calc
    (∑ m : M, ∑ y : Y,
        (q.mass history m * p.mass (theta, m) y) *
          mixedInformationInnovation q r axis history m i j) =
        ∑ m : M,
          (q.mass history m * mixedInformationInnovation q r axis history m i j) *
            (∑ y : Y, p.mass (theta, m) y) := by
              apply Finset.sum_congr rfl
              intro m _
              calc
                (∑ y : Y,
                    (q.mass history m * p.mass (theta, m) y) *
                      mixedInformationInnovation q r axis history m i j) =
                    ∑ y : Y,
                      (q.mass history m *
                          mixedInformationInnovation q r axis history m i j) *
                        p.mass (theta, m) y := by
                          apply Finset.sum_congr rfl
                          intro y _
                          ring
                _ =
                    (q.mass history m *
                        mixedInformationInnovation q r axis history m i j) *
                      (∑ y : Y, p.mass (theta, m) y) := by
                        rw [Finset.mul_sum]
    _ = ∑ m : M, q.mass history m *
          mixedInformationInnovation q r axis history m i j := by
            apply Finset.sum_congr rfl
            intro m _
            rw [p.sum_mass]
            ring
    _ = 0 := by
      simp only [mixedInformationInnovation, mixedPolicyMeanInformation,
        finitePolicyExpectation, Matrix.sub_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, q.sum_mass]
      ring

/-- The same centering identity, expressed directly for the trajectory kernel
used by the Ionescu--Tulcea path-space construction. -/
theorem integral_mixedInformationInnovation_adaptiveTrajectoryKernel_zero
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (n : ℕ) (pref : Finset.Iic n → M × Y) (i j : Fin 3) :
    ∫ z,
        mixedInformationInnovation q r axis (trajectoryPrefixHistory pref) z.1 i j
      ∂ (adaptiveTrajectoryKernel q p theta n) pref = 0 := by
  change
    ∫ z,
        mixedInformationInnovation q r axis (trajectoryPrefixHistory pref) z.1 i j
      ∂ finiteMassMeasure
          ((adaptiveJointKernel q p theta).mass (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel q p theta).mass_nonneg (trajectoryPrefixHistory pref))
          ((adaptiveJointKernel q p theta).sum_mass (trajectoryPrefixHistory pref)) = 0
  exact integral_mixedInformationInnovation_adaptiveJointKernel_zero
    q p theta r axis (trajectoryPrefixHistory pref) i j

/-- The information innovation at shot `n + 1`, after observing the trajectory
prefix through shot `n`.  Starting at the second shot aligns the increment with
the canonical product filtration; omitting the first bounded shot has no effect
on normalized asymptotics. -/
def mixedPathInformationInnovation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (n : ℕ) (omega : ℕ → M × Y) : OracleMatrix :=
  mixedInformationInnovation q r axis
    (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
    (omega (n + 1)).1

private def mixedPrefixInformationInnovation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (n : ℕ) (pref : Finset.Iic (n + 1) → M × Y) : OracleMatrix :=
  mixedInformationInnovation q r axis
    (trajectoryPrefixHistory
      (fun k : Finset.Iic n =>
        pref ⟨k.1, Finset.mem_Iic.mpr
          ((Finset.mem_Iic.mp k.2).trans (Nat.le_succ n))⟩))
    (pref ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩).1

private theorem mixedPathInformationInnovation_eq_prefix_comp
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (n : ℕ) :
    mixedPathInformationInnovation q r axis n =
      mixedPrefixInformationInnovation q r axis n ∘
        Preorder.frestrictLe (n + 1) := by
  funext omega
  unfold mixedPathInformationInnovation mixedPrefixInformationInnovation
  apply congrArg (fun h =>
    mixedInformationInnovation q r axis h (omega (n + 1)).1)
  apply congrArg trajectoryPrefixHistory
  funext k
  rfl

/-- Each scalar coordinate of the next-shot innovation is measurable at time
`n + 1` in the canonical product filtration. -/
theorem mixedPathInformationInnovation_stronglyMeasurable_succ
    {M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (n : ℕ) (i j : Fin 3) :
    StronglyMeasurable[MeasureTheory.Filtration.piLE (n + 1)]
      (fun omega : ℕ → M × Y =>
        mixedPathInformationInnovation q r axis n omega i j) := by
  let g : (Finset.Iic (n + 1) → M × Y) → ℝ := fun pref =>
    mixedPrefixInformationInnovation q r axis n pref i j
  rw [mixedPathInformationInnovation_eq_prefix_comp,
    MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  have hg : Measurable g := measurable_of_countable g
  simpa [g, Function.comp_def] using
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Uniform boundedness of an interior-state innovation makes every scalar
coordinate integrable under any finite trajectory law. -/
theorem mixedPathInformationInnovation_integrable
    {M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (mu : Measure (ℕ → M × Y)) [IsFiniteMeasure mu]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (n : ℕ) (i j : Fin 3) :
    Integrable
      (fun omega : ℕ → M × Y =>
        mixedPathInformationInnovation q r axis n omega i j) mu := by
  refine Integrable.of_bound
    ((mixedPathInformationInnovation_stronglyMeasurable_succ
      q r axis n i j).mono
        (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE (n + 1))).aestronglyMeasurable
    (2 * (1 - QubitOracle.blochNormSq r)⁻¹) ?_
  exact ae_of_all mu fun omega =>
    mixedInformationInnovation_entry_norm_le q r axis
      (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
      (omega (n + 1)).1 hr haxis i j

/-- The scalar partial-sum process is adapted to the canonical product
filtration. -/
theorem mixedPathInformationPartialSum_stronglyAdapted
    {M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (i j : Fin 3) :
    StronglyAdapted MeasureTheory.Filtration.piLE
      (scalarMartingalePartialSum fun n omega =>
        mixedPathInformationInnovation q r axis n omega i j) := by
  intro n
  unfold scalarMartingalePartialSum
  have hsum := Finset.stronglyMeasurable_sum (Finset.range n) fun k hk =>
    (mixedPathInformationInnovation_stronglyMeasurable_succ
      q r axis k i j).mono
        (MeasureTheory.Filtration.mono MeasureTheory.Filtration.piLE
          (Nat.succ_le_iff.2 (Finset.mem_range.1 hk)))
  have heq :
      (fun omega : ℕ → M × Y =>
        ∑ k ∈ Finset.range n,
          mixedPathInformationInnovation q r axis k omega i j) =
      ∑ k ∈ Finset.range n, fun omega : ℕ → M × Y =>
        mixedPathInformationInnovation q r axis k omega i j := by
    funext omega
    simp
  rw [heq]
  exact hsum

/-- The scalar partial sums are integrable under any finite trajectory law. -/
theorem mixedPathInformationPartialSum_integrable
    {M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (mu : Measure (ℕ → M × Y)) [IsFiniteMeasure mu]
    (q : AdaptivePolicy M Y) (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (i j : Fin 3) :
    ∀ n, Integrable
      (scalarMartingalePartialSum (fun k omega =>
        mixedPathInformationInnovation q r axis k omega i j) n) mu := by
  intro n
  induction n with
  | zero =>
      change Integrable (0 : (ℕ → M × Y) → ℝ) mu
      exact integrable_zero (ℕ → M × Y) ℝ mu
  | succ n ih =>
      rw [show scalarMartingalePartialSum
          (fun k omega => mixedPathInformationInnovation q r axis k omega i j)
          (n + 1) =
          scalarMartingalePartialSum
              (fun k omega => mixedPathInformationInnovation q r axis k omega i j) n +
            (fun omega => mixedPathInformationInnovation q r axis n omega i j) by
        funext omega
        simp [scalarMartingalePartialSum, Finset.sum_range_succ]]
      exact ih.add (mixedPathInformationInnovation_integrable
        mu q r axis hr haxis n i j)

/-- The next coordinate's conditional law under the adaptive trajectory is
the one-step adaptive kernel.  Supplying the constant trajectory type family
explicitly keeps the dependent Ionescu--Tulcea indices transparent to Lean. -/
theorem adaptiveTrajectory_condDistrib_next
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (n : ℕ) :
    ⇑(ProbabilityTheory.condDistrib
      (fun omega : ℕ → M × Y => omega (n + 1))
      (Preorder.frestrictLe (π := fun _ : ℕ => M × Y) n)
      (ProbabilityTheory.Kernel.trajMeasure
        (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta))) =ᵐ[
      Measure.map (Preorder.frestrictLe (π := fun _ : ℕ => M × Y) n)
        (ProbabilityTheory.Kernel.trajMeasure
          (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta))]
    ⇑(adaptiveTrajectoryKernel q p theta n) :=
  ProbabilityTheory.Kernel.condDistrib_trajMeasure
    (X := fun _ : ℕ => M × Y)
    (κ := adaptiveTrajectoryKernel q p theta)
    (μ₀ := adaptiveInitialMeasure q p theta) (a := n)

/-- Under the Ionescu--Tulcea trajectory law, the next-shot information
innovation has conditional expectation zero given the observed prefix. -/
theorem mixedPathInformationInnovation_condExp_zero
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (n : ℕ) (i j : Fin 3) :
    (ProbabilityTheory.Kernel.trajMeasure
      (adaptiveInitialMeasure q p theta)
      (adaptiveTrajectoryKernel q p theta))[
        (fun omega : ℕ → M × Y =>
          mixedPathInformationInnovation q r axis n omega i j) |
        MeasureTheory.Filtration.piLE n] =ᵐ[
          ProbabilityTheory.Kernel.trajMeasure
            (adaptiveInitialMeasure q p theta)
            (adaptiveTrajectoryKernel q p theta)]
      0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu : Measure (ℕ → M × Y) := ProbabilityTheory.Kernel.trajMeasure
    (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta)
  let X : (ℕ → M × Y) → (Finset.Iic n → M × Y) :=
    Preorder.frestrictLe (π := fun _ : ℕ => M × Y) n
  let Ynext : (ℕ → M × Y) → M × Y := fun omega => omega (n + 1)
  let f : (Finset.Iic n → M × Y) × (M × Y) → ℝ := fun z =>
    mixedInformationInnovation q r axis (trajectoryPrefixHistory z.1) z.2.1 i j
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hYnext : Measurable Ynext := measurable_pi_apply (n + 1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hf_int : Integrable (fun omega => f (X omega, Ynext omega)) mu := by
    refine Integrable.of_bound
      (((measurable_of_countable f).comp (hX.prodMk hYnext)).aestronglyMeasurable)
      (2 * (1 - QubitOracle.blochNormSq r)⁻¹) ?_
    exact ae_of_all mu fun omega =>
      mixedInformationInnovation_entry_norm_le q r axis
        (trajectoryPrefixHistory (X omega)) (Ynext omega).1 hr haxis i j
  have hcondExp :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hX hYnext.aemeasurable hf hf_int
  have hcondPrefix :
      (fun pref =>
        ProbabilityTheory.condDistrib Ynext X mu pref) =ᵐ[Measure.map X mu]
      (fun pref => adaptiveTrajectoryKernel q p theta n pref) := by
    simpa only [mu, X, Ynext] using
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
    exact integral_mixedInformationInnovation_adaptiveTrajectoryKernel_zero
      q p theta r axis n (X omega) i j
  have hfinal := hcondExp.trans hzero
  change
    mu[(fun omega => f (X omega, Ynext omega)) |
      MeasurableSpace.comap X MeasurableSpace.pi] =ᵐ[mu] 0
  exact hfinal

/-- Each coordinate partial sum of the adaptive information innovation is a
martingale under the actual trajectory law. -/
theorem mixedPathInformationPartialSum_martingale
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (i j : Fin 3) :
    Martingale
      (scalarMartingalePartialSum fun n omega =>
        mixedPathInformationInnovation q r axis n omega i j)
      MeasureTheory.Filtration.piLE
      (ProbabilityTheory.Kernel.trajMeasure
        (adaptiveInitialMeasure q p theta)
        (adaptiveTrajectoryKernel q p theta)) := by
  let mu : Measure (ℕ → M × Y) := ProbabilityTheory.Kernel.trajMeasure
    (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta)
  let increment : ℕ → (ℕ → M × Y) → ℝ := fun n omega =>
    mixedPathInformationInnovation q r axis n omega i j
  let partialSum := scalarMartingalePartialSum increment
  have hadapted : StronglyAdapted MeasureTheory.Filtration.piLE partialSum := by
    simpa [partialSum, increment] using
      mixedPathInformationPartialSum_stronglyAdapted q r axis i j
  have hintegrable : ∀ n, Integrable (partialSum n) mu := by
    simpa [partialSum, increment, mu] using
      mixedPathInformationPartialSum_integrable
        (ProbabilityTheory.Kernel.trajMeasure
          (adaptiveInitialMeasure q p theta)
          (adaptiveTrajectoryKernel q p theta)) q r axis hr haxis i j
  refine martingale_nat hadapted hintegrable ?_
  intro n
  have hcenter :
      mu[increment n | MeasureTheory.Filtration.piLE n] =ᵐ[mu] 0 := by
    simpa [mu, increment] using
      mixedPathInformationInnovation_condExp_zero
        q p theta r axis hr haxis n i j
  have hself :
      mu[partialSum n | MeasureTheory.Filtration.piLE n] = partialSum n :=
    condExp_of_stronglyMeasurable
      (MeasureTheory.Filtration.le MeasureTheory.Filtration.piLE n)
      (hadapted n) (hintegrable n)
  have hadd := condExp_add (hintegrable n)
    (mixedPathInformationInnovation_integrable
      mu q r axis hr haxis n i j)
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

/- Actual path-space information SLLN for arbitrary adaptive finite
projective designs.  Unlike the generic wrapper, this theorem has no assumed
martingale premise: conditional centering is derived from the experiment law. -/
set_option maxHeartbeats 1000000 in
theorem mixedInformationInnovation_strongLaw_adaptiveTrajectory
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1) :
    ∀ᵐ omega : ℕ → M × Y ∂ ProbabilityTheory.Kernel.trajMeasure
        (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta),
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ •
            ∑ k ∈ Finset.range n,
              mixedInformationInnovation q r axis
                (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
                (omega (k + 1)).1)
        atTop (nhds 0) := by
  have hmartingale :
      ∀ i j : Fin 3,
        Martingale
          (scalarMartingalePartialSum fun (n : ℕ) (omega : ℕ → M × Y) =>
            mixedInformationInnovation q r axis
              (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
              (omega (n + 1)).1 i j)
          MeasureTheory.Filtration.piLE
          (ProbabilityTheory.Kernel.trajMeasure
            (adaptiveInitialMeasure q p theta)
            (adaptiveTrajectoryKernel q p theta)) := by
    intro i j
    simpa only [mixedPathInformationInnovation] using
      mixedPathInformationPartialSum_martingale
        q p theta r axis hr haxis i j
  exact mixedInformationInnovation_strongLaw
    (Omega := ℕ → M × Y) (M := M) (Y := Y)
    (mu := ProbabilityTheory.Kernel.trajMeasure
      (adaptiveInitialMeasure q p theta) (adaptiveTrajectoryKernel q p theta))
    (filtration := MeasureTheory.Filtration.piLE)
    (q := q) (r := r) (axis := axis)
    (history := fun n omega =>
      trajectoryPrefixHistory (Preorder.frestrictLe n omega))
    (setting := fun n omega => (omega (n + 1)).1)
    (hr := hr) (haxis := haxis) (hmartingale := hmartingale)

/-- Named-measure form of the actual adaptive path-space information SLLN. -/
theorem mixedInformationInnovation_strongLaw_adaptiveTrajectoryMeasure
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1) :
    ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ •
            ∑ k ∈ Finset.range n,
              mixedInformationInnovation q r axis
                (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
                (omega (k + 1)).1)
        atTop (nhds 0) := by
  exact mixedInformationInnovation_strongLaw_adaptiveTrajectory
    q p theta r axis hr haxis

end QubitOracle.Paper
