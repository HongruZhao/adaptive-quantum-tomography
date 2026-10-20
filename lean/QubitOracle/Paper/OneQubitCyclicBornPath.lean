import QubitOracle.Paper.OneQubitCyclicPauliProtocol
import QubitOracle.Paper.AdaptiveTrajectoryExperiment

/-!
# Concrete Born path for the cyclic-Pauli controller

This module instantiates the abstract RLS probability premises on the existing
Ionescu--Tulcea infinite trajectory space.  The parameter space is the closed
Bloch ball, the response is the exact binary Born law, and the deterministic
design cycles through the three Pauli coordinate axes.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Physical one-qubit parameters, represented by their Bloch vectors. -/
abbrev OneQubitPhysicalParameter :=
  {theta : Fin 3 → ℝ // QubitOracle.blochNormSq theta ≤ 1}

theorem pauliCoordinateAxis_blochNormSq (slot : Fin 3) :
    QubitOracle.blochNormSq (pauliCoordinateAxis slot) = 1 := by
  fin_cases slot <;>
    norm_num [QubitOracle.blochNormSq, pauliCoordinateAxis, Fin.sum_univ_succ]

theorem oneQubitCyclicPauliAxis_blochNormSq (k : ℕ) :
    QubitOracle.blochNormSq (oneQubitCyclicPauliAxis k) = 1 := by
  unfold oneQubitCyclicPauliAxis
  exact pauliCoordinateAxis_blochNormSq _

theorem oneQubitCyclicBorn_dot_abs_le_one
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) :
    |QubitOracle.blochDot (pauliCoordinateAxis slot) theta| ≤ 1 := by
  have hAxis : QubitOracle.blochNormSq (pauliCoordinateAxis slot) ≤ 1 := by
    rw [pauliCoordinateAxis_blochNormSq]
  have hNorm : blochNorm theta ≤ 1 := by
    simpa [blochNorm] using (Real.sqrt_le_one.mpr hTheta)
  have hDot := abs_blochDot_le_blochNorm theta (pauliCoordinateAxis slot) hAxis
  have hDot' :
      |QubitOracle.blochDot (pauliCoordinateAxis slot) theta| ≤ blochNorm theta := by
    simpa [QubitOracle.blochDot, mul_comm] using hDot
  exact hDot'.trans hNorm

theorem oneQubitCyclicBornProbability_nonneg
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) (y : QubitRLSOutcome) :
    0 ≤ qubitRLSBornProbability theta (pauliCoordinateAxis slot) y := by
  have hAbs := oneQubitCyclicBorn_dot_abs_le_one theta hTheta slot
  rw [qubitRLSBornProbability, qubitBornTrace_eq]
  cases y with
  | false =>
      simp [qubitRLSOutcomeSign]
      linarith [le_of_abs_le hAbs]
  | true =>
      simp [qubitRLSOutcomeSign]
      linarith [neg_le_of_abs_le hAbs]

/-- Exact binary Born probability mass function for a Pauli coordinate axis. -/
def oneQubitCyclicBornPMF
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) : PMF QubitRLSOutcome :=
  PMF.ofFintype
    (fun y => ENNReal.ofReal
      (qubitRLSBornProbability theta (pauliCoordinateAxis slot) y))
    (by
      have hNonneg : ∀ y ∈ (Finset.univ : Finset QubitRLSOutcome),
          0 ≤ qubitRLSBornProbability theta (pauliCoordinateAxis slot) y :=
        fun y _ => oneQubitCyclicBornProbability_nonneg theta hTheta slot y
      calc
        (∑ y, ENNReal.ofReal
            (qubitRLSBornProbability theta (pauliCoordinateAxis slot) y)) =
            ENNReal.ofReal
              (∑ y, qubitRLSBornProbability theta (pauliCoordinateAxis slot) y) :=
          (ENNReal.ofReal_sum_of_nonneg hNonneg).symm
        _ = ENNReal.ofReal 1 := by
          rw [qubitRLSBornProbability_sum]
        _ = 1 := ENNReal.ofReal_one)

/-- Born measure associated with `oneQubitCyclicBornPMF`. -/
def oneQubitCyclicBornMeasure
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) : Measure QubitRLSOutcome :=
  (oneQubitCyclicBornPMF theta hTheta slot).toMeasure

instance oneQubitCyclicBornMeasure_isProbability
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) :
    IsProbabilityMeasure (oneQubitCyclicBornMeasure theta hTheta slot) := by
  unfold oneQubitCyclicBornMeasure
  infer_instance

/-- Markov response kernel carrying the exact Born law. -/
def oneQubitCyclicBornResponseKernel
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    ProbabilityTheory.Kernel (Fin 3) QubitRLSOutcome :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun slot => oneQubitCyclicBornMeasure theta hTheta slot)

instance oneQubitCyclicBornResponseKernel_isMarkov
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    ProbabilityTheory.IsMarkovKernel
      (oneQubitCyclicBornResponseKernel theta hTheta) := by
  refine ⟨?_⟩
  intro slot
  change IsProbabilityMeasure (oneQubitCyclicBornMeasure theta hTheta slot)
  infer_instance

/--
Protocol indexing uses coordinate zero for initialization.  Coordinate `k+1`
uses cyclic Pauli axis `k`, exactly matching `oneQubitRLSNoise`.
-/
def oneQubitCyclicProtocolSlot : ℕ → Fin 3
  | 0 => 0
  | k + 1 => ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩

@[simp]
theorem pauliCoordinateAxis_cyclicProtocolSlot_succ (k : ℕ) :
    pauliCoordinateAxis (oneQubitCyclicProtocolSlot (k + 1)) =
      oneQubitCyclicPauliAxis k := by
  rfl

/-- Predictable cyclic-Pauli protocol on the physical Bloch ball. -/
def oneQubitCyclicBornProtocol :
    PredictableAdaptiveProtocol OneQubitPhysicalParameter (Fin 3) QubitRLSOutcome :=
  { response := fun theta => oneQubitCyclicBornResponseKernel theta.1 theta.2
    response_isMarkov := fun theta =>
      oneQubitCyclicBornResponseKernel_isMarkov theta.1 theta.2
    design := fun n _history => oneQubitCyclicProtocolSlot n
    design_measurable := fun _ => measurable_const }

abbrev OneQubitCyclicBornPath := AdaptiveInfinitePath QubitRLSOutcome

/-- Infinite Born trajectory measure generated by the cyclic protocol. -/
def oneQubitCyclicBornPathMeasure
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    Measure OneQubitCyclicBornPath :=
  adaptiveInfiniteTrajectoryMeasure oneQubitCyclicBornProtocol ⟨theta, hTheta⟩

instance oneQubitCyclicBornPathMeasure_isProbability
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    IsProbabilityMeasure (oneQubitCyclicBornPathMeasure theta hTheta) := by
  unfold oneQubitCyclicBornPathMeasure
  exact adaptiveInfiniteTrajectoryMeasure_isProbability
    oneQubitCyclicBornProtocol ⟨theta, hTheta⟩

/-- Deterministic regressor process on the Born path. -/
def oneQubitCyclicBornAxis
    (k : ℕ) (_omega : OneQubitCyclicBornPath) : Fin 3 → ℝ :=
  oneQubitCyclicPauliAxis k

/-- Coordinate outcome process on the Born path. -/
def oneQubitCyclicBornOutcome
    (k : ℕ) (omega : OneQubitCyclicBornPath) : QubitRLSOutcome :=
  omega k

/-- Coordinate `k` is measurable for the finite-coordinate filtration at `k`. -/
theorem measurable_oneQubitCyclicBornOutcome_piLE (k : ℕ) :
    @Measurable OneQubitCyclicBornPath QubitRLSOutcome
      (MeasureTheory.Filtration.piLE k) Bool.instMeasurableSpace
      (oneQubitCyclicBornOutcome k) := by
  change @Measurable OneQubitCyclicBornPath QubitRLSOutcome
    (MeasureTheory.Filtration.piLE k) Bool.instMeasurableSpace
    (fun omega => omega k)
  let restrict : OneQubitCyclicBornPath →
      ((i : ↥(Set.Iic k)) → QubitRLSOutcome) := Preorder.restrictLe k
  have hRestrict :
      @Measurable OneQubitCyclicBornPath
        ((i : ↥(Set.Iic k)) → QubitRLSOutcome)
        (MeasureTheory.Filtration.piLE k) inferInstance restrict := by
    apply Measurable.of_comap_le
    rfl
  have hEval : Measurable
      (fun z : ((i : ↥(Set.Iic k)) → QubitRLSOutcome) =>
        z (⟨k, by simp⟩ : ↥(Set.Iic k))) :=
    measurable_pi_apply (⟨k, by simp⟩ : ↥(Set.Iic k))
  have hComp := hEval.comp hRestrict
  simpa [restrict, Function.comp_def,
    Preorder.restrictLe_apply] using hComp

theorem integral_qubitRLSScalarNoise_oneQubitCyclicBornMeasure_zero
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (slot : Fin 3) :
    ∫ y, qubitRLSScalarNoise theta (pauliCoordinateAxis slot) y
        ∂(oneQubitCyclicBornMeasure theta hTheta slot) = 0 := by
  have hIntegrable : Integrable
      (fun y => qubitRLSScalarNoise theta (pauliCoordinateAxis slot) y)
      (oneQubitCyclicBornMeasure theta hTheta slot) := Integrable.of_finite
  have hToReal : ∀ y : QubitRLSOutcome,
      (ENNReal.ofReal
        (qubitRLSBornProbability theta (pauliCoordinateAxis slot) y)).toReal =
        qubitRLSBornProbability theta (pauliCoordinateAxis slot) y :=
    fun y => ENNReal.toReal_ofReal
      (oneQubitCyclicBornProbability_nonneg theta hTheta slot y)
  rw [integral_fintype hIntegrable]
  simpa [oneQubitCyclicBornMeasure, oneQubitCyclicBornPMF,
    Measure.real, PMF.toMeasure_apply_singleton,
    hToReal] using
      qubitRLSScalarNoise_centered theta (pauliCoordinateAxis slot)

theorem oneQubitCyclicBornStepKernel_eq
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (k : ℕ)
    (pref : (i : ↥(Finset.Iic k)) →
      AdaptiveOutcomeProcess QubitRLSOutcome i.1) :
    adaptiveIonescuStepKernel oneQubitCyclicBornProtocol ⟨theta, hTheta⟩ k pref =
      oneQubitCyclicBornMeasure theta hTheta
        ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ := by
  rfl

theorem oneQubitCyclicBornNoise_integrable
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (k : ℕ) :
    Integrable
      (oneQubitRLSNoise theta oneQubitCyclicBornAxis
        oneQubitCyclicBornOutcome (k + 1))
      (oneQubitCyclicBornPathMeasure theta hTheta) := by
  have hMeas : Measurable
      (oneQubitRLSNoise theta oneQubitCyclicBornAxis
        oneQubitCyclicBornOutcome (k + 1)) := by
    change Measurable (fun omega : OneQubitCyclicBornPath =>
      qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k) (omega (k + 1)))
    exact (measurable_of_countable
      (qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k))).comp
        (measurable_pi_apply (k + 1))
  apply Integrable.of_bound hMeas.aestronglyMeasurable 2
  filter_upwards [] with omega
  rw [Real.norm_eq_abs]
  apply abs_qubitRLSScalarNoise_le_two
  change |QubitOracle.blochDot (oneQubitCyclicPauliAxis k) theta| ≤ 1
  simpa [oneQubitCyclicPauliAxis] using
    oneQubitCyclicBorn_dot_abs_le_one theta hTheta
      ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩

/--
The exact Born scalar noise at coordinate `k+1` has conditional expectation
zero given coordinates through `k`.
-/
theorem oneQubitCyclicBornNoise_condExp_zero
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (k : ℕ) :
    (oneQubitCyclicBornPathMeasure theta hTheta)[
        oneQubitRLSNoise theta oneQubitCyclicBornAxis
          oneQubitCyclicBornOutcome (k + 1) |
        (MeasureTheory.Filtration.piLE k :
          MeasurableSpace OneQubitCyclicBornPath)]
      =ᵐ[oneQubitCyclicBornPathMeasure theta hTheta] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu := oneQubitCyclicBornPathMeasure theta hTheta
  let X : OneQubitCyclicBornPath →
      ((i : ↥(Finset.Iic k)) → AdaptiveOutcomeProcess QubitRLSOutcome i.1) :=
    Preorder.frestrictLe k
  let Ynext := fun omega : OneQubitCyclicBornPath => omega (k + 1)
  let f := fun z :
      (((i : ↥(Finset.Iic k)) → AdaptiveOutcomeProcess QubitRLSOutcome i.1) ×
        QubitRLSOutcome) =>
    qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k) z.2
  have hX : Measurable X := by
    exact Preorder.measurable_frestrictLe k
  have hYnext : Measurable Ynext := measurable_pi_apply (k + 1)
  have hf : StronglyMeasurable f :=
    (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun omega => f (X omega, Ynext omega)) mu := by
    change Integrable
      (oneQubitRLSNoise theta oneQubitCyclicBornAxis
        oneQubitCyclicBornOutcome (k + 1))
      (oneQubitCyclicBornPathMeasure theta hTheta)
    exact oneQubitCyclicBornNoise_integrable theta hTheta k
  have hCondExp :=
    ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
      hX hYnext.aemeasurable hf hfInt
  have hCondPrefix :=
    adaptiveInfiniteTrajectory_conditionalStep
      oneQubitCyclicBornProtocol ⟨theta, hTheta⟩ k
  have hCondPath :=
    (MeasureTheory.ae_map_iff hX.aemeasurable
      (Set.Finite.measurableSet
        (Set.toFinite
          {pref |
            (ProbabilityTheory.condDistrib Ynext X mu) pref =
              adaptiveIonescuStepKernel oneQubitCyclicBornProtocol
                ⟨theta, hTheta⟩ k pref}))).mp hCondPrefix
  have hZero :
      (fun omega =>
        ∫ y, f (X omega, y)
          ∂(ProbabilityTheory.condDistrib Ynext X mu) (X omega))
        =ᵐ[mu] 0 := by
    filter_upwards [hCondPath] with omega homega
    rw [homega, oneQubitCyclicBornStepKernel_eq]
    simpa [f, oneQubitCyclicPauliAxis] using
      integral_qubitRLSScalarNoise_oneQubitCyclicBornMeasure_zero
        theta hTheta ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩
  have hFinal := hCondExp.trans hZero
  change (oneQubitCyclicBornPathMeasure theta hTheta)[
      (fun omega =>
        qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k) (omega (k + 1))) |
      MeasurableSpace.comap (Preorder.frestrictLe k) MeasurableSpace.pi]
    =ᵐ[oneQubitCyclicBornPathMeasure theta hTheta] 0
  simpa only [mu, X, Ynext, f] using hFinal

theorem oneQubitCyclicBornNoise_measurable
    (theta : Fin 3 → ℝ) (k : ℕ) :
    Measurable
      (oneQubitRLSNoise theta oneQubitCyclicBornAxis
        oneQubitCyclicBornOutcome k) := by
  cases k with
  | zero =>
      change Measurable (fun _ : OneQubitCyclicBornPath => (0 : ℝ))
      exact measurable_const
  | succ k =>
      change Measurable (fun omega : OneQubitCyclicBornPath =>
        qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k) (omega (k + 1)))
      exact (measurable_of_countable
        (qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k))).comp
          (measurable_pi_apply (k + 1))

theorem oneQubitCyclicBornNoise_adapted
    (theta : Fin 3 → ℝ) :
    Adapted MeasureTheory.Filtration.piLE
      (oneQubitRLSNoise theta oneQubitCyclicBornAxis
        oneQubitCyclicBornOutcome) := by
  intro n
  cases n with
  | zero =>
      change @Measurable OneQubitCyclicBornPath ℝ
        (MeasureTheory.Filtration.piLE 0) inferInstance
        (fun _ => (0 : ℝ))
      exact measurable_const
  | succ k =>
      change @Measurable OneQubitCyclicBornPath ℝ
        (MeasureTheory.Filtration.piLE (k + 1)) inferInstance
        (fun omega =>
          qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k)
            (oneQubitCyclicBornOutcome (k + 1) omega))
      exact (measurable_of_countable
        (qubitRLSScalarNoise theta (oneQubitCyclicPauliAxis k))).comp
          (measurable_oneQubitCyclicBornOutcome_piLE (k + 1))

/--
All APS/RLS probability premises for the explicit cyclic-Pauli Born protocol.
-/
def oneQubitCyclicBornReducedProbabilityPremises
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    BinaryQubitRLSReducedProbabilityPremises OneQubitCyclicBornPath
      (oneQubitCyclicBornPathMeasure theta hTheta) theta
      oneQubitCyclicBornAxis oneQubitCyclicBornOutcome :=
  { filtration := MeasureTheory.Filtration.piLE
    axisAdapted := fun _ => measurable_const
    noiseAdapted := oneQubitCyclicBornNoise_adapted theta
    noiseMeasurable := oneQubitCyclicBornNoise_measurable theta
    martingaleDifference := oneQubitCyclicBornNoise_condExp_zero theta hTheta
    physicalAxis := fun k _ => by
      rw [oneQubitCyclicBornAxis, oneQubitCyclicPauliAxis_blochNormSq] }

/--
Fully instantiated non-LAN RLS convergence for every physical one-qubit Bloch
vector under the exact cyclic-Pauli Born experiment.
-/
theorem oneQubitCyclicBornControllerConvergence
    (theta : Fin 3 → ℝ) (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    AlmostSureControllerRate (oneQubitCyclicBornPathMeasure theta hTheta)
        (oneQubitAPSRidgeController
          (oneQubitCyclicBornReducedProbabilityPremises theta hTheta) hTheta 1)
        theta oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂(oneQubitCyclicBornPathMeasure theta hTheta),
        Filter.Tendsto
          (fun n => oneQubitAPSRidgeController
            (oneQubitCyclicBornReducedProbabilityPremises theta hTheta)
            hTheta 1 n omega)
          Filter.atTop (nhds theta)) ∧
      TendstoInMeasure (oneQubitCyclicBornPathMeasure theta hTheta)
        (scaledControllerNormError
          (oneQubitAPSRidgeController
            (oneQubitCyclicBornReducedProbabilityPremises theta hTheta) hTheta 1)
          theta)
        Filter.atTop (fun _ => 0) := by
  exact oneQubitCyclicPauliControllerConvergence
    (oneQubitCyclicBornReducedProbabilityPremises theta hTheta) hTheta
    (fun _ _ => rfl)

end

end QubitOracle.Paper
