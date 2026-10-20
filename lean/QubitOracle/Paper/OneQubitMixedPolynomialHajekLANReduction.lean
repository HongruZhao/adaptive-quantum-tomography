import QubitOracle.Paper.OneQubitMixedPolynomialWhitenedScoreCLT
import QubitOracle.Paper.OneQubitMixedUniformLocalRiskCore

/-!
# Concrete Hajek LAN reduction for the polynomial mixed-qubit protocol

This file packages the exact finite two-stage Born rows as one
`HajekExperimentSequence`.  A global physical fallback makes every law a
probability measure, while every fixed root-information local alternative is
proved eventually to use the genuine interior Born law.

All LAN fields except the finite discrete Radon--Nikodym identity are
constructed here.  That identity is exposed as a named proposition, not an
axiom, so it remains a computational Lean obligation.
-/

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology

namespace QubitOracle.Paper

noncomputable section

attribute [local instance]
  mixedPolynomialTotalScaleRowMeasurableSpace
  mixedPolynomialTotalScaleRowMeasurableSingletonClass

/-- Candidate physical Bloch parameter corresponding to the local Hajek
coordinate `eta` in row `n`. -/
def mixedPolynomialHajekPhysicalCandidate
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (eta : HajekParameter (Fin 3)) : Fin 3 → ℝ :=
  if n = 0 then theta else
    fun i => theta i +
      mixedLocalScale mixedPolynomialTotalScaleObservations n *
        mixedPolynomialTruthFrameWhiteningDirection theta b
          (fun j => Real.sqrt (n : ℝ) * eta j) i

/-- Global probability-law extension: outside the physical Bloch ball use the
truth law.  This branch is never used by a fixed local alternative for all
large rows. -/
noncomputable def mixedPolynomialHajekSafePhysicalParameter
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (eta : HajekParameter (Fin 3)) : Fin 3 → ℝ := by
  classical
  exact if PauliPilotPhysicalBloch
    (mixedPolynomialHajekPhysicalCandidate theta b n eta)
    then mixedPolynomialHajekPhysicalCandidate theta b n eta
    else theta

theorem mixedPolynomialHajekPhysicalCandidate_zero
    (theta b : Fin 3 → ℝ) (n : ℕ) :
    mixedPolynomialHajekPhysicalCandidate theta b n 0 = theta := by
  by_cases hn : n = 0
  · simp [mixedPolynomialHajekPhysicalCandidate, hn]
  · rw [mixedPolynomialHajekPhysicalCandidate, if_neg hn]
    funext i
    have hzero : (fun j : Fin 3 => Real.sqrt (n : ℝ) * (0 : Fin 3 → ℝ) j) = 0 := by
      funext j
      simp
    rw [hzero, mixedPolynomialTruthFrameWhiteningDirection_zero]
    simp

theorem mixedPolynomialHajekSafePhysicalParameter_physical
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (n : ℕ) (eta : HajekParameter (Fin 3)) :
    PauliPilotPhysicalBloch
      (mixedPolynomialHajekSafePhysicalParameter theta b n eta) := by
  unfold mixedPolynomialHajekSafePhysicalParameter
  by_cases hphysical : PauliPilotPhysicalBloch
      (mixedPolynomialHajekPhysicalCandidate theta b n eta)
  · rw [if_pos hphysical]
    exact hphysical
  · rw [if_neg hphysical]
    exact mixedNonzeroInterior_pauliPilotPhysical theta hTruth

theorem mixedPolynomialHajekSafePhysicalParameter_zero
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (n : ℕ) :
    mixedPolynomialHajekSafePhysicalParameter theta b n 0 = theta := by
  rw [mixedPolynomialHajekSafePhysicalParameter,
    mixedPolynomialHajekPhysicalCandidate_zero theta b n]
  simp [mixedNonzeroInterior_pauliPilotPhysical theta hTruth]

/-- The exact finite-row experiment in local whitened coordinates. -/
noncomputable def mixedPolynomialHajekExperiment
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    HajekExperimentSequence (Fin 3) where
  Sample n := MixedPolynomialTotalScaleRow n
  measurableSpace n := mixedPolynomialTotalScaleRowMeasurableSpace n
  parameterSet := Set.univ
  law n eta :=
    mixedPolynomialTotalScaleRowMeasure
      (mixedPolynomialHajekSafePhysicalParameter theta b n eta) b n
  probabilityMeasure n eta := by
    refine ⟨?_⟩
    unfold mixedPolynomialTotalScaleRowMeasure
    exact mixedTwoStageFiniteBornMeasure_univ
      (mixedPolynomialHajekSafePhysicalParameter theta b n eta)
      (mixedPolynomialTotalScaleSelectedFrame b n)
      (mixedPolynomialHajekSafePhysicalParameter_physical
        theta b hTruth n eta)

/-- The base law of the local experiment is exactly the original truth Born
row, with no fallback branch. -/
theorem mixedPolynomialHajekExperiment_baseLaw
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (n : ℕ) :
    (mixedPolynomialHajekExperiment theta b hTruth).law n 0 =
      mixedPolynomialTotalScaleRowMeasure theta b n := by
  change mixedPolynomialTotalScaleRowMeasure
      (mixedPolynomialHajekSafePhysicalParameter theta b n 0) b n =
    mixedPolynomialTotalScaleRowMeasure theta b n
  rw [mixedPolynomialHajekSafePhysicalParameter_zero theta b hTruth n]

/-- For positive row index, Hajek's `h / sqrt n` coordinate is exactly the
paper's physical `A h / sqrt(N_n)` local alternative. -/
theorem mixedPolynomialHajekPhysicalCandidate_localParameter
    (theta b h : Fin 3 → ℝ) (n : ℕ) (hn : n ≠ 0) :
      mixedPolynomialHajekPhysicalCandidate theta b n
        (hajekLocalParameter 0 h n) =
      mixedLocalAlternative theta mixedPolynomialTotalScaleObservations n
        (mixedPolynomialTruthFrameWhiteningDirection theta b h) := by
  rw [mixedPolynomialHajekPhysicalCandidate, if_neg hn]
  unfold hajekLocalParameter mixedLocalAlternative
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnpos)
  have hscaled :
      (fun j : Fin 3 =>
        Real.sqrt (n : ℝ) *
          ((0 : Fin 3 → ℝ) j + (Real.sqrt (n : ℝ))⁻¹ * h j)) = h := by
    funext j
    simp only [Pi.zero_apply, zero_add]
    field_simp [hsqrt]
  rw [hscaled]

/-- Every fixed local direction eventually uses the genuine physical
alternative rather than the global fallback. -/
theorem mixedPolynomialHajekSafePhysicalParameter_eventually_local
    (theta b h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ n : ℕ in atTop,
      mixedPolynomialHajekSafePhysicalParameter theta b n
          (hajekLocalParameter 0 h n) =
        mixedLocalAlternative theta mixedPolynomialTotalScaleObservations n
          (mixedPolynomialTruthFrameWhiteningDirection theta b h) := by
  let ah :=
    mixedPolynomialTruthFrameWhiteningDirection theta b h
  let H : ℝ := blochNormSq ah + 1
  have hnorm : 0 ≤ blochNormSq ah := by
    unfold blochNormSq
    positivity
  have hball : MixedLocalDirectionBall H ah := by
    unfold MixedLocalDirectionBall H
    nlinarith [sq_nonneg (blochNormSq ah)]
  have hscale :
      Tendsto (mixedLocalScale mixedPolynomialTotalScaleObservations)
        atTop (nhds 0) := by
    change Tendsto
      (fun n : ℕ =>
        (Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ))⁻¹)
      atTop (nhds 0)
    apply Tendsto.squeeze tendsto_const_nhds
      mixedPolynomial_invSqrtLANScale_tendsto_zero
    · intro n
      positivity
    · intro n
      have hcountNat :
          mixedPolynomialPilotLANScale n ≤
            mixedPolynomialTotalScaleObservations n := by
        simp [mixedPolynomialPilotLANScale,
          mixedPolynomialScheduleM,
          mixedPolynomialTotalScaleObservations,
          mixedPolynomialTotalScalePilotObservations,
          mixedPolynomialTotalScalePilotBlocks,
          mixedPolynomialTotalScaleFinalObservations,
          mixedPolynomialTotalScaleFinalCycles]
      have hcount :
          (mixedPolynomialPilotLANScale n : ℝ) ≤
            (mixedPolynomialTotalScaleObservations n : ℝ) := by
        exact_mod_cast hcountNat
      exact inv_anti₀
        (Real.sqrt_pos.2 (by
          exact_mod_cast mixedPolynomialPilotLANScale_pos n))
        (Real.sqrt_le_sqrt hcount)
  have hinterior :=
    mixedLocalAlternative_eventually_uniform_interior
      theta mixedPolynomialTotalScaleObservations H hTruth.2 hscale
  filter_upwards [hinterior,
    eventually_atTop.2 ⟨1, fun n hn => Nat.ne_of_gt hn⟩] with n hnInterior hn
  have hcandidate :=
    mixedPolynomialHajekPhysicalCandidate_localParameter
      theta b h n hn
  have hphysical : PauliPilotPhysicalBloch
      (mixedLocalAlternative theta mixedPolynomialTotalScaleObservations n ah) := by
    exact le_of_lt (hnInterior ah hball)
  unfold mixedPolynomialHajekSafePhysicalParameter
  rw [hcandidate, if_pos hphysical]

/-- Consequently, every fixed local experiment law is eventually the exact
Born row at the paper's local alternative. -/
theorem mixedPolynomialHajekExperiment_eventually_localLaw
    (theta b h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ n : ℕ in atTop,
      (mixedPolynomialHajekExperiment theta b hTruth).law n
          (hajekLocalParameter 0 h n) =
        mixedPolynomialTotalScaleRowMeasure
          (mixedLocalAlternative theta mixedPolynomialTotalScaleObservations n
            (mixedPolynomialTruthFrameWhiteningDirection theta b h))
          b n := by
  filter_upwards
    [mixedPolynomialHajekSafePhysicalParameter_eventually_local
      theta b h hTruth] with n hn
  change mixedPolynomialTotalScaleRowMeasure
      (mixedPolynomialHajekSafePhysicalParameter theta b n
        (hajekLocalParameter 0 h n)) b n = _
  rw [hn]

/-- Frozen-coordinate score used in the concrete Hajek record. -/
def mixedPolynomialHajekScore
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : HajekParameter (Fin 3) :=
  mixedPolynomialRowWhitenedVectorScore theta b n row

/-- Concrete LAN remainder in one frozen local direction. -/
def mixedPolynomialHajekRemainder
    (theta b : Fin 3 → ℝ) (n : ℕ)
    (h : HajekParameter (Fin 3))
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedPolynomialTotalScaleResidual theta
    (mixedPolynomialTruthFrameWhiteningDirection theta b h) b n row

theorem mixedPolynomialHajekScore_measurable
    (theta b : Fin 3 → ℝ) (n : ℕ) (i : Fin 3) :
    letI : MeasurableSpace (MixedPolynomialTotalScaleRow n) :=
      mixedPolynomialTotalScaleRowMeasurableSpace n
    Measurable (fun row => mixedPolynomialHajekScore theta b n row i) :=
  measurable_of_finite _

theorem mixedPolynomialHajekRemainder_measurable
    (theta b : Fin 3 → ℝ) (n : ℕ) (h : HajekParameter (Fin 3)) :
    letI : MeasurableSpace (MixedPolynomialTotalScaleRow n) :=
      mixedPolynomialTotalScaleRowMeasurableSpace n
    Measurable (mixedPolynomialHajekRemainder theta b n h) :=
  measurable_of_finite _

/-- The exact frozen score satisfies Hajek's characteristic-function Gaussian
convergence condition. -/
theorem mixedPolynomialHajekScore_converges
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    HajekScoreConvergesToGaussian
      (mixedPolynomialHajekExperiment theta b hTruth) 0
      mixedFrozenOracleInformation
      (mixedPolynomialHajekScore theta b) := by
  intro z
  have hlaw :=
    mixedPolynomialRowWhitenedVectorScoreLaw_tendsto_gaussian
      b theta hTruth hSeed hHoeffding
  have hz :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hlaw)
      (WithLp.toLp 2 z)
  have htarget :
      charFun (mixedFrozenOracleGaussianLaw :
          Measure (EuclideanSpace ℝ (Fin 3)))
          (WithLp.toLp 2 z) =
        Complex.exp
          (-((hajekQuadraticForm
            mixedFrozenOracleInformation z : ℝ) : ℂ) / 2) := by
    change charFun (multivariateGaussian 0 mixedFrozenOracleInformation)
        (WithLp.toLp 2 z) = _
    rw [charFun_multivariateGaussian
      mixedFrozenOracleInformation_posDef.posSemidef]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    congr 1
    simp [hajekQuadraticForm, PiLp.inner_apply, dotProduct]
    ring
  rw [htarget] at hz
  have hsource :
      (fun n : ℕ =>
        charFun
          (mixedPolynomialRowWhitenedVectorScoreLaw
            b theta hTruth hSeed n :
            Measure (EuclideanSpace ℝ (Fin 3)))
          (WithLp.toLp 2 z)) =
        (fun n : ℕ =>
          letI : MeasurableSpace
              ((mixedPolynomialHajekExperiment theta b hTruth).Sample n) :=
            (mixedPolynomialHajekExperiment theta b hTruth).measurableSpace n
          integral
            ((mixedPolynomialHajekExperiment theta b hTruth).law n 0)
            (fun row => Complex.exp
              (Complex.I * Complex.ofReal
                (dotProduct z
                  (mixedPolynomialHajekScore theta b n row))))) := by
    funext n
    rw [mixedPolynomialHajekExperiment_baseLaw]
    change
      (∫ x, Complex.exp
          (⟪x, WithLp.toLp 2 z⟫ * Complex.I)
        ∂((mixedPolynomialTotalScaleRowMeasure theta b n).map
          (fun row => WithLp.toLp 2
            (mixedPolynomialRowWhitenedVectorScore theta b n row)))) = _
    rw [MeasureTheory.integral_map
      (measurable_of_finite _).aemeasurable (by fun_prop)]
    apply integral_congr_ae
    filter_upwards with row
    simp [mixedPolynomialHajekScore, PiLp.inner_apply, dotProduct,
      mul_comm]
  rw [hsource] at hz
  exact hz

set_option maxHeartbeats 800000 in
/-- The concrete remainder converges to zero in probability under the exact
truth Born rows. -/
theorem mixedPolynomialHajekRemainder_converges
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    HajekRemainderConvergesInProbability
      (mixedPolynomialHajekExperiment theta b hTruth) 0
      (mixedPolynomialHajekRemainder theta b) := by
  intro h epsilon hepsilon
  have hresidual :=
    mixedPolynomialTotalScaleResidual_convergesInProbability
      theta
      (mixedPolynomialTruthFrameWhiteningDirection theta b h)
      b hTruth hSeed hHoeffding
  unfold MixedPolynomialTotalScaleRowConvergesInProbability at hresidual
  simp only [mixedPolynomialHajekExperiment,
    mixedPolynomialHajekSafePhysicalParameter_zero theta b hTruth,
    mixedPolynomialHajekRemainder]
  convert hresidual epsilon hepsilon using 1
  funext n
  congr 1

/-- The remaining finite computational obligation: the pointwise
Radon--Nikodym ratio of the eventual local Born law equals the exponential of
the already verified complete log likelihood.  This is deliberately a
proposition, not an axiom. -/
def MixedPolynomialFiniteRadonNikodymIdentity
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta) : Prop :=
  ∀ h : HajekParameter (Fin 3), ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ row : MixedPolynomialTotalScaleRow n,
      hajekLikelihoodRatio
          (mixedPolynomialHajekExperiment theta b hTruth) n
          (hajekLocalParameter 0 h n) 0 row =
        Real.exp
          (mixedPolynomialTotalScaleCompleteLogLikelihood theta
            (mixedPolynomialTruthFrameWhiteningDirection theta b h)
            b n row)

/-- All non-Radon--Nikodym fields of the concrete frozen Hajek LAN record are
closed.  Supplying the named finite identity completes the record without any
additional scientific premise. -/
noncomputable def mixedPolynomialConcreteFrozenHajekLAN_of_finiteRN
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
    (hRN : MixedPolynomialFiniteRadonNikodymIdentity theta b hTruth) :
    Hajek1972Assumption31LAN
      (mixedPolynomialHajekExperiment theta b hTruth) 0 := by
  refine
    { truth_mem := Set.mem_univ 0
      information := mixedFrozenOracleInformation
      information_posDef := mixedFrozenOracleInformation_posDef
      score := mixedPolynomialHajekScore theta b
      score_measurable := mixedPolynomialHajekScore_measurable theta b
      remainder := mixedPolynomialHajekRemainder theta b
      remainder_measurable :=
        mixedPolynomialHajekRemainder_measurable theta b
      local_parameter_eventually_mem := ?_
      likelihood_ratio_expansion := ?_
      score_converges :=
        mixedPolynomialHajekScore_converges
          theta b hTruth hSeed hHoeffding
      remainder_converges :=
        mixedPolynomialHajekRemainder_converges
          theta b hTruth hSeed hHoeffding }
  · intro h
    exact ⟨0, fun n hn => Set.mem_univ _⟩
  · intro h
    obtain ⟨N, hN⟩ := hRN h
    refine ⟨N, fun n hn row => ?_⟩
    change MixedPolynomialTotalScaleRow n at row
    rw [hN n hn row]
    congr 1
    rw [mixedPolynomialTotalScaleCompleteLogLikelihood_exact]
    rw [← mixedPolynomialRowWhitenedVectorScore_projection
      theta b n row h]
    rw [mixedPolynomialTruthFrameDirectionalInformation_whitened
      theta b h hTruth hSeed]
    unfold mixedPolynomialHajekScore mixedPolynomialHajekRemainder
      hajekQuadraticForm
    rw [mixedFrozenOracleInformation_quadratic]
    ring

/-- Paper-facing frozen LAN package, still conditional only on the named finite
Radon--Nikodym computation. -/
noncomputable def constructConcreteFrozenMixedQubitLANConclusion_of_finiteRN
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
    (hRN : MixedPolynomialFiniteRadonNikodymIdentity theta b hTruth) :
    FrozenMixedQubitLANConclusion
      (mixedPolynomialHajekExperiment theta b hTruth) 0 :=
  constructFrozenMixedQubitLANConclusion
    (mixedPolynomialConcreteFrozenHajekLAN_of_finiteRN
      theta b hTruth hSeed hHoeffding hRN)
    rfl

end

end QubitOracle.Paper
