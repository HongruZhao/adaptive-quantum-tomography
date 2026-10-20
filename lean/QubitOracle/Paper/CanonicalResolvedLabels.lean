import QubitOracle.FourDimensional
import QubitOracle.RankOneLosses
import QubitOracle.Paper.AdaptiveLANExperimentBridge
import QubitOracle.Paper.AdaptivePolicyMixture
import QubitOracle.Paper.ExplorationScheduleLabels
import QubitOracle.Paper.InformationPathLabelStrengthening
import QubitOracle.Paper.MixedOracleFeasible
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.RankOneStageContinuity
import QubitOracle.Paper.RetainedTailSet
import QubitOracle.Paper.SequentialHessian

/-!
# Canonical wrappers for exactly resolved manuscript labels

Every declaration in this file is a source-faithful wrapper around an
existing definition or proved theorem.  Labels whose current Lean analogue
does not preserve the manuscript's quantifiers, convergence mode, physical
loss, or stochastic object are intentionally absent.
-/

namespace QubitOracle.Paper.Label

open QubitOracle QubitOracle.Paper
open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Main-paper definitions -/

/-- Main equation `eq:design_info`: entrywise design-information integral. -/
abbrev eq_design_info {U : Type*} [MeasurableSpace U]
    (axisInformation : U -> OracleMatrix) (xi : Measure U) : OracleMatrix :=
  mixedDesignInformation axisInformation xi

/-- Main equation `eq:A_criterion`, on the nonsingular regular domain. -/
theorem eq_A_criterion (G M : OracleMatrix) (_hM : M.PosDef) :
    mixedDesignCriterion G M = Matrix.trace (G * M⁻¹) :=
  rfl

/-- Main equation `eq:adaptive_LAN`: the RN likelihood remainder and Gaussian
score convergence, together with the local domination needed to form the RN
derivative. -/
abbrev eq_adaptive_LAN
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ -> StatisticalExperiment (LANParameter D))
    (M : Matrix D D ℝ)
    (score : ∀ n, (E n).Sample -> LANParameter D) : Prop :=
  IsLANSequence E M score

/-- Main equation `eq:Gaussian_shift_limit`: `X = h + Z`,
`Z ~ N(0,M⁻¹)`. -/
abbrev eq_Gaussian_shift_limit
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D ℝ) : StatisticalExperiment (LANParameter D) :=
  gaussianLocationExperiment M⁻¹

/-- Main equation `eq:r1_local_chart`. -/
abbrev eq_r1_local_chart {n : ℕ} (h : TangentIndex n -> ℝ) :
    Fin (n + 1) -> ℂ :=
  chartState h

/-- Main equation `eq:GM_region`, expressed as equality of membership
predicates after the `J^(1/2)` congruence. -/
theorem eq_GM_region (S M : OracleMatrix) :
    (∃ A : OracleMatrix,
        IsNormalizedProjectiveInformation A ∧
          M = S * A * S.transpose) ↔
      ∃ A : OracleMatrix,
        A.PosSemidef ∧ Matrix.trace A = 1 ∧
          M = S * A * S.transpose := by
  constructor
  · rintro ⟨A, hA, hM⟩
    have hchar := (normalized_projective_information_iff A).1 hA
    exact ⟨A, hchar.1, hchar.2, hM⟩
  · rintro ⟨A, hpos, htrace, hM⟩
    exact ⟨A, (normalized_projective_information_iff A).2 ⟨hpos, htrace⟩, hM⟩

/-- Main equation `eq:general_three_axes`, with `r_j = sqrt(c_j)`. -/
theorem eq_general_three_axes
    (S : OracleMatrix) (c : Fin 3 -> ℝ)
    (x : Fin 3 -> Fin 3 -> ℝ) (i : Fin 3) :
    oracleThreeAxis S x i = oracleNormalize (S.mulVec (x i)) ∧
      oracleThreeAxisWeight (fun j => Real.sqrt (c j)) i =
        Real.sqrt (c i) / ∑ j, Real.sqrt (c j) :=
  ⟨rfl, rfl⟩

/-- Main equation `eq:r1_chi_basis`. -/
abbrev eq_r1_chi_basis {n : ℕ} (F : OracleFrame n) :=
  chiBasis F

/-- Main equation `eq:r1_tau_basis`. -/
abbrev eq_r1_tau_basis {n : ℕ} (F : OracleFrame n) :=
  tauBasis F

/-- Main equation `eq:hadamard_four`. -/
abbrev eq_hadamard_four : Matrix (Fin 4) (Fin 4) ℝ :=
  hadamard4

/-- Main equation `eq:two_qubit_global_unitaries`.  `phaseMatrix 3` is the
displayed `D = diag(-i,1,1,1)`, and `preReadout` is the adjoint. -/
theorem eq_two_qubit_global_unitaries
    (E : Matrix (Fin 4) (Fin 4) ℂ) :
    transportedChiBasis E fourDimensionalFrame =
        E * chiBasis fourDimensionalFrame ∧
      transportedTauBasis E fourDimensionalFrame =
        E * (phaseMatrix 3 * chiBasis fourDimensionalFrame) ∧
      preReadout (transportedChiBasis E fourDimensionalFrame) =
        star (transportedChiBasis E fourDimensionalFrame) ∧
      preReadout (transportedTauBasis E fourDimensionalFrame) =
        star (transportedTauBasis E fourDimensionalFrame) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Main equation `eq:sequential_mixture`, for a finite setting space. -/
theorem eq_sequential_mixture
    {M Y : Type*} [Fintype M]
    (epsilon : SequentialHistory M Y -> ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (h : SequentialHistory M Y) (m : M) :
    (adaptivePolicyMixture epsilon exploit explore
        hepsilon_nonneg hepsilon_le_one).mass h m =
      (1 - epsilon h) * exploit.mass h m +
        epsilon h * explore.mass h m :=
  rfl

/-- Main equation `eq:exploration_conditions`. -/
abbrev eq_exploration_conditions (epsilon : ℕ -> ℝ) : Prop :=
  ExplorationScheduleHypotheses epsilon

/-- Main equation `eq:accumulated_mixed_info`. -/
abbrev eq_accumulated_mixed_info
    {Theta M Y : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y (Fin 3))
    (theta : Theta) (h : SequentialHistory M Y) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  empiricalInformation model theta h

/-- Main equation `eq:accumulated_r1_info`. -/
abbrev eq_accumulated_r1_info
    {Theta M Y : Type*} [Fintype Y] {n : ℕ}
    (model : FiniteScoreModel Theta M Y (TangentIndex n))
    (theta : Theta) (h : SequentialHistory M Y) :
    Matrix (TangentIndex n) (TangentIndex n) ℝ :=
  empiricalInformation model theta h

/-- Main equation `eq:retained_index_set_main`. -/
abbrev eq_retained_index_set_main
    (n : ℕ) (exploration : ℕ -> ℕ) : Finset ℕ :=
  terminalTailSet n exploration

/-! ## Supplement definitions and elementary identities -/

/-- Supplement equation `eq:SI_r1_chart`. -/
abbrev eq_SI_r1_chart {n : ℕ} (h : TangentIndex n -> ℝ) :
    Fin (n + 1) -> ℂ :=
  chartState h

/-- Supplement equation `eq:SI_chi_basis`. -/
abbrev eq_SI_chi_basis {n : ℕ} (F : OracleFrame n) :=
  chiBasis F

/-- Supplement equation `eq:SI_tau_basis`. -/
abbrev eq_SI_tau_basis {n : ℕ} (F : OracleFrame n) :=
  tauBasis F

/-- Supplement equation `eq:SI_mixed_target`, simultaneously for the
Frobenius/trace and Bures rows of the manuscript table. -/
theorem eq_SI_mixed_target
    (r : Fin 3 -> ℝ)
    (hr0 : 0 < blochNormSq r) (hr1 : blochNormSq r < 1) :
    mixedFrobeniusTraceTarget r =
        mixedCoherenceAllocation r • mixedTangentProjector r +
          (mixedRadialAllocation r / (1 - blochNormSq r)) •
            mixedRadialProjector r ∧
      mixedBuresTarget r =
        (1 / 3 : ℝ) • mixedTangentProjector r +
          ((1 / 3 : ℝ) / (1 - blochNormSq r)) •
            mixedRadialProjector r :=
  ⟨mixedFrobeniusTraceTarget_eq_radialTangent r hr0 hr1,
    mixedBuresTarget_eq_radialTangent r hr0 hr1⟩

/-- Supplement equation `eq:SI_stage_mixed_info`. -/
abbrev eq_SI_stage_mixed_info
    {M : Type*} [Fintype M]
    (r : Fin 3 -> ℝ) (mass : M -> ℝ)
    (axis : M -> Fin 3 -> ℝ) : OracleMatrix :=
  mixedStageInformation r mass axis

/-- Supplement equation `eq:SI_mixed_score_increment`, split into its two
binary outcomes. -/
theorem eq_SI_mixed_score_increment (theta u : Fin 3 -> ℝ) :
    mixedAxisPlusScoreVector theta u =
        (fun i => (1 + blochDot theta u)⁻¹ * u i) ∧
      mixedAxisMinusScoreVector theta u =
        (fun i => -(1 - blochDot theta u)⁻¹ * u i) :=
  ⟨rfl, rfl⟩

/-- Supplement equation `eq:SI_mixed_hessian_mean`: for the affine binary
Born model, observed information is the score outer product, so the exact
second-score-moment theorem is the displayed expected-Hessian identity. -/
theorem eq_SI_mixed_hessian_mean
    (theta u : Fin 3 -> ℝ)
    (hregular : blochDot theta u ^ 2 < 1) :
    ∀ i j,
      binaryAxisPlusProbability (blochDot theta u) *
            mixedAxisPlusScoreVector theta u i *
            mixedAxisPlusScoreVector theta u j +
        binaryAxisMinusProbability (blochDot theta u) *
            mixedAxisMinusScoreVector theta u i *
            mixedAxisMinusScoreVector theta u j =
          mixedAxisFisher theta u i j :=
  mixedAxisScore_secondMoment_eq_fisher theta u hregular

/-- Supplement equation `eq:SI_r1_margin`, with the explicit deterministic
choice `c0 = 1/(2d)`. -/
theorem eq_SI_r1_margin {n : ℕ}
    (F : OracleFrame n)
    (controllerFrame : ℕ ->
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hunitary : ∀ m, controllerFrame m ∈
      Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hoverlap : Tendsto
      (fun m => controllerTrueOverlapSq (controllerFrame m))
      atTop (nhds 1)) :
    ∃ c0 : ℝ, 0 < c0 ∧
      ∀ᶠ m in atTop, ∀ k : Fin (n + 1),
        c0 ≤ fixedChartBasisProbability
            (controllerChiBasis F (controllerFrame m)) k ∧
          c0 ≤ fixedChartBasisProbability
            (controllerTauBasis F (controllerFrame m)) k := by
  refine ⟨1 / (2 * (n + 1 : ℝ)), ?_, ?_⟩
  · positivity
  · exact eventually_rankOne_exploitation_probability_margin
      F controllerFrame hunitary hoverlap

/-- Supplement equation `eq:SI_regular_information_limit`, in the equivalent
finite-dimensional quadratic-form formulation used by Hall--Heyde. -/
abbrev eq_SI_regular_information_limit
    {D : Type*} [Fintype D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ) : Prop :=
  problem.ConditionalCovarianceConverges M

end

end QubitOracle.Paper.Label
