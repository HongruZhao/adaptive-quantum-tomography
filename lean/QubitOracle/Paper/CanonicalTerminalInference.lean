import QubitOracle.Paper.AdaptiveMLEEfficiency

/-!
# Canonical terminal-estimator inference labels

This module closes the estimator-inference part of the paper without adding a
scientific axiom.  The primitive hypotheses are exactly the local score-root,
Taylor, Hessian, remainder, score-CLT, and measurability conditions used by the
proof.  The rank-one normalization is made explicit through
`I_rank-one = (1/2) I`, whose inverse is proved to be `2 I`.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- Fisher information in the two-dimensional moving tangent chart at a pure
qubit state: one half of the identity. -/
def rankOneInformationMatrix (D : Type*) [Fintype D] [DecidableEq D] :
    Matrix D D ℝ :=
  (1 / 2 : ℝ) • (1 : Matrix D D ℝ)

/-- Covariance in the rank-one terminal central limit theorem. -/
def rankOneLimitCovariance (D : Type*) [Fintype D] [DecidableEq D] :
    Matrix D D ℝ :=
  (2 : ℝ) • (1 : Matrix D D ℝ)

theorem rankOneInformationMatrix_posDef
    (D : Type*) [Fintype D] [DecidableEq D] :
    (rankOneInformationMatrix D).PosDef := by
  rw [rankOneInformationMatrix]
  exact Matrix.PosDef.one.smul (by norm_num)

theorem rankOneInformationMatrix_inv
    (D : Type*) [Fintype D] [DecidableEq D] :
    (rankOneInformationMatrix D)⁻¹ = rankOneLimitCovariance D := by
  rw [rankOneInformationMatrix]
  letI : Invertible (1 / 2 : ℝ) := invertibleOfNonzero (by norm_num)
  rw [Matrix.inv_smul (1 : Matrix D D ℝ) (1 / 2 : ℝ) (by simp)]
  simp [rankOneLimitCovariance]

/-- Primitive sufficient conditions for terminal score-root inference.  This
is deliberately not a conclusion-shaped assumption: each field is a local
analytic or probabilistic obligation used in the score-root proof. -/
structure TerminalInferenceConditions
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ)
    (Delta : ℕ → Omega → LANParameter D) : Prop where
  information_posDef : M.PosDef
  score_root : problem.IsScoreRoot mu
  score_taylor : problem.HasScoreTaylorExpansion mu Delta
  hessian_linearization : problem.HasUniformHessianLinearizationAtRoot mu M
  taylor_remainder : TendstoInMeasure mu problem.taylorRemainder atTop 0
  score_clt :
    TendstoInDistribution Delta atTop id (fun _ => mu)
      (multivariateGaussian 0 M)
  residual_measurable :
    ∀ n, AEMeasurable (problem.asymptoticLinearResidual M Delta n) mu

/-- The common score-root argument: asymptotic linearity followed by Slutsky's
continuous linear transfer of the score CLT. -/
theorem terminalInference_of_conditions
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ)
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu M Delta) :
    problem.HasAsymptoticLinearRepresentation mu M Delta ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction M⁻¹ z) (fun _ => mu)
        (multivariateGaussian 0 M) := by
  have hLinear :=
    problem.asymptoticLinearRepresentation_of_scoreRoot
      mu M h.information_posDef Delta h.score_root h.score_taylor
        h.hessian_linearization h.taylor_remainder
  exact ⟨hLinear,
    problem.tendstoInDistribution_inverseInformationGaussian
      mu M Delta h.score_clt hLinear h.residual_measurable⟩

/-- Exact transformed-Gaussian statement of the rank-one limit.  The source
Gaussian has information `(1/2) I`, and the displayed action is by `2 I`. -/
theorem rankOneTerminalInference_of_conditions
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu
      (rankOneInformationMatrix D) Delta) :
    problem.HasAsymptoticLinearRepresentation mu
        (rankOneInformationMatrix D) Delta ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction (rankOneLimitCovariance D) z)
        (fun _ => mu)
        (multivariateGaussian 0 (rankOneInformationMatrix D)) := by
  rcases terminalInference_of_conditions problem mu
    (rankOneInformationMatrix D) Delta h with ⟨hLinear, hCLT⟩
  refine ⟨hLinear, ?_⟩
  simpa only [rankOneInformationMatrix_inv] using hCLT

namespace Label

/-- Supplement equation `eq:SI_mixed_AL`. -/
theorem eq_SI_mixed_AL
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ) (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu M Delta) :
    problem.HasAsymptoticLinearRepresentation mu M Delta :=
  (terminalInference_of_conditions problem mu M Delta h).1

/-- Main-text mixed-state terminal CLT `eq:mixed_terminal_clt`. -/
theorem eq_mixed_terminal_clt
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ) (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu M Delta) :
    TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction M⁻¹ z) (fun _ => mu)
      (multivariateGaussian 0 M) :=
  (terminalInference_of_conditions problem mu M Delta h).2

/-- Supplement equation `eq:SI_mixed_terminal_clt`. -/
theorem eq_SI_mixed_terminal_clt
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ) (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu M Delta) :
    TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction M⁻¹ z) (fun _ => mu)
      (multivariateGaussian 0 M) :=
  eq_mixed_terminal_clt problem mu M Delta h

/-- Supplement mixed-terminal theorem `thm:SI_mixed_terminal`. -/
theorem thm_SI_mixed_terminal
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ) (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu M Delta) :
    problem.HasAsymptoticLinearRepresentation mu M Delta ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction M⁻¹ z) (fun _ => mu)
        (multivariateGaussian 0 M) :=
  terminalInference_of_conditions problem mu M Delta h

/-- Supplement rank-one asymptotic linearity equation `eq:SI_r1_AL`. -/
theorem eq_SI_r1_AL
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu
      (rankOneInformationMatrix D) Delta) :
    problem.HasAsymptoticLinearRepresentation mu
      (rankOneInformationMatrix D) Delta :=
  (rankOneTerminalInference_of_conditions problem mu Delta h).1

/-- Main-text rank-one terminal CLT `eq:r1_terminal_clt`. -/
theorem eq_r1_terminal_clt
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu
      (rankOneInformationMatrix D) Delta) :
    TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction (rankOneLimitCovariance D) z)
      (fun _ => mu)
      (multivariateGaussian 0 (rankOneInformationMatrix D)) :=
  (rankOneTerminalInference_of_conditions problem mu Delta h).2

/-- Supplement equation `eq:SI_r1_terminal_clt`. -/
theorem eq_SI_r1_terminal_clt
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu
      (rankOneInformationMatrix D) Delta) :
    TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction (rankOneLimitCovariance D) z)
      (fun _ => mu)
      (multivariateGaussian 0 (rankOneInformationMatrix D)) :=
  eq_r1_terminal_clt problem mu Delta h

/-- Supplement rank-one terminal theorem `thm:SI_r1_terminal`. -/
theorem thm_SI_r1_terminal
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Delta : ℕ → Omega → LANParameter D)
    (h : TerminalInferenceConditions problem mu
      (rankOneInformationMatrix D) Delta) :
    problem.HasAsymptoticLinearRepresentation mu
        (rankOneInformationMatrix D) Delta ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction (rankOneLimitCovariance D) z)
        (fun _ => mu)
        (multivariateGaussian 0 (rankOneInformationMatrix D)) :=
  rankOneTerminalInference_of_conditions problem mu Delta h

/-- Main terminal-inference theorem `thm:terminal_inference`, combining the
mixed-state and rank-one branches under their primitive score-root conditions. -/
theorem thm_terminal_inference
    {DM DR : Type*} {OmegaM OmegaR : Type}
    [Fintype DM] [DecidableEq DM] [Fintype DR] [DecidableEq DR]
    [MeasurableSpace OmegaM] [MeasurableSpace OmegaR]
    (mixedProblem : AdaptiveScoreRootProblem DM OmegaM)
    (rankOneProblem : AdaptiveScoreRootProblem DR OmegaR)
    (muM : Measure OmegaM) [IsProbabilityMeasure muM]
    (muR : Measure OmegaR) [IsProbabilityMeasure muR]
    (M : Matrix DM DM ℝ)
    (mixedDelta : ℕ → OmegaM → LANParameter DM)
    (rankOneDelta : ℕ → OmegaR → LANParameter DR)
    (hMixed : TerminalInferenceConditions mixedProblem muM M mixedDelta)
    (hRankOne : TerminalInferenceConditions rankOneProblem muR
      (rankOneInformationMatrix DR) rankOneDelta) :
    (mixedProblem.HasAsymptoticLinearRepresentation muM M mixedDelta ∧
      TendstoInDistribution mixedProblem.localError atTop
        (fun z => lanMatrixAction M⁻¹ z) (fun _ => muM)
        (multivariateGaussian 0 M)) ∧
    (rankOneProblem.HasAsymptoticLinearRepresentation muR
        (rankOneInformationMatrix DR) rankOneDelta ∧
      TendstoInDistribution rankOneProblem.localError atTop
        (fun z => lanMatrixAction (rankOneLimitCovariance DR) z)
        (fun _ => muR)
        (multivariateGaussian 0 (rankOneInformationMatrix DR))) :=
  ⟨thm_SI_mixed_terminal mixedProblem muM M mixedDelta hMixed,
    thm_SI_r1_terminal rankOneProblem muR rankOneDelta hRankOne⟩

end Label

end

end QubitOracle.Paper
