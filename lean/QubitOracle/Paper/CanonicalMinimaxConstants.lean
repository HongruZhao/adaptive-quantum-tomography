import QubitOracle.Paper.QuadraticRiskAttainability
import QubitOracle.Paper.SourceFaithfulDesignOptimality

/-!
# Canonical local-minimax constants

This file closes three displayed paper labels without identifying a finite
information-matrix inequality with a minimax theorem.  The statistical part
uses the source-faithful Gaussian-score asymptotic minimax theorem for the
universal lower bound and the already proved capped-risk/uniform-tail theorem
for attainment.  The remaining bridge from the paper's physical state loss to
the LAN quadratic risk is exposed as `HasExactPhysicalLossTransfer`.
-/

open scoped ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace QubitOracle.Paper

universe uD uSample

/-- A sequence of local estimators for a sequence of LAN experiments. -/
abbrev LocalEstimatorSequence {D : Type uD} [Fintype D]
    (E : ℕ → StatisticalExperiment (LANParameter D)) :=
  (m : ℕ) → Statistic (E m) (LANParameter D)

/-- Explicit bridge still required to turn the normalized quadratic LAN risk
into the paper's normalized physical-state loss.  This is a definition, not an
axiom: a protocol-specific verification must prove the displayed equality for
every estimator sequence. -/
def HasExactPhysicalLossTransfer {D : Type uD} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (physicalRisk : LocalEstimatorSequence E → ENNReal) : Prop :=
  ∀ S, physicalRisk S = asymptoticFiniteLocalQuadraticRisk E S

/-- LAN plus uniform-integrability hypotheses give all three logically
distinct claims needed for a minimax equality: every estimator obeys the lower
bound, the nominated estimator attains it, and the infimum over all estimators
equals the Gaussian benchmark. -/
theorem physicalLocalMinimax_lower_attained_and_value
    {D : Type uD} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (hLAN : ExperimentsConverge E (gaussianScoreExperiment J))
    (physicalRisk : LocalEstimatorSequence E → ENNReal)
    (hLossTransfer : HasExactPhysicalLossTransfer E physicalRisk)
    (T : LocalEstimatorSequence E)
    (hCapped : ∀ I : Finset (LANParameter D), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hTails : ∀ I : Finset (LANParameter D), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails E T I) :
    (∀ S, ENNReal.ofReal (Matrix.trace J⁻¹) ≤ physicalRisk S) ∧
      physicalRisk T = ENNReal.ofReal (Matrix.trace J⁻¹) ∧
      (⨅ S, physicalRisk S) = ENNReal.ofReal (Matrix.trace J⁻¹) := by
  have hLower : ∀ S, ENNReal.ofReal (Matrix.trace J⁻¹) ≤ physicalRisk S := by
    intro S
    rw [hLossTransfer S]
    exact gaussianScore_localAsymptoticMinimax_quadratic J hJ E hLAN S
  have hAttained :
      physicalRisk T = ENNReal.ofReal (Matrix.trace J⁻¹) := by
    rw [hLossTransfer T]
    exact gaussianScore_localAsymptoticMinimax_attained_of_cappedGaussian_of_uniformTails
      J hJ E hLAN T hCapped hTails
  refine ⟨hLower, hAttained, le_antisymm ?_ ?_⟩
  · exact (iInf_le physicalRisk T).trans_eq hAttained
  · exact le_iInf hLower

namespace Label

/-- Main-text equation `eq:mixed_local_minimax_constant`.

The first three conclusions are the universal physical-risk lower bound,
attainment, and the genuine all-estimator minimax equality at `9/4`.  The last
two conclusions independently identify `9/4` as the source-constrained mixed
Bures/fidelity design optimum.  `hLossTransfer` and `hGaussianConstant` state
the protocol-specific physical-loss and whitening identifications explicitly.
-/
theorem eq_mixed_local_minimax_constant
    {O : Type} [Fintype O]
    (model : SourceFaithfulGillMassar.OneCopySLDModel 2 (Fin 3))
    (P : FinitePOVM (Fin 2) O)
    [SourceFaithfulGillMassar.GillMassar2000OneCopyAssumption model P]
    (A Ainv H K : OracleMatrix)
    (hSourceHpos : (SourceFaithfulGillMassar.sldQuantumFisher model).PosDef)
    (hTraceIdentification :
      SourceFaithfulGillMassar.informationTrace model P = Matrix.trace A)
    (hHK : H * K = 1) (hHsym : H.transpose = H)
    (hKsym : K.transpose = K) (hHsq : H * H = A)
    (hKsq : K * K = Ainv) (hTraceA0 : 0 ≤ Matrix.trace A)
    (hDesignRisk0 :
      0 ≤ Matrix.trace
        (SourceFaithfulDesignOptimality.mixedBuresInfidelityNormalizedCost * Ainv))
    (J : Matrix (Fin 3) (Fin 3) ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter (Fin 3)))
    (hLAN : ExperimentsConverge E (gaussianScoreExperiment J))
    (physicalRisk : LocalEstimatorSequence E → ENNReal)
    (hLossTransfer : HasExactPhysicalLossTransfer E physicalRisk)
    (T : LocalEstimatorSequence E)
    (hCapped : ∀ I : Finset (LANParameter (Fin 3)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hTails : ∀ I : Finset (LANParameter (Fin 3)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails E T I)
    (hGaussianConstant : Matrix.trace J⁻¹ = (9 / 4 : ℝ)) :
    (∀ S, ENNReal.ofReal (9 / 4 : ℝ) ≤ physicalRisk S) ∧
      physicalRisk T = ENNReal.ofReal (9 / 4 : ℝ) ∧
      (⨅ S, physicalRisk S) = ENNReal.ofReal (9 / 4 : ℝ) ∧
      (9 / 4 : ℝ) ≤ mixedDesignCriterion
        SourceFaithfulDesignOptimality.mixedBuresInfidelityNormalizedCost A ∧
      mixedDesignCriterion
        SourceFaithfulDesignOptimality.mixedBuresInfidelityNormalizedCost
        SourceFaithfulDesignOptimality.mixedBuresInfidelityNormalizedOptimizer =
        (9 / 4 : ℝ) := by
  have hMinimax := physicalLocalMinimax_lower_attained_and_value
    J hJ E hLAN physicalRisk hLossTransfer T hCapped hTails
  rw [hGaussianConstant] at hMinimax
  have hDesign :=
    SourceFaithfulDesignOptimality.mixedQubit_buresInfidelity_normalized_optimality_from_source
      model P A Ainv H K hSourceHpos hTraceIdentification hHK hHsym hKsym
      hHsq hKsq hTraceA0 hDesignRisk0
  exact ⟨hMinimax.1, hMinimax.2.1, hMinimax.2.2,
    hDesign.1, hDesign.2.1⟩

/-- Main-text equation `eq:r1_local_minimax_constants`.

For the three loss normalizations, the theorem records a universal lower
bound, an attaining estimator, and equality of the infimum over every
estimator.  The final equalities connect those asymptotic constants to the
rank-one equal-mixture oracle calculation. -/
theorem eq_r1_local_minimax_constants
    {n : ℕ} (F : OracleFrame n)
    (JF JT JB : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hJF : JF.PosDef) (hJT : JT.PosDef) (hJB : JB.PosDef)
    (EF ET EB : ℕ → StatisticalExperiment (LANParameter (TangentIndex n)))
    (hLANF : ExperimentsConverge EF (gaussianScoreExperiment JF))
    (hLANT : ExperimentsConverge ET (gaussianScoreExperiment JT))
    (hLANB : ExperimentsConverge EB (gaussianScoreExperiment JB))
    (physicalF : LocalEstimatorSequence EF → ENNReal)
    (physicalT : LocalEstimatorSequence ET → ENNReal)
    (physicalB : LocalEstimatorSequence EB → ENNReal)
    (hTransferF : HasExactPhysicalLossTransfer EF physicalF)
    (hTransferT : HasExactPhysicalLossTransfer ET physicalT)
    (hTransferB : HasExactPhysicalLossTransfer EB physicalB)
    (TF : LocalEstimatorSequence EF) (TT : LocalEstimatorSequence ET)
    (TB : LocalEstimatorSequence EB)
    (hCappedF : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JF EF TF I)
    (hCappedT : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JT ET TT I)
    (hCappedB : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JB EB TB I)
    (hTailsF : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails EF TF I)
    (hTailsT : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails ET TT I)
    (hTailsB : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails EB TB I)
    (hGaussianF : Matrix.trace JF⁻¹ = 2 * (n : ℝ))
    (hGaussianT : Matrix.trace JT⁻¹ = (n : ℝ))
    (hGaussianB : Matrix.trace JB⁻¹ = (n : ℝ)) :
    ((∀ S, ENNReal.ofReal (2 * (n : ℝ)) ≤ physicalF S) ∧
      physicalF TF = ENNReal.ofReal (2 * (n : ℝ)) ∧
      (⨅ S, physicalF S) = ENNReal.ofReal (2 * (n : ℝ))) ∧
    ((∀ S, ENNReal.ofReal (n : ℝ) ≤ physicalT S) ∧
      physicalT TT = ENNReal.ofReal (n : ℝ) ∧
      (⨅ S, physicalT S) = ENNReal.ofReal (n : ℝ)) ∧
    ((∀ S, ENNReal.ofReal (n : ℝ) ≤ physicalB S) ∧
      physicalB TB = ENNReal.ofReal (n : ℝ) ∧
      (⨅ S, physicalB S) = ENNReal.ofReal (n : ℝ)) ∧
    isotropicRisk (1 / 2) (equalMixtureFisher F) = 2 * (n : ℝ) ∧
    isotropicRisk (1 / 4) (equalMixtureFisher F) = (n : ℝ) ∧
    isotropicRisk (1 / 4) (equalMixtureFisher F) = (n : ℝ) := by
  have hF := physicalLocalMinimax_lower_attained_and_value
    JF hJF EF hLANF physicalF hTransferF TF hCappedF hTailsF
  have hT := physicalLocalMinimax_lower_attained_and_value
    JT hJT ET hLANT physicalT hTransferT TT hCappedT hTailsT
  have hB := physicalLocalMinimax_lower_attained_and_value
    JB hJB EB hLANB physicalB hTransferB TB hCappedB hTailsB
  rw [hGaussianF] at hF
  rw [hGaussianT] at hT
  rw [hGaussianB] at hB
  exact ⟨hF, hT, hB, equalMixture_frobeniusRisk F,
    equalMixture_traceRisk F, equalMixture_buresQuadraticRisk F⟩

/-- Main-text equation `eq:r1_risk_lower_bounds`.

This is the expected-risk form of the preceding minimax constants.  It retains
the attaining equalities, rather than weakening the displayed result to the
finite information-matrix inequalities alone. -/
theorem eq_r1_risk_lower_bounds
    {n : ℕ} (F : OracleFrame n)
    (JF JT JB : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hJF : JF.PosDef) (hJT : JT.PosDef) (hJB : JB.PosDef)
    (EF ET EB : ℕ → StatisticalExperiment (LANParameter (TangentIndex n)))
    (hLANF : ExperimentsConverge EF (gaussianScoreExperiment JF))
    (hLANT : ExperimentsConverge ET (gaussianScoreExperiment JT))
    (hLANB : ExperimentsConverge EB (gaussianScoreExperiment JB))
    (physicalF : LocalEstimatorSequence EF → ENNReal)
    (physicalT : LocalEstimatorSequence ET → ENNReal)
    (physicalB : LocalEstimatorSequence EB → ENNReal)
    (hTransferF : HasExactPhysicalLossTransfer EF physicalF)
    (hTransferT : HasExactPhysicalLossTransfer ET physicalT)
    (hTransferB : HasExactPhysicalLossTransfer EB physicalB)
    (TF : LocalEstimatorSequence EF) (TT : LocalEstimatorSequence ET)
    (TB : LocalEstimatorSequence EB)
    (hCappedF : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JF EF TF I)
    (hCappedT : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JT ET TT I)
    (hCappedB : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian JB EB TB I)
    (hTailsF : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails EF TF I)
    (hTailsT : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails ET TT I)
    (hTailsB : ∀ I : Finset (LANParameter (TangentIndex n)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails EB TB I)
    (hGaussianF : Matrix.trace JF⁻¹ = 2 * (n : ℝ))
    (hGaussianT : Matrix.trace JT⁻¹ = (n : ℝ))
    (hGaussianB : Matrix.trace JB⁻¹ = (n : ℝ)) :
    ((∀ S, ENNReal.ofReal (2 * (n : ℝ)) ≤ physicalF S) ∧
      physicalF TF = ENNReal.ofReal (2 * (n : ℝ))) ∧
    ((∀ S, ENNReal.ofReal (n : ℝ) ≤ physicalT S) ∧
      physicalT TT = ENNReal.ofReal (n : ℝ)) ∧
    ((∀ S, ENNReal.ofReal (n : ℝ) ≤ physicalB S) ∧
      physicalB TB = ENNReal.ofReal (n : ℝ)) := by
  have h := eq_r1_local_minimax_constants F JF JT JB hJF hJT hJB
    EF ET EB hLANF hLANT hLANB physicalF physicalT physicalB
    hTransferF hTransferT hTransferB TF TT TB hCappedF hCappedT hCappedB
    hTailsF hTailsT hTailsB hGaussianF hGaussianT hGaussianB
  exact ⟨⟨h.1.1, h.1.2.1⟩,
    ⟨h.2.1.1, h.2.1.2.1⟩,
    ⟨h.2.2.1.1, h.2.2.1.2.1⟩⟩

end Label
end QubitOracle.Paper
