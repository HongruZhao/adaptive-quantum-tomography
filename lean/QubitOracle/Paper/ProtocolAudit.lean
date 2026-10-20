/-!
# Logical audit of the protocol-specific adaptive-LAN conditions

This module records the logical interface between the manuscript's
protocol-specific verification and conditions (A1)--(A3) of the adaptive-LAN
proposition.  It deliberately proves no analytic or probabilistic statement.
Every such statement is a field of `AdaptiveLANClaims`, and every proof of one
is supplied explicitly through a protocol evidence record.
-/

namespace QubitOracle
namespace Paper
namespace ProtocolAudit

/-- Names for all analytic statements used by conditions (A1)--(A3).

A value of this structure contains propositions, not proofs of them.  Thus it
introduces no analytic facts; those enter only as explicit fields of the
evidence structures below. -/
structure AdaptiveLANClaims where
  policyPredictable : Prop
  externalRandomizationParameterIndependent : Prop
  conditionalOutcomeLaw : Prop
  regularIndicatorPredictable : Prop
  summableDQM : Prop
  scoreConditionalMeanZero : Prop
  informationConvergence : Prop
  informationLimitPositiveDefinite : Prop
  martingaleLindeberg : Prop
  exceptionalRoundsSublinearInMean : Prop
  localBuresQuadratic : Prop

/-- Condition (A1): predictable, parameter-free protocol selection and the
conditional Born outcome law.  The standing predictability requirement on the
regular-round indicator is included here so that the package is complete. -/
structure ConditionA1 (claims : AdaptiveLANClaims) : Prop where
  policyPredictable : claims.policyPredictable
  externalRandomizationParameterIndependent :
    claims.externalRandomizationParameterIndependent
  conditionalOutcomeLaw : claims.conditionalOutcomeLaw
  regularIndicatorPredictable : claims.regularIndicatorPredictable

/-- Condition (A2): summable DQM and the regular martingale score-array
conditions, including a positive-definite limiting information matrix. -/
structure ConditionA2 (claims : AdaptiveLANClaims) : Prop where
  summableDQM : claims.summableDQM
  scoreConditionalMeanZero : claims.scoreConditionalMeanZero
  informationConvergence : claims.informationConvergence
  informationLimitPositiveDefinite :
    claims.informationLimitPositiveDefinite
  martingaleLindeberg : claims.martingaleLindeberg

/-- Condition (A3): sublinear exceptional rounds in mean and compact-uniform
local quadratic Bures control. -/
structure ConditionA3 (claims : AdaptiveLANClaims) : Prop where
  exceptionalRoundsSublinearInMean :
    claims.exceptionalRoundsSublinearInMean
  localBuresQuadratic : claims.localBuresQuadratic

/-- The three separately exposed hypotheses of the manuscript's adaptive-LAN
proposition. -/
structure AdaptiveLANConditions (claims : AdaptiveLANClaims) : Prop where
  conditionA1 : ConditionA1 claims
  conditionA2 : ConditionA2 claims
  conditionA3 : ConditionA3 claims

/-- Analytic evidence supplied for the interior mixed-qubit protocol.

For example, the manuscript obtains the last two fields from the absence of
exceptional mixed rounds and smooth Bures geometry.  This record does not make
those deductions; it requires their conclusions explicitly. -/
structure MixedProtocolEvidence (claims : AdaptiveLANClaims) : Prop where
  -- (A1)
  a1PolicyPredictable : claims.policyPredictable
  a1ExternalRandomizationParameterIndependent :
    claims.externalRandomizationParameterIndependent
  a1ConditionalOutcomeLaw : claims.conditionalOutcomeLaw
  a1RegularIndicatorPredictable : claims.regularIndicatorPredictable
  -- (A2)
  a2SummableDQM : claims.summableDQM
  a2ScoreConditionalMeanZero : claims.scoreConditionalMeanZero
  a2InformationConvergence : claims.informationConvergence
  a2InformationLimitPositiveDefinite :
    claims.informationLimitPositiveDefinite
  a2MartingaleLindeberg : claims.martingaleLindeberg
  -- (A3)
  a3ExceptionalRoundsSublinearInMean :
    claims.exceptionalRoundsSublinearInMean
  a3LocalBuresQuadratic : claims.localBuresQuadratic

/-- Analytic evidence supplied for the finite-dimensional rank-one protocol.

In particular, `a1RegularIndicatorPredictable` is where the proof-only
regular-round indicator is required to be predictable.  No measurability,
limit, or Bures assertion is postulated by this module. -/
structure RankOneProtocolEvidence (claims : AdaptiveLANClaims) : Prop where
  -- (A1)
  a1PolicyPredictable : claims.policyPredictable
  a1ExternalRandomizationParameterIndependent :
    claims.externalRandomizationParameterIndependent
  a1ConditionalOutcomeLaw : claims.conditionalOutcomeLaw
  a1RegularIndicatorPredictable : claims.regularIndicatorPredictable
  -- (A2)
  a2SummableDQM : claims.summableDQM
  a2ScoreConditionalMeanZero : claims.scoreConditionalMeanZero
  a2InformationConvergence : claims.informationConvergence
  a2InformationLimitPositiveDefinite :
    claims.informationLimitPositiveDefinite
  a2MartingaleLindeberg : claims.martingaleLindeberg
  -- (A3)
  a3ExceptionalRoundsSublinearInMean :
    claims.exceptionalRoundsSublinearInMean
  a3LocalBuresQuadratic : claims.localBuresQuadratic

/-- Mixed-protocol evidence discharges conditions (A1)--(A3). -/
theorem mixedProtocolEvidence_dischargesAdaptiveLAN
    {claims : AdaptiveLANClaims}
    (evidence : MixedProtocolEvidence claims) :
    AdaptiveLANConditions claims :=
  { conditionA1 :=
      { policyPredictable := evidence.a1PolicyPredictable
        externalRandomizationParameterIndependent :=
          evidence.a1ExternalRandomizationParameterIndependent
        conditionalOutcomeLaw := evidence.a1ConditionalOutcomeLaw
        regularIndicatorPredictable :=
          evidence.a1RegularIndicatorPredictable }
    conditionA2 :=
      { summableDQM := evidence.a2SummableDQM
        scoreConditionalMeanZero := evidence.a2ScoreConditionalMeanZero
        informationConvergence := evidence.a2InformationConvergence
        informationLimitPositiveDefinite :=
          evidence.a2InformationLimitPositiveDefinite
        martingaleLindeberg := evidence.a2MartingaleLindeberg }
    conditionA3 :=
      { exceptionalRoundsSublinearInMean :=
          evidence.a3ExceptionalRoundsSublinearInMean
        localBuresQuadratic := evidence.a3LocalBuresQuadratic } }

/-- Rank-one-protocol evidence discharges conditions (A1)--(A3). -/
theorem rankOneProtocolEvidence_dischargesAdaptiveLAN
    {claims : AdaptiveLANClaims}
    (evidence : RankOneProtocolEvidence claims) :
    AdaptiveLANConditions claims :=
  { conditionA1 :=
      { policyPredictable := evidence.a1PolicyPredictable
        externalRandomizationParameterIndependent :=
          evidence.a1ExternalRandomizationParameterIndependent
        conditionalOutcomeLaw := evidence.a1ConditionalOutcomeLaw
        regularIndicatorPredictable :=
          evidence.a1RegularIndicatorPredictable }
    conditionA2 :=
      { summableDQM := evidence.a2SummableDQM
        scoreConditionalMeanZero := evidence.a2ScoreConditionalMeanZero
        informationConvergence := evidence.a2InformationConvergence
        informationLimitPositiveDefinite :=
          evidence.a2InformationLimitPositiveDefinite
        martingaleLindeberg := evidence.a2MartingaleLindeberg }
    conditionA3 :=
      { exceptionalRoundsSublinearInMean :=
          evidence.a3ExceptionalRoundsSublinearInMean
        localBuresQuadratic := evidence.a3LocalBuresQuadratic } }

/-- Evidence tagged by which of the two manuscript protocols supplied it. -/
inductive ProtocolEvidence (claims : AdaptiveLANClaims) : Prop where
  | mixed : MixedProtocolEvidence claims -> ProtocolEvidence claims
  | rankOne : RankOneProtocolEvidence claims -> ProtocolEvidence claims

/-- Protocol-specific evidence, for either proposed protocol, discharges the
general adaptive-LAN conditions. -/
theorem protocolSpecificEvidence_dischargesAdaptiveLAN
    {claims : AdaptiveLANClaims}
    (evidence : ProtocolEvidence claims) :
    AdaptiveLANConditions claims := by
  cases evidence with
  | mixed mixedEvidence =>
      exact mixedProtocolEvidence_dischargesAdaptiveLAN mixedEvidence
  | rankOne rankOneEvidence =>
      exact rankOneProtocolEvidence_dischargesAdaptiveLAN rankOneEvidence

end ProtocolAudit
end Paper
end QubitOracle
