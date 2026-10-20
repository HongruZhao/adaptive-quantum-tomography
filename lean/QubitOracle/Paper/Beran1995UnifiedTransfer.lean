import QubitOracle.Paper.OneQubitConcreteLocalMinimaxReduction
import QubitOracle.Paper.SourceFaithfulMinimax

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

universe u v

def beranWeightedQuadraticValue
    {D : Type*} [Fintype D] [DecidableEq D]
    (W : Matrix D D Real) (x : LANParameter D) : Real :=
  dotProduct (fun i => x i) (W.mulVec (fun i => x i))

def beranLocalWeightedQuadraticRiskAt
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (W : Matrix D D Real)
    (n : Nat) (T : Statistic (E n) (LANParameter D))
    (h : LANParameter D) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal
    (beranWeightedQuadraticValue W (T.toFun x - h))
      ∂(E n).measure h

/-- Worst local risk over the complete Euclidean ball in Beran's theorem. -/
def beranLocalBallWorstWeightedQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (W : Matrix D D Real)
    (n : Nat) (T : Statistic (E n) (LANParameter D))
    (c : Real) : ENNReal :=
  ⨆ h : LANParameter D, ⨆ (_ : ‖h‖ < c),
    beranLocalWeightedQuadraticRiskAt E W n T h

/-- The growing-ball asymptotic local risk of one estimator sequence. -/
def beranAsymptoticLocalWeightedQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (W : Matrix D D Real)
    (T : (n : Nat) -> Statistic (E n) (LANParameter D)) : ENNReal :=
  Filter.liminf (fun c : Real =>
    Filter.liminf
      (fun n => beranLocalBallWorstWeightedQuadraticRisk E W n (T n) c) atTop) atTop

/-- Beran's exact order of quantifiers: growing local ball, sample-size
`liminf`, then the infimum over all estimators at that sample size. -/
def beranAsymptoticLocalMinimaxWeightedQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (W : Matrix D D Real) : ENNReal :=
  Filter.liminf (fun c : Real =>
    Filter.liminf (fun n =>
      ⨅ T : Statistic (E n) (LANParameter D),
        beranLocalBallWorstWeightedQuadraticRisk E W n T c) atTop) atTop

/-- The minimax functional is below the growing-ball risk of every estimator
sequence.  This is a lattice consequence, not a statistical axiom. -/
theorem beranAsymptoticLocalMinimax_le_allEstimator
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (W : Matrix D D Real)
    (T : (n : Nat) -> Statistic (E n) (LANParameter D)) :
    beranAsymptoticLocalMinimaxWeightedQuadraticRisk E W <=
      beranAsymptoticLocalWeightedQuadraticRisk E W T := by
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall (fun c => by
    apply Filter.liminf_le_liminf
    · exact Filter.Eventually.of_forall (fun n =>
        iInf_le
          (fun Tn : Statistic (E n) (LANParameter D) =>
            beranLocalBallWorstWeightedQuadraticRisk E W n Tn c)
          (T n))
    · isBoundedDefault
    · isBoundedDefault)
  · isBoundedDefault
  · isBoundedDefault

/-- The source-faithful finite-dimensional specialization of Beran (1995),
Theorem 4.1.  It uses the theorem's growing local ball, liminf in sample size,
and infimum over all estimators at each sample size. -/
structure Beran1995Theorem41UnifiedTransfer : Prop where
  sourceFaithful_weighted_transfer :
    forall {D : Type u} [Fintype D] [DecidableEq D]
      (E : Nat -> StatisticalExperiment.{u, v} (LANParameter D))
      (J : Matrix D D Real) (hJ : J.PosDef)
      (score : forall n, (E n).Sample -> LANParameter D)
      (hLAN : IsLANSequence E J score)
      (W : Matrix D D Real) (hW : W.PosSemidef),
      ENNReal.ofReal (Matrix.trace (W * J⁻¹)) <=
        beranAsymptoticLocalMinimaxWeightedQuadraticRisk E W

/-- Rudolf Beran, "The Role of Hajek's Convolution Theorem in Statistical
Theory", Kybernetika 31 (1995), Theorem 4.1, pp. 221--237. -/
axiom beran1995_theorem4_1_unified_external :
  Beran1995Theorem41UnifiedTransfer.{u, v}

/-- Beran's minimax theorem implies the corresponding growing-ball lower
bound for every chosen estimator sequence. -/
theorem beran1995_weightedQuadratic_allEstimator
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (J : Matrix D D Real) (hJ : J.PosDef)
    (score : forall n, (E n).Sample -> LANParameter D)
    (hLAN : IsLANSequence E J score)
    (W : Matrix D D Real) (hW : W.PosSemidef)
    (T : (n : Nat) -> Statistic (E n) (LANParameter D)) :
    ENNReal.ofReal (Matrix.trace (W * J⁻¹)) <=
      beranAsymptoticLocalWeightedQuadraticRisk E W T :=
  (beran1995_theorem4_1_unified_external.sourceFaithful_weighted_transfer
    E J hJ score hLAN W hW).trans
      (beranAsymptoticLocalMinimax_le_allEstimator E W T)

end

end QubitOracle.Paper
