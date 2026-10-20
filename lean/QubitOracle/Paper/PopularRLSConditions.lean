import QubitOracle.Paper.SourceFaithfulSelfNormalized

/-!
# Source conditions for adaptive regularized least squares

This file formalizes only the hypotheses used in Theorems 1 and 2 of

Y. Abbasi-Yadkori, D. Pal, and C. Szepesvari,
*Improved Algorithms for Linear Stochastic Bandits*,
Advances in Neural Information Processing Systems 24 (2011), 2312--2320.

Official source:
https://proceedings.neurips.cc/paper_files/paper/2011/file/e1d5be1c7f2f456670de3d53c7b54f4a-Paper.pdf

The external confidence theorem is deliberately not reproved here.  A paper
application must construct this structure and may then cite the source result.
-/

namespace QubitOracle.Paper.PopularRLSConditions

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- Euclidean norm used by the finite-dimensional source theorem.  It is
defined explicitly to avoid confusing it with the sup norm on a function
type. -/
def finiteEuclideanNorm {d : Nat} (x : Fin d -> Real) : Real :=
  Real.sqrt (∑ j, x j ^ 2)

/-- Exact assumption package used by the adaptive least-squares confidence
ellipsoid in Abbasi-Yadkori--Pal--Szepesvari (2011), Theorems 1 and 2.

`martingaleData` contains the filtration, predictable regressors, adapted
noise, conditional centering, and conditional `R`-sub-Gaussian MGF bound.
The remaining fields record the linear observation model, ridge parameter,
parameter radius, bounded features, and confidence level. -/
structure AbbasiYadkoriPalSzepesvari2011Conditions
    (Omega : Type*) [MeasurableSpace Omega]
    (d : Nat) (mu : Measure Omega) where
  noiseScale : Real
  noiseScale_nonnegative : 0 <= noiseScale
  martingaleData :
    SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu noiseScale
  thetaStar : Fin d -> Real
  observation : Nat -> Omega -> Real
  linearObservation : forall k,
    observation (k + 1) =ᵐ[mu] fun omega =>
      dotProduct (martingaleData.regressor k omega) thetaStar +
        martingaleData.noise (k + 1) omega
  regularization : Real
  regularization_positive : 0 < regularization
  parameterRadius : Real
  parameterRadius_nonnegative : 0 <= parameterRadius
  parameter_bounded : finiteEuclideanNorm thetaStar <= parameterRadius
  featureRadius : Real
  featureRadius_nonnegative : 0 <= featureRadius
  feature_bounded : forall k,
    ∀ᵐ omega ∂mu,
      finiteEuclideanNorm (martingaleData.regressor k omega) <= featureRadius
  confidenceLevel : Real
  confidenceLevel_positive : 0 < confidenceLevel
  confidenceLevel_lt_one : confidenceLevel < 1

/-- Paper-specific assumptions needed in addition to the cited confidence
theorem to turn a self-normalized ellipsoid into controller consistency.  They
are not hypotheses of the external theorem and are kept separate for audit. -/
structure PaperRLSApplicationConditions
    (expectedExploration : Nat -> Real) where
  expectedExploration_positive :
    ∀ᶠ n in Filter.atTop, 0 < expectedExploration n
  persistentExploration :
    Filter.Tendsto
      (fun n : Nat => Real.log (n : Real) / expectedExploration n)
      Filter.atTop (nhds 0)
  vanishingExplorationFraction :
    Filter.Tendsto
      (fun n : Nat => expectedExploration n / (n : Real))
      Filter.atTop (nhds 0)

end

end QubitOracle.Paper.PopularRLSConditions
