import QubitOracle.Paper.PopularRLSConditions

/-!
# Source-faithful adaptive RLS confidence ellipsoid

This module records the determinant-form confidence ellipsoid in Theorem 2 of

Y. Abbasi-Yadkori, D. Pal, and C. Szepesvari,
*Improved Algorithms for Linear Stochastic Bandits*, NeurIPS 24 (2011),
2312--2320.

Official source:
https://proceedings.neurips.cc/paper_files/paper/2011/file/e1d5be1c7f2f456670de3d53c7b54f4a-Paper.pdf

The theorem is intentionally imported as one explicit scientific axiom.  Its
assumptions and conclusion are represented below; no qubit-specific claim is
included in the axiom.
-/

namespace QubitOracle.Paper.PopularRLSConditions

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The source regularizer `lambda I`. -/
def aps2011Theorem2Regularizer (d : Nat) (regularization : Real) :
    Matrix (Fin d) (Fin d) Real :=
  regularization • (1 : Matrix (Fin d) (Fin d) Real)

/-- The regularized design matrix
`V_t = lambda I + sum_{k < t} X_k X_k^T`. -/
def aps2011Theorem2Gram
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (regularization : Real) (t : Nat) (omega : Omega) :
    Matrix (Fin d) (Fin d) Real :=
  SourceFaithfulSelfNormalized.regularizedGram data
    (aps2011Theorem2Regularizer d regularization) t omega

/-- The response moment `sum_{k < t} X_k Y_{k+1}`. -/
def aps2011Theorem2ResponseMoment
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (observation : Nat -> Omega -> Real)
    (t : Nat) (omega : Omega) : Fin d -> Real :=
  ∑ k ∈ Finset.range t,
    observation (k + 1) omega • data.regressor k omega

/-- The source's ridge least-squares estimator. -/
def aps2011Theorem2Estimator
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (observation : Nat -> Omega -> Real)
    (regularization : Real) (t : Nat) (omega : Omega) : Fin d -> Real :=
  Matrix.mulVec (aps2011Theorem2Gram data regularization t omega)⁻¹
    (aps2011Theorem2ResponseMoment data observation t omega)

/-- Estimation error `thetaHat_t - thetaStar`. -/
def aps2011Theorem2Error
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (regularization : Real) (t : Nat) (omega : Omega) : Fin d -> Real :=
  fun j =>
    aps2011Theorem2Estimator data observation regularization t omega j -
      thetaStar j

/-- Matrix norm `||thetaHat_t - thetaStar||_{V_t}`. -/
def aps2011Theorem2WeightedError
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (regularization : Real) (t : Nat) (omega : Omega) : Real :=
  Real.sqrt
    (SourceFaithfulSelfNormalized.weightedNormSq
      (aps2011Theorem2Gram data regularization t omega)
      (aps2011Theorem2Error data thetaStar observation
        regularization t omega))

/-- Exact determinant radius in Abbasi-Yadkori--Pal--Szepesvari (2011),
Theorem 2. -/
def aps2011Theorem2Radius
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (regularization parameterRadius delta : Real)
    (t : Nat) (omega : Omega) : Real :=
  R * Real.sqrt
      (2 * Real.log
        ((Real.sqrt
            (Matrix.det (aps2011Theorem2Gram data regularization t omega)) *
          (Real.sqrt
            (Matrix.det
              (aps2011Theorem2Regularizer d regularization)))⁻¹) / delta)) +
    Real.sqrt regularization * parameterRadius

/-- Event on which the confidence ellipsoid holds simultaneously for every
time `t`. -/
def aps2011Theorem2GoodEvent
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (regularization parameterRadius delta : Real) : Set Omega :=
  {omega | forall t : Nat,
    aps2011Theorem2WeightedError data thetaStar observation
        regularization t omega <=
      aps2011Theorem2Radius data regularization parameterRadius delta t omega}

/-- Exact high-probability conclusion of the determinant-form confidence
ellipsoid. -/
def APS2011Theorem2ConfidenceEllipsoidContract
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (regularization parameterRadius delta : Real) : Prop :=
  ENNReal.ofReal (1 - delta) <=
    mu (aps2011Theorem2GoodEvent data thetaStar observation
      regularization parameterRadius delta)

/-- **External scientific axiom: Abbasi-Yadkori--Pal--Szepesvari (2011),
Theorem 2, determinant-form confidence ellipsoid.**

For predictable finite-dimensional regressors, adapted conditionally
`R`-sub-Gaussian noise, the exact linear observation model, positive ridge
regularization, a bounded true parameter, and `0 < delta < 1`, the displayed
RLS ellipsoid contains the true parameter simultaneously at every time with
probability at least `1 - delta`.
-/
axiom abbasiYadkoriPalSzepesvari2011_theorem2_confidenceEllipsoid_external
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} [IsProbabilityMeasure mu] {R : Real}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
      Omega d mu R)
    (hR : 0 <= R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (hLinearObservation : forall k,
      observation (k + 1) =ᵐ[mu] fun omega =>
        dotProduct (data.regressor k omega) thetaStar +
          data.noise (k + 1) omega)
    (regularization : Real) (hRegularization : 0 < regularization)
    (parameterRadius : Real) (hParameterRadius : 0 <= parameterRadius)
    (hParameterBound : finiteEuclideanNorm thetaStar <= parameterRadius)
    (delta : Real) (hDelta0 : 0 < delta) (hDelta1 : delta < 1) :
    APS2011Theorem2ConfidenceEllipsoidContract data thetaStar observation
      regularization parameterRadius delta

/-- The already-formalized general RLS hypothesis package instantiates the
newly approved source axiom without adding another scientific assumption. -/
theorem abbasiYadkoriPalSzepesvari2011_theorem2_of_conditions
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} [IsProbabilityMeasure mu]
    (conditions : AbbasiYadkoriPalSzepesvari2011Conditions Omega d mu) :
    APS2011Theorem2ConfidenceEllipsoidContract
      conditions.martingaleData conditions.thetaStar conditions.observation
      conditions.regularization conditions.parameterRadius
      conditions.confidenceLevel :=
  abbasiYadkoriPalSzepesvari2011_theorem2_confidenceEllipsoid_external
    conditions.martingaleData conditions.noiseScale_nonnegative
    conditions.thetaStar conditions.observation conditions.linearObservation
    conditions.regularization conditions.regularization_positive
    conditions.parameterRadius conditions.parameterRadius_nonnegative
    conditions.parameter_bounded conditions.confidenceLevel
    conditions.confidenceLevel_positive conditions.confidenceLevel_lt_one

end

end QubitOracle.Paper.PopularRLSConditions
