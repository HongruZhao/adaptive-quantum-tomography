import QubitOracle.Paper.PopularRLSConditions
import QubitOracle.Paper.QubitRLSReduction

/-!
# One-qubit reduction of self-normalized RLS confidence

This file uses only the clean source-faithful RLS contracts.  It does not
assert the Abbasi-Yadkori--Pal--Szepesvari confidence theorem as an axiom.
Instead, it separates:

* the exact Theorem 1 martingale hypotheses, represented by the existing
  `SelfNormalizedMartingaleData` contract;
* elementary one-qubit Born-regression facts proved here; and
* a deterministic reduction from a supplied self-normalized confidence bound
  and persistent-excitation coercivity to Euclidean RLS consistency.

Conditional sub-Gaussianity remains an explicit field of the source contract.
No appeal to Hoeffding's lemma is made.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

/-! ## Exact source-theorem contract specialized to one qubit -/

/-- Prop-valued one-qubit specialization of the hypotheses of
Abbasi-Yadkori--Pal--Szepesvari (2011), Theorem 1.

The parameter `martingaleData` is the clean source-faithful contract.  It
contains exactly a filtration, `Fin 3` predictable regressors, adapted scalar
noise, conditional centering, and the conditional `R`-sub-Gaussian MGF bound.
This wrapper adds the project-specific fact that the regressors are unit Bloch
axes and records the positive-definite initial Gram matrix used by the
self-normalized norm.

It is a hypothesis package only, not an assertion of the source theorem's
conclusion. -/
structure OneQubitAPSTheoremOneContract
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (noiseScale : Real)
    (martingaleData :
      SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
        Omega 3 mu noiseScale)
    (initialGram : Matrix (Fin 3) (Fin 3) Real) : Prop where
  noiseScale_nonnegative : 0 <= noiseScale
  unit_axes : ∀ k, ∀ᵐ omega ∂mu,
    QubitOracle.blochNormSq (martingaleData.regressor k omega) = 1
  initialGram_posDef : initialGram.PosDef

/-! ## Elementary binary Born regression -/

/-- Binary response used by one-qubit least squares: `false` is `-1` and
`true` is `+1`. -/
def qubitBinaryRLSResponse : Bool -> Real
  | false => -1
  | true => 1

/-- Binary Born law with scalar Bloch overlap `overlap`. -/
def qubitBinaryBornProbability (overlap : Real) : Bool -> Real
  | false => (1 - overlap) / 2
  | true => (1 + overlap) / 2

/-- Expectation under the binary Born law after conditioning on the history,
so that `overlap` is fixed. -/
def qubitBinaryBornExpectation
    (overlap : Real) (f : Bool -> Real) : Real :=
  qubitBinaryBornProbability overlap false * f false +
    qubitBinaryBornProbability overlap true * f true

/-- Least-squares residual for the signed binary response. -/
def qubitBinaryRLSResidual (overlap : Real) (outcome : Bool) : Real :=
  qubitBinaryRLSResponse outcome - overlap

/-- The signed response has absolute value exactly one. -/
@[simp]
theorem abs_qubitBinaryRLSResponse (outcome : Bool) :
    |qubitBinaryRLSResponse outcome| = 1 := by
  cases outcome <;> norm_num [qubitBinaryRLSResponse]

/-- In particular, the signed response is bounded by one. -/
theorem abs_qubitBinaryRLSResponse_le_one (outcome : Bool) :
    |qubitBinaryRLSResponse outcome| <= 1 := by
  rw [abs_qubitBinaryRLSResponse]

/-- The two Born probabilities sum to one. -/
theorem qubitBinaryBornProbability_sum (overlap : Real) :
    qubitBinaryBornProbability overlap false +
      qubitBinaryBornProbability overlap true = 1 := by
  simp [qubitBinaryBornProbability]
  ring

/-- If the Bloch overlap lies in `[-1,1]`, each Born weight is nonnegative. -/
theorem qubitBinaryBornProbability_nonnegative
    (overlap : Real) (hlower : -1 <= overlap) (hupper : overlap <= 1)
    (outcome : Bool) :
    0 <= qubitBinaryBornProbability overlap outcome := by
  cases outcome <;> simp [qubitBinaryBornProbability] <;> linarith

/-- If the Bloch overlap lies in `[-1,1]`, each Born weight is at most one. -/
theorem qubitBinaryBornProbability_le_one
    (overlap : Real) (hlower : -1 <= overlap) (hupper : overlap <= 1)
    (outcome : Bool) :
    qubitBinaryBornProbability overlap outcome <= 1 := by
  cases outcome <;> simp [qubitBinaryBornProbability] <;> linarith

/-- The signed Born response has conditional mean equal to the Bloch overlap. -/
theorem qubitBinaryBornResponse_mean (overlap : Real) :
    qubitBinaryBornExpectation overlap qubitBinaryRLSResponse = overlap := by
  simp [qubitBinaryBornExpectation, qubitBinaryBornProbability,
    qubitBinaryRLSResponse]
  ring

/-- The RLS residual is exactly centered under the conditional binary Born
law.  Since `overlap` is fixed by the past, this is the project-specific
conditional-centering calculation. -/
theorem qubitBinaryBornResidual_centered (overlap : Real) :
    qubitBinaryBornExpectation overlap
      (qubitBinaryRLSResidual overlap) = 0 := by
  simp [qubitBinaryBornExpectation, qubitBinaryBornProbability,
    qubitBinaryRLSResidual, qubitBinaryRLSResponse]
  ring

/-- Pointwise-in-history form of conditional centering for an adaptive qubit
axis.  The actual measure-theoretic conditional-law identification is kept
separate from this finite Born-kernel calculation. -/
theorem adaptiveQubitBinaryBornResidual_conditionallyCentered
    {Omega : Type*} (axis : Nat -> Omega -> Fin 3 -> Real)
    (theta : Fin 3 -> Real) (k : Nat) (omega : Omega) :
    qubitBinaryBornExpectation
        (QubitOracle.blochDot (axis k omega) theta)
        (qubitBinaryRLSResidual
          (QubitOracle.blochDot (axis k omega) theta)) = 0 :=
  qubitBinaryBornResidual_centered
    (QubitOracle.blochDot (axis k omega) theta)

/-- Every residual lies in the translated interval
`[-1-overlap, 1-overlap]`. -/
theorem qubitBinaryRLSResidual_interval
    (overlap : Real) (outcome : Bool) :
    -1 - overlap <= qubitBinaryRLSResidual overlap outcome ∧
      qubitBinaryRLSResidual overlap outcome <= 1 - overlap := by
  cases outcome <;>
    simp [qubitBinaryRLSResidual, qubitBinaryRLSResponse] <;> constructor <;>
      linarith

/-- The deterministic residual interval has length exactly two. -/
theorem qubitBinaryRLSResidual_interval_length (overlap : Real) :
    (1 - overlap) - (-1 - overlap) = 2 := by
  ring

/-- The explicit Euclidean feature norm equals one for a unit Bloch axis. -/
theorem finiteEuclideanNorm_eq_one_of_unitBlochAxis
    (axis : Fin 3 -> Real)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    PopularRLSConditions.finiteEuclideanNorm axis = 1 := by
  unfold PopularRLSConditions.finiteEuclideanNorm
  change Real.sqrt (QubitOracle.blochNormSq axis) = 1
  rw [haxis]
  norm_num

/-- Thus every unit qubit design axis satisfies the source feature bound with
radius one. -/
theorem finiteEuclideanNorm_le_one_of_unitBlochAxis
    (axis : Fin 3 -> Real)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    PopularRLSConditions.finiteEuclideanNorm axis <= 1 := by
  rw [finiteEuclideanNorm_eq_one_of_unitBlochAxis axis haxis]

/-- The one-qubit source contract supplies the source theorem's bounded-feature
condition with feature radius one. -/
theorem oneQubitAPS_featureRadius_one
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (noiseScale : Real)
    (martingaleData :
      SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData
        Omega 3 mu noiseScale)
    (initialGram : Matrix (Fin 3) (Fin 3) Real)
    (h : OneQubitAPSTheoremOneContract
      mu noiseScale martingaleData initialGram) :
    ∀ k, ∀ᵐ omega ∂mu,
      PopularRLSConditions.finiteEuclideanNorm
        (martingaleData.regressor k omega) <= 1 := by
  intro k
  filter_upwards [h.unit_axes k] with omega hunit
  exact finiteEuclideanNorm_le_one_of_unitBlochAxis
    (martingaleData.regressor k omega) hunit

/-! ## Deterministic self-normalized confidence reduction -/

/-- Error of a `Fin 3` RLS estimate in Bloch coordinates. -/
def oneQubitRLSError
    (estimate truth : Fin 3 -> Real) : Fin 3 -> Real :=
  fun j => estimate j - truth j

/-- Quadratic energy induced by a `3 x 3` Gram matrix. -/
def oneQubitGramEnergy
    (gram : Matrix (Fin 3) (Fin 3) Real)
    (x : Fin 3 -> Real) : Real :=
  QubitOracle.blochDot x (gram.mulVec x)

/-- A supplied self-normalized confidence conclusion.  This is a deterministic
premise, not an axiom asserting the external probability theorem. -/
structure OneQubitSelfNormalizedConfidence
    (gram : Matrix (Fin 3) (Fin 3) Real)
    (estimate truth : Fin 3 -> Real) (radius : Real) : Prop where
  radius_nonnegative : 0 <= radius
  confidence_bound :
    oneQubitGramEnergy gram (oneQubitRLSError estimate truth) <= radius ^ 2

/-- Persistent excitation expressed as Euclidean coercivity.  For a symmetric
Gram matrix this is precisely the usable content of a lower-eigenvalue bound
`lambda_min(gram) >= excitation`. -/
structure OneQubitPersistentExcitation
    (gram : Matrix (Fin 3) (Fin 3) Real)
    (excitation : Real) : Prop where
  excitation_positive : 0 < excitation
  euclidean_coercive : ∀ x : Fin 3 -> Real,
    excitation * QubitOracle.blochNormSq x <= oneQubitGramEnergy gram x

/-- Squared Euclidean error is bounded by confidence radius squared divided by
the persistent-excitation level. -/
theorem oneQubitRLSSquaredEuclideanError_le
    (gram : Matrix (Fin 3) (Fin 3) Real)
    (estimate truth : Fin 3 -> Real) (radius excitation : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      gram estimate truth radius)
    (hExcitation : OneQubitPersistentExcitation gram excitation) :
    QubitOracle.blochNormSq (oneQubitRLSError estimate truth) <=
      radius ^ 2 / excitation := by
  have hchain :
      excitation * QubitOracle.blochNormSq
          (oneQubitRLSError estimate truth) <= radius ^ 2 :=
    (hExcitation.euclidean_coercive
      (oneQubitRLSError estimate truth)).trans hConfidence.confidence_bound
  apply (le_div_iff₀ hExcitation.excitation_positive).2
  simpa [mul_comm] using hchain

/-- Explicit Euclidean RLS error bound obtained by taking square roots. -/
theorem oneQubitRLSEuclideanError_le
    (gram : Matrix (Fin 3) (Fin 3) Real)
    (estimate truth : Fin 3 -> Real) (radius excitation : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      gram estimate truth radius)
    (hExcitation : OneQubitPersistentExcitation gram excitation) :
    PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError estimate truth) <=
      Real.sqrt (radius ^ 2 / excitation) := by
  have hsqrt := Real.sqrt_le_sqrt
    (oneQubitRLSSquaredEuclideanError_le
      gram estimate truth radius excitation hConfidence hExcitation)
  simpa only [Function.comp_def,
    PopularRLSConditions.finiteEuclideanNorm,
    QubitOracle.blochNormSq, Real.sqrt_zero] using hsqrt

/-- Deterministic RLS consistency: if the confidence-radius-to-excitation
ratio vanishes, then the squared Euclidean Bloch error vanishes. -/
theorem oneQubitRLSSquaredEuclideanError_tendsto_zero
    (gram : Nat -> Matrix (Fin 3) (Fin 3) Real)
    (estimate : Nat -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (radius excitation : Nat -> Real)
    (hConfidence : ∀ n, OneQubitSelfNormalizedConfidence
      (gram n) (estimate n) truth (radius n))
    (hExcitation : ∀ n, OneQubitPersistentExcitation
      (gram n) (excitation n))
    (hRate : Tendsto
      (fun n => radius n ^ 2 / excitation n) atTop (nhds 0)) :
    Tendsto
      (fun n => QubitOracle.blochNormSq
        (oneQubitRLSError (estimate n) truth)) atTop (nhds 0) := by
  have hnonnegative : ∀ n,
      0 <= QubitOracle.blochNormSq
        (oneQubitRLSError (estimate n) truth) := by
    intro n
    unfold QubitOracle.blochNormSq
    exact Finset.sum_nonneg fun j _ => sq_nonneg
      (oneQubitRLSError (estimate n) truth j)
  have hupper : ∀ n,
      QubitOracle.blochNormSq
          (oneQubitRLSError (estimate n) truth) <=
        radius n ^ 2 / excitation n := by
    intro n
    exact oneQubitRLSSquaredEuclideanError_le
      (gram n) (estimate n) truth (radius n) (excitation n)
        (hConfidence n) (hExcitation n)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper) hRate

/-- Consequently, the ordinary finite-dimensional Euclidean error converges
to zero. -/
theorem oneQubitRLSEuclideanError_tendsto_zero
    (gram : Nat -> Matrix (Fin 3) (Fin 3) Real)
    (estimate : Nat -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (radius excitation : Nat -> Real)
    (hConfidence : ∀ n, OneQubitSelfNormalizedConfidence
      (gram n) (estimate n) truth (radius n))
    (hExcitation : ∀ n, OneQubitPersistentExcitation
      (gram n) (excitation n))
    (hRate : Tendsto
      (fun n => radius n ^ 2 / excitation n) atTop (nhds 0)) :
    Tendsto
      (fun n => PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError (estimate n) truth)) atTop (nhds 0) := by
  have hsquared := oneQubitRLSSquaredEuclideanError_tendsto_zero
    gram estimate truth radius excitation hConfidence hExcitation hRate
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquared
  simpa only [Function.comp_def,
    PopularRLSConditions.finiteEuclideanNorm,
    QubitOracle.blochNormSq, Real.sqrt_zero] using hsqrt

end

end QubitOracle.Paper
