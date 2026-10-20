import QubitOracle.Paper.MixedInformationMartingale
import QubitOracle.Paper.ProtocolLabelStrengthening

/-!
# Canonical labels for adaptive information convergence
-/

namespace QubitOracle.Paper.Label

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Supplement equation defining the predictable policy mean and its
matrix-valued martingale innovation. -/
theorem eq_SI_info_martingale
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : SequentialHistory M Y)
    (setting : M) :
    mixedInformationInnovation q r axis history setting =
      QubitOracle.mixedAxisFisher r (axis setting) -
        finitePolicyExpectation q history
          (fun m => QubitOracle.mixedAxisFisher r (axis m)) :=
  rfl

/-- Supplement matrix-martingale SLLN.  All deterministic boundedness and
finite-dimensional lifting are checked; the sole stochastic premise is the
coordinatewise martingale property of the path-space partial sums. -/
theorem eq_SI_info_martingale_SLLN_from_martingale
    {Omega M Y : Type*} [MeasurableSpace Omega]
    [Fintype M]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : ℕ → Omega → SequentialHistory M Y)
    (setting : ℕ → Omega → M)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (hmartingale : ∀ i j, Martingale
      (scalarMartingalePartialSum
        (fun n omega => mixedInformationInnovation q r axis
          (history n omega) (setting n omega) i j))
      filtration mu) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            mixedInformationInnovation q r axis
              (history k omega) (setting k omega))
        atTop (nhds 0) :=
  mixedInformationInnovation_strongLaw
    mu filtration q r axis history setting hr haxis hmartingale

end

end QubitOracle.Paper.Label
