import QubitOracle.Paper.InformationFullPathSLLN
import QubitOracle.Paper.InformationLabelWrappers

noncomputable section

namespace QubitOracle.Paper.Label

open Filter MeasureTheory

/-- Supplement equation `SI_info_martingale_SLLN`, specialized to the actual
Ionescu--Tulcea law and including the initial shot.  Conditional centering and
the martingale premises are derived, not assumed. -/
theorem eq_SI_info_martingale_SLLN
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1) :
    MixedInformationFullSLLNStatement q p theta r axis :=
  mixedInformationInnovation_fullStrongLaw_adaptiveTrajectoryMeasure
    q p theta r axis hr haxis

end QubitOracle.Paper.Label
