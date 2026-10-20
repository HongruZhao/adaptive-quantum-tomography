import QubitOracle.Paper.SequentialLabelWrappers
import QubitOracle.Paper.MixedProtocolDQM

/-!
# Protocol-specific strengthenings of canonical manuscript labels

Generic implication wrappers remain available in `SequentialLabelWrappers`.
This module assigns the canonical protocol-verification labels only after the
corresponding assumptions have been discharged for the actual qubit model.
-/

namespace QubitOracle.Paper.Label

open scoped BigOperators
open Filter

noncomputable section

/-- Canonical supplement label: S-DQM for the actual mixed-qubit adaptive
projective protocol, not merely a generic implication from a rate premise. -/
theorem eq_SI_protocol_SDQM_verified
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (rounds : ℕ → Finset I)
    (axis : ℕ → Omega → I → Fin 3 → ℝ)
    (theta h : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (hcard : ∀ n, (rounds n).card ≤ n)
    (haxis : ∀ n omega i, i ∈ rounds n →
      QubitOracle.blochNormSq (axis n omega i) ≤ 1) :
    MeasureTheory.TendstoInMeasure mu
      (fun n omega => ∑ i ∈ rounds n,
        mixedProjectiveDQMDefectAt n theta h (axis n omega i))
      atTop 0 :=
  mixedProtocol_SDQM_tendstoInMeasure
    mu rounds axis theta h htheta hcard haxis

end

end QubitOracle.Paper.Label
