import QubitOracle.Paper.FiniteOutcomeResponseDomination
import QubitOracle.Paper.MixedProbabilityFloor

/-!
# Mixed-qubit Born responses dominate localized adaptive paths

At an interior Bloch vector every binary projective Born probability is strictly
positive.  Hence any protocol whose response kernel has the displayed Born masses
satisfies the response-domination and full-path-domination hypotheses used by the
adaptive LAN experiment.
-/

open MeasureTheory ProbabilityTheory

namespace QubitOracle.Paper

universe u w

/-- Interior mixed-qubit Born masses give full-path domination for any predictable design. -/
theorem mixedHybridFullPathDominatedByBase
    {D : Type u} [Fintype D]
    {Action : Type w} [MeasurableSpace Action]
    [MeasurableSpace BinaryOutcome] [MeasurableSingletonClass BinaryOutcome]
    (protocol : PredictableAdaptiveProtocol (Fin 3 -> Real) Action BinaryOutcome)
    (overlap : Action -> Real)
    (localize : Nat -> LANParameter D -> (Fin 3 -> Real))
    (theta0 : Fin 3 -> Real)
    (radius : Real)
    (hoverlap : forall action, |overlap action| <= radius)
    (hradius : radius < 1)
    (hresponse : forall action outcome,
      (protocol.response theta0 action) {outcome} =
        ENNReal.ofReal
          (binaryBornProbability (overlap action) outcome)) :
    HybridFullPathDominatedByBase protocol localize theta0 := by
  apply hybridFullPathDominatedByBase_of_base_singleton_pos
  intro action outcome
  rw [hresponse action outcome]
  exact ENNReal.ofReal_pos.mpr
    (binaryBornProbability_pos (overlap action) radius
      (hoverlap action) hradius outcome)

end QubitOracle.Paper
