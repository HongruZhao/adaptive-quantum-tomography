import QubitOracle.Paper.PureMultilevelNearestPureProjection
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Compact nearest-pure projection estimator

The embedded pure-state set is compact in every finite-dimensional physical
application.  Compactness alone lets us define an exact nearest pure-state
projection of every raw estimator, with no spectral-selection axiom.
-/

namespace QubitOracle.Paper
namespace PureMultilevelCompactNearestProjection

open Filter Set Topology

noncomputable section

variable {Ambient Pure : Type*} [NormedAddCommGroup Ambient]

/-- A compact nonempty embedded pure-state set contains a norm-nearest point
to every ambient raw estimate. -/
theorem exists_nearest_pure_projection
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed)) (raw : Ambient) :
    ∃ projected : Pure, forall candidate : Pure,
      ‖embed projected - raw‖ <= ‖embed candidate - raw‖ := by
  have hnonempty : (Set.range embed).Nonempty :=
    ⟨embed truthPure, ⟨truthPure, rfl⟩⟩
  have hcontinuous : Continuous (fun x : Ambient => dist x raw) :=
    continuous_id.dist continuous_const
  obtain ⟨nearest, hnearestRange, hminimal⟩ :=
    hcompact.exists_isMinOn hnonempty hcontinuous.continuousOn
  obtain ⟨projected, rfl⟩ := hnearestRange
  refine ⟨projected, fun candidate => ?_⟩
  have hcandidate := hminimal ⟨candidate, rfl⟩
  change dist (embed projected) raw <= dist (embed candidate) raw at hcandidate
  simpa only [dist_eq_norm] using hcandidate

/-- A noncomputable but exact nearest-pure projection estimator selected from
the compactness theorem. -/
def compactNearestPureProjection
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed)) (raw : Ambient) : Pure :=
  Classical.choose
    (exists_nearest_pure_projection embed truthPure hcompact raw)

theorem compactNearestPureProjection_is_nearest
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed)) (raw : Ambient)
    (candidate : Pure) :
    ‖embed (compactNearestPureProjection embed truthPure hcompact raw) - raw‖ <=
      ‖embed candidate - raw‖ :=
  Classical.choose_spec
    (exists_nearest_pure_projection embed truthPure hcompact raw) candidate

/-- Apply the exact nearest-pure estimator pointwise to an ambient path. -/
def compactNearestPureProjectionPath
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed))
    (raw : Nat -> Ambient) : Nat -> Pure :=
  fun n => compactNearestPureProjection embed truthPure hcompact (raw n)

theorem compactNearestPureProjectionPath_is_nearest
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed))
    (raw : Nat -> Ambient) (n : Nat) (candidate : Pure) :
    ‖embed (compactNearestPureProjectionPath embed truthPure hcompact raw n) -
        raw n‖ <= ‖embed candidate - raw n‖ :=
  compactNearestPureProjection_is_nearest embed truthPure hcompact
    (raw n) candidate

/-- The compactly selected nearest-pure estimator is consistent whenever the
raw ambient estimator is consistent. -/
theorem compactNearestPureProjectionPath_tendsto
    (embed : Pure -> Ambient) (truthPure : Pure)
    (hcompact : IsCompact (Set.range embed))
    (raw : Nat -> Ambient)
    (hraw : Tendsto raw atTop (nhds (embed truthPure))) :
    Tendsto
      (fun n => embed
        (compactNearestPureProjectionPath embed truthPure hcompact raw n))
      atTop (nhds (embed truthPure)) := by
  exact PureMultilevelNearestPureProjection.nearestPureProjection_tendsto
    embed truthPure raw
    (compactNearestPureProjectionPath embed truthPure hcompact raw)
    (compactNearestPureProjectionPath_is_nearest
      embed truthPure hcompact raw) hraw

end

end PureMultilevelCompactNearestProjection
end QubitOracle.Paper
