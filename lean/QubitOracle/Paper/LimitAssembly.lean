import Mathlib.Topology.Algebra.Module.Basic

/-!
# Deterministic assembly of adaptive information limits

The stochastic theorems establish limits for the full and deleted information
terms.  The subtraction step producing the retained-information limit is a
pure topological-vector-space argument checked here.
-/

namespace QubitOracle
namespace Paper

open Filter Topology

/-- If `retained = full - deleted`, the full term tends to `target`, and the
deleted term tends to zero, then the retained term has the same limit. -/
theorem retainedLimit_of_fullLimit_of_deletedLimit
    {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (full deleted retained : ℕ → E) (target : E)
    (decompose : ∀ n, retained n = full n - deleted n)
    (hfull : Tendsto full atTop (𝓝 target))
    (hdeleted : Tendsto deleted atTop (𝓝 0)) :
    Tendsto retained atTop (𝓝 target) := by
  have hfun : retained = fun n => full n - deleted n := funext decompose
  rw [hfun]
  simpa using hfull.sub hdeleted

/-- A perturbation tending to zero does not change a sequence limit. -/
theorem addVanishing_preserves_limit
    {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    (main error : ℕ → E) (target : E)
    (hmain : Tendsto main atTop (𝓝 target))
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun n => main n + error n) atTop (𝓝 target) := by
  simpa using hmain.add herror

end Paper
end QubitOracle
