import Mathlib
/-!
# Compact subsequence transfer for invariant adaptive limits
-/

namespace QubitOracle
namespace Paper

open Filter Set

/-- If a sequence stays in a compact set, a continuous identifying map tends
to its target, and a second map is continuous and constant on the identified
fiber, then the second map converges as well. -/
theorem tendsto_of_compact_identified_fiber
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace Z]
    [T2Space Z]
    (K : Set X) (hK : IsCompact K)
    (u : Nat -> X) (hu : ∀ n, u n ∈ K)
    (g : X -> Z) (hgContinuous : Continuous g) (z : Z)
    (hg : Tendsto (fun n => g (u n)) atTop (nhds z))
    (f : X -> Y) (y : Y)
    (hfiber : ∀ x ∈ K, g x = z -> ContinuousAt f x ∧ f x = y) :
    Tendsto (fun n => f (u n)) atTop (nhds y) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  by_contra hnot
  push Not at hnot
  have hfrequent : ∃ᶠ n in atTop,
      epsilon <= dist (f (u n)) y :=
    frequently_atTop.2 fun N => by
      obtain ⟨n, hnN, hn⟩ := hnot N
      exact ⟨n, hnN, hn⟩
  obtain ⟨ns, hns, hbad⟩ :=
    subseq_forall_of_frequently
      (x := fun n : Nat => n) tendsto_id hfrequent
  obtain ⟨x, hxK, phi, hphi, hux⟩ :=
    hK.tendsto_subseq (fun n => hu (ns n))
  have hindex : Tendsto (fun m => ns (phi m)) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have hgsub : Tendsto (fun m => g (u (ns (phi m))))
      atTop (nhds z) :=
    hg.comp hindex
  have hux' : Tendsto (fun m => u (ns (phi m)))
      atTop (nhds x) := by
    simpa [Function.comp_def] using hux
  have hgsubAtX : Tendsto (fun m => g (u (ns (phi m))))
      atTop (nhds (g x)) :=
    hgContinuous.continuousAt.tendsto.comp hux'
  have hgx : g x = z := tendsto_nhds_unique hgsubAtX hgsub
  obtain ⟨hfContinuous, hfxy⟩ := hfiber x hxK hgx
  have hfsub : Tendsto (fun m => f (u (ns (phi m))))
      atTop (nhds y) := by
    rw [← hfxy]
    exact hfContinuous.tendsto.comp hux'
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hfsub) epsilon hepsilon
  have hclose := hN N le_rfl
  have hfar := hbad (phi N)
  linarith

end Paper
end QubitOracle
