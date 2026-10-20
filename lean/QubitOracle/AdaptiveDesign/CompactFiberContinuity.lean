import Mathlib

/-! Convergence through a compact family of frames. A chosen frame need not
converge: continuity and a common value on the limiting projector fiber suffice.
-/
namespace QubitOracle.AdaptiveDesign
open Filter
open scoped Topology

theorem compactFiber_tendsto
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace Y] [T2Space Y]
    [PseudoMetricSpace Z]
    (f : X → Y) (hf : Continuous f) (g : X → Z)
    (truth : Y) (target : Z)
    (hlocal : ∀ x, f x = truth → ContinuousAt g x ∧ g x = target)
    (u : Nat → X) (hu : Tendsto (f ∘ u) atTop (nhds truth)) :
    Tendsto (g ∘ u) atTop (nhds target) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hn
  push_neg at hn
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (g (u n)) target := by
    exact frequently_atTop.2 hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨x, ψ, hψ, hx⟩ := CompactSpace.tendsto_subseq (u ∘ φ)
  have htruth : f x = truth := by
    exact tendsto_nhds_unique (hf.continuousAt.tendsto.comp hx)
      ((hu.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
  have hg := hlocal x htruth
  have hlim : Tendsto (g ∘ (u ∘ φ) ∘ ψ) atTop (nhds target) := by
    simpa only [hg.2] using hg.1.tendsto.comp hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  exact (not_le_of_gt (hN N le_rfl)) (hbad (ψ N))

end QubitOracle.AdaptiveDesign
