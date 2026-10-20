import QubitOracle.Paper.OneQubitLocalContinuousFrame

/-!
# Eventual closure of the local continuous-frame domain

For a coordinatewise consistent pilot, both denominators used by the local
Gram--Schmidt frame converge to their values at the truth.  Strict positivity
at the truth therefore makes the local frame well-defined eventually.  This
removes the eventual-domain premise from the pilot-frame constructor.
-/

open Filter

namespace QubitOracle.Paper

private theorem tendsto_blochNormSq_of_coordinatewise_local
    {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j))) :
    Tendsto (fun n => blochNormSq (xHat n)) atTop (nhds (blochNormSq r)) := by
  have hxWhole : Tendsto xHat atTop (nhds r) := tendsto_pi_nhds.2 hx
  have hContinuous : Continuous (fun x : Fin 3 → ℝ => blochNormSq x) := by
    unfold blochNormSq
    fun_prop
  exact hContinuous.continuousAt.tendsto.comp hxWhole

private theorem tendsto_blochDot_fixed_left_local
    (b : Fin 3 → ℝ) {yHat : ℕ → Fin 3 → ℝ} {y : Fin 3 → ℝ}
    (hy : ∀ j, Tendsto (fun n => yHat n j) atTop (nhds (y j))) :
    Tendsto (fun n => blochDot b (yHat n)) atTop (nhds (blochDot b y)) := by
  have hyWhole : Tendsto yHat atTop (nhds y) := tendsto_pi_nhds.2 hy
  have hContinuous : Continuous (fun z : Fin 3 → ℝ => blochDot b z) := by
    unfold blochDot
    fun_prop
  exact hContinuous.continuousAt.tendsto.comp hyWhole

private theorem tendsto_localNormalizedBlochDirection_entry_local
    {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j)))
    (hrPositive : 0 < blochNormSq r) (j : Fin 3) :
    Tendsto (fun n => localNormalizedBlochDirection (xHat n) j) atTop
      (nhds (localNormalizedBlochDirection r j)) := by
  exact localNormalizedBlochDirection_entry_tendsto xHat r hx hrPositive j

private theorem tendsto_localFrameFirstResidual_entry_local
    (b : Fin 3 → ℝ) {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j)))
    (hrPositive : 0 < blochNormSq r) (j : Fin 3) :
    Tendsto (fun n => localFrameFirstResidual b (xHat n) j) atTop
      (nhds (localFrameFirstResidual b r j)) := by
  have hNormalized : ∀ i,
      Tendsto (fun n => localNormalizedBlochDirection (xHat n) i) atTop
        (nhds (localNormalizedBlochDirection r i)) :=
    fun i => tendsto_localNormalizedBlochDirection_entry_local hx hrPositive i
  have hProjection := tendsto_blochDot_fixed_left_local b hNormalized
  simpa [localFrameFirstResidual] using
    tendsto_const_nhds.sub (hProjection.mul (hNormalized j))

/-- Both squared frame denominators converge to their values at the truth. -/
theorem localContinuousFrame_denominator_convergence
    (b : Fin 3 → ℝ) {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j)))
    (hrPositive : 0 < blochNormSq r) :
    Tendsto (fun n => blochNormSq (xHat n)) atTop (nhds (blochNormSq r)) ∧
      Tendsto (fun n => blochNormSq (localFrameFirstResidual b (xHat n))) atTop
        (nhds (blochNormSq (localFrameFirstResidual b r))) := by
  constructor
  · exact tendsto_blochNormSq_of_coordinatewise_local hx
  · apply tendsto_blochNormSq_of_coordinatewise_local
    intro j
    exact tendsto_localFrameFirstResidual_entry_local b hx hrPositive j

/-- Coordinatewise consistency and strict positivity at the truth imply that
the local Gram--Schmidt frame is defined eventually. -/
theorem eventually_localContinuousFrameDomain
    (b : Fin 3 → ℝ) {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j)))
    (hrPositive : 0 < blochNormSq r)
    (hSeedPositive : 0 < blochNormSq (localFrameFirstResidual b r)) :
    ∀ᶠ n in atTop, LocalContinuousFrameDomain b (xHat n) := by
  obtain ⟨hRadial, hTangent⟩ :=
    localContinuousFrame_denominator_convergence b hx hrPositive
  have hRadialEventually : ∀ᶠ n in atTop, 0 < blochNormSq (xHat n) := by
    exact hRadial.eventually (Ioi_mem_nhds hrPositive)
  have hTangentEventually :
      ∀ᶠ n in atTop, 0 < blochNormSq (localFrameFirstResidual b (xHat n)) := by
    exact hTangent.eventually (Ioi_mem_nhds hSeedPositive)
  filter_upwards [hRadialEventually, hTangentEventually] with n hnRadial hnTangent
  exact
    { radial_denominator_pos := hnRadial
      tangent_denominator_pos := hnTangent }

/-- The preceding result expressed through the frame module's explicit
nonparallel-seed predicate. -/
theorem eventually_localContinuousFrameDomain_of_nonparallel
    (b : Fin 3 → ℝ) {xHat : ℕ → Fin 3 → ℝ} {r : Fin 3 → ℝ}
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j)))
    (hrPositive : 0 < blochNormSq r)
    (hSeed : LocalFrameSeedNonparallelAt b r) :
    ∀ᶠ n in atTop, LocalContinuousFrameDomain b (xHat n) := by
  apply eventually_localContinuousFrameDomain b hx hrPositive
  simpa only [LocalFrameSeedNonparallelAt] using hSeed

/-- Strengthened deterministic pilot constructor.  Eventual membership in the
local chart is now a consequence, rather than a caller-supplied premise. -/
noncomputable def localContinuousFramePilot_of_coordinatewise
    (b r : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ)
    (hrUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j))) :
    QubitPilotFrameConvergence r := by
  have hrPositive : 0 < blochNormSq r := by
    simpa [hrUnit] using (show (0 : ℝ) < 1 from zero_lt_one)
  have hEventuallyDomain :
      ∀ᶠ n in atTop, LocalContinuousFrameDomain b (xHat n) :=
    eventually_localContinuousFrameDomain_of_nonparallel b hx hrPositive hSeed
  apply localContinuousFramePilot <;> assumption

namespace Label

/-- Paper-label wrapper for the concrete local-domain closure reduction.  Its
premises contain no assumed frame-domain convergence. -/
noncomputable def lem_SI_local_frame_domain_closure_qubit_reduction
    (b r : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ)
    (hrUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (r j))) :
    QubitPilotFrameConvergence r :=
  localContinuousFramePilot_of_coordinatewise b r xHat hrUnit hSeed hx

end Label
end QubitOracle.Paper
