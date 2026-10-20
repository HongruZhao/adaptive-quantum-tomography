import QubitOracle.AdaptiveDesign.SpherePhaseQuotient
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Smoothness of the actual projection from the standard Euclidean
unit sphere to complex rays. The norm is the physical L2 norm, not the
default maximum norm on a function space. -/
namespace QubitOracle.AdaptiveDesign.SmoothSphereProjection
open QubitOracle.Paper ProjectiveStateGeometry ProjectiveStateTopology
  ProjectiveProjectorEquivalence ProjectiveStateManifold SpherePhaseQuotient
open scoped Manifold ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev PhysicalSpace (d : ℕ) := EuclideanSpace ℂ (Fin (d+1))
abbrev PhysicalSphere (d : ℕ) := Metric.sphere (0 : PhysicalSpace d) 1

instance sphereDimension (d : ℕ) :
    Fact (Module.finrank ℝ (PhysicalSpace d) = (2*d+1)+1) := by
  constructor
  rw [finrank_real_of_complex]
  simp [PhysicalSpace]
  omega

theorem sphere_normSq {d : ℕ} (h : PhysicalSphere d) :
    pureStateNormSq (fun i => h.val i) = 1 := by
  have hn : ‖h.val‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using h.property
  have hs := EuclideanSpace.norm_sq_eq h.val
  simp only [Complex.sq_norm] at hs
  simpa only [pureStateNormSq,hn,one_pow] using hs.symm

def sphereToUnit {d : ℕ} (h : PhysicalSphere d) : UnitVector (Fin (d+1)) :=
  ⟨fun i => h.val i,sphere_normSq h⟩

theorem sphereToUnit_continuous (d : ℕ) : Continuous (@sphereToUnit d) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  apply continuous_pi
  intro i
  exact (EuclideanSpace.proj i).continuous.comp continuous_subtype_val

def sphereRay {d : ℕ} (h : PhysicalSphere d) :
    Projectivization ℂ (Fin (d+1) → ℂ) := unitRay (sphereToUnit h)

theorem sphereRay_continuous (d : ℕ) : Continuous (@sphereRay d) :=
  (unitRay_continuous d).comp (sphereToUnit_continuous d)

theorem sphereRay_smooth (d : ℕ) :
    ContMDiff (𝓡 (2*d+1)) 𝓘(ℝ,Fin d → ℂ) ∞ (@sphereRay d) := by
  intro h
  let r : Fin (d+1) := selectedIndex (rayProjectorHomeomorph d (sphereRay h))
  have hc : sphereRay h ∈ (chartAt (Fin d → ℂ) (sphereRay h)).source :=
    mem_chart_source _ _
  have hr : h.val r ≠ 0 := by
    apply (rayChart_source_formula r (sphereToUnit h).val
      (unitVector_ne_zero (sphereToUnit h))).mp
    exact hc
  apply (contMDiffAt_iff_target_of_mem_source hc).mpr
  refine ⟨(sphereRay_continuous d).continuousAt,?_⟩
  have ha : ContDiffAt ℝ ∞ (fun z : PhysicalSpace d =>
      fun j : Fin d => z (r.succAbove j)/z r) h.val := by
    apply contDiffAt_pi.mpr
    intro j
    have hf : ContDiffAt ℝ ∞ (fun z : PhysicalSpace d => z (r.succAbove j)) h.val :=
      ((EuclideanSpace.proj (𝕜:=ℂ) (r.succAbove j)).restrictScalars ℝ).contDiff.contDiffAt
    have hg : ContDiffAt ℝ ∞ (fun z : PhysicalSpace d => z r) h.val :=
      ((EuclideanSpace.proj (𝕜:=ℂ) r).restrictScalars ℝ).contDiff.contDiffAt
    simpa only [div_eq_mul_inv] using! hf.mul (hg.inv hr)
  have hs := ha.contMDiffAt.comp h (contMDiff_coe_sphere (n:=2*d+1) (m:=∞) h)
  apply hs.congr_of_eventuallyEq
  have he : ∀ᶠ z : PhysicalSphere d in 𝓝 h, z.val r ≠ 0 :=
    (isOpen_ne.preimage ((EuclideanSpace.proj r).continuous.comp
      continuous_subtype_val)).mem_nhds hr
  filter_upwards [he] with z hz
  change rayChart r (sphereRay z) = _
  exact rayChart_formula r (sphereToUnit z).val
    (unitVector_ne_zero (sphereToUnit z)) hz

def spherePhaseProjection {d : ℕ} (h : PhysicalSphere d) :
    UnitPhaseQuotient (ι := Fin (d+1)) := Quotient.mk _ (sphereToUnit h)

theorem spherePhaseProjection_smooth (d : ℕ) :
    ContMDiff (𝓡 (2*d+1)) 𝓘(ℝ,Fin d → ℂ) ∞ (@spherePhaseProjection d) := by
  have hs := (spherePhaseHomeomorph_inverse_smooth d).comp (sphereRay_smooth d)
  convert hs using 1
  funext h
  apply (spherePhaseHomeomorph d).injective
  change sphereRay h = spherePhaseHomeomorph d ((spherePhaseHomeomorph d).symm (sphereRay h))
  exact (Homeomorph.apply_symm_apply _ _).symm

end
end QubitOracle.AdaptiveDesign.SmoothSphereProjection
