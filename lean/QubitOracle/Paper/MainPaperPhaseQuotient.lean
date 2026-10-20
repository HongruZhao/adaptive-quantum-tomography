import QubitOracle.AdaptiveDesign.ProjectiveStateManifold

set_option autoImplicit false

/-! Definition A.1: the actual quotient topology on unit vectors modulo
phase, equipped with the ordinary homogeneous-coordinate smooth atlas.
Its identification with matrix-defined pure projectors is a diffeomorphism.
The quotient topology is not defined by transporting the target topology. -/
namespace QubitOracle.Paper.MainPaperPhaseQuotient
open QubitOracle.Paper ProjectiveStateGeometry QubitOracle.AdaptiveDesign
open ProjectiveProjectorEquivalence ProjectiveStateTopology AffineProjectorCharts ProjectiveStateManifold
open scoped Manifold ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

instance phaseCompact (d : ℕ) : CompactSpace (UnitPhaseQuotient (ι := Fin (d+1))) := by
  infer_instance

theorem phaseClassProjector_continuous (d : ℕ) : Continuous (phaseClassProjector d) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun h : UnitVector (Fin (d+1)) => rankOneDensity h.val)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).comp continuous_subtype_val).mul
    (((continuous_apply j).comp continuous_subtype_val).star)

def phaseProjectorHomeomorph (d : ℕ) :
    UnitPhaseQuotient (ι := Fin (d+1)) ≃ₜ PureProjector d :=
  (phaseClassProjectorEquiv d).toHomeomorphOfContinuousClosed
    (phaseClassProjector_continuous d) (phaseClassProjector_continuous d).isClosedMap

def phaseChart {d : ℕ} (r : Fin (d+1)) :
    OpenPartialHomeomorph (UnitPhaseQuotient (ι := Fin (d+1))) (Fin d → ℂ) :=
  (phaseProjectorHomeomorph d).toOpenPartialHomeomorph.trans (chart r)

instance phaseChartedSpace (d : ℕ) :
    ChartedSpace (Fin d → ℂ) (UnitPhaseQuotient (ι := Fin (d+1))) where
  atlas := Set.range (@phaseChart d)
  chartAt p := phaseChart (selectedIndex (phaseProjectorHomeomorph d p))
  mem_chart_source p := ⟨Set.mem_univ p,selectedIndex_source _⟩
  chart_mem_atlas p := ⟨selectedIndex (phaseProjectorHomeomorph d p),rfl⟩

theorem phase_transition_smooth {d : ℕ} (r s : Fin (d+1)) :
    ContDiffOn ℝ ∞ ((phaseChart r).symm.trans (phaseChart s))
      ((phaseChart r).symm.trans (phaseChart s)).source := by
  change ContDiffOn ℝ ∞
    (fun u => coordinates s (phaseProjectorHomeomorph d
      ((phaseProjectorHomeomorph d).symm (inverseChart r u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth r s).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp [OpenPartialHomeomorph.trans_source,phaseChart,chart]

instance phaseManifold (d : ℕ) :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (UnitPhaseQuotient (ι := Fin (d+1))) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨r,rfl⟩ ⟨s,rfl⟩
  simpa using phase_transition_smooth r s

theorem phaseToProjector_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (phaseProjectorHomeomorph d) := by
  apply contMDiff_iff.mpr
  refine ⟨(phaseProjectorHomeomorph d).continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞
    (fun u => coordinates (selectedIndex y) (phaseProjectorHomeomorph d
      ((phaseProjectorHomeomorph d).symm
        (inverseChart (selectedIndex (phaseProjectorHomeomorph d x)) u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth (selectedIndex (phaseProjectorHomeomorph d x))
    (selectedIndex y)).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
  change (u ∈ (phaseChart (selectedIndex (phaseProjectorHomeomorph d x))).target ∧
    phaseProjectorHomeomorph d
      ((phaseChart (selectedIndex (phaseProjectorHomeomorph d x))).symm u) ∈
      (chart (selectedIndex y)).source) ↔ _
  simp [phaseChart,OpenPartialHomeomorph.trans_target,chart]

theorem projectorToPhase_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (phaseProjectorHomeomorph d).symm := by
  apply contMDiff_iff.mpr
  refine ⟨(phaseProjectorHomeomorph d).symm.continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞
    (fun u => coordinates (selectedIndex (phaseProjectorHomeomorph d y))
      (phaseProjectorHomeomorph d
        ((phaseProjectorHomeomorph d).symm (inverseChart (selectedIndex x) u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth (selectedIndex x)
    (selectedIndex (phaseProjectorHomeomorph d y))).of_le
      (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
  change (u ∈ (chart (selectedIndex x)).target ∧
    (phaseProjectorHomeomorph d).symm ((chart (selectedIndex x)).symm u) ∈
      (phaseChart (selectedIndex (phaseProjectorHomeomorph d y))).source) ↔ _
  simp [phaseChart,OpenPartialHomeomorph.trans_source,chart]

def phaseProjectorDiffeomorph (d : ℕ) :
    (UnitPhaseQuotient (ι := Fin (d+1))) ≃ₘ⟮𝓘(ℝ, Fin d → ℂ),𝓘(ℝ, Fin d → ℂ)⟯ PureProjector d where
  toEquiv := phaseClassProjectorEquiv d
  contMDiff_toFun := phaseToProjector_smooth d
  contMDiff_invFun := projectorToPhase_smooth d

theorem phaseChart_formula {d : ℕ} (r : Fin (d+1))
    (h : UnitVector (Fin (d+1))) (hr : h.val r ≠ 0) :
    phaseChart r (Quotient.mk _ h) = fun j => h.val (r.succAbove j) / h.val r := by
  funext j
  change (h.val (r.succAbove j) * star (h.val r)) /
    (h.val r * star (h.val r)) = h.val (r.succAbove j) / h.val r
  field_simp [hr]

end
end QubitOracle.Paper.MainPaperPhaseQuotient
