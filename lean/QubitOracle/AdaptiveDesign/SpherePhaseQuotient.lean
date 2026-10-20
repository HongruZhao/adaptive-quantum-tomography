import QubitOracle.AdaptiveDesign.ProjectiveStateManifold

/-! The unit-sphere phase quotient with its actual quotient topology and
the standard homogeneous-coordinate smooth atlas. The equivalence with
complex projectivization is proved, rather than postulated. -/
namespace QubitOracle.AdaptiveDesign.SpherePhaseQuotient
open QubitOracle.Paper ProjectiveStateGeometry ProjectiveProjectorEquivalence
  ProjectiveStateTopology AffineProjectorCharts ProjectiveStateManifold
open scoped Manifold ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

instance phaseQuotientTopology (d : ℕ) :
    TopologicalSpace (UnitPhaseQuotient (ι := Fin (d+1))) := inferInstance

instance phaseQuotientCompact (d : ℕ) :
    CompactSpace (UnitPhaseQuotient (ι := Fin (d+1))) := inferInstance

instance projectiveT2 (d : ℕ) :
    T2Space (Projectivization ℂ (Fin (d+1) → ℂ)) :=
  (rayProjectorHomeomorph d).symm.t2Space

theorem quotientRay_continuous (d : ℕ) :
    Continuous (quotientRay (ι := Fin (d+1))) := by
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr (unitRay_continuous d)

def spherePhaseHomeomorph (d : ℕ) :
    UnitPhaseQuotient (ι := Fin (d+1)) ≃ₜ
      Projectivization ℂ (Fin (d+1) → ℂ) :=
  (spherePhaseEquivProjective (ι := Fin (d+1))).toHomeomorphOfContinuousClosed
    (quotientRay_continuous d) (quotientRay_continuous d).isClosedMap

def phaseChart {d : ℕ} (r : Fin (d+1)) :
    OpenPartialHomeomorph (UnitPhaseQuotient (ι := Fin (d+1))) (Fin d → ℂ) :=
  (spherePhaseHomeomorph d).toOpenPartialHomeomorph.trans (rayChart r)

def phaseSelectedIndex {d : ℕ} (q : UnitPhaseQuotient (ι := Fin (d+1))) : Fin (d+1) :=
  selectedIndex (rayProjectorHomeomorph d (spherePhaseHomeomorph d q))

instance phaseChartedSpace (d : ℕ) :
    ChartedSpace (Fin d → ℂ) (UnitPhaseQuotient (ι := Fin (d+1))) where
  atlas := Set.range (@phaseChart d)
  chartAt q := phaseChart (phaseSelectedIndex q)
  mem_chart_source q := ⟨Set.mem_univ q,Set.mem_univ _,selectedIndex_source _⟩
  chart_mem_atlas q := ⟨phaseSelectedIndex q,rfl⟩

theorem phaseChart_formula {d : ℕ} (r : Fin (d+1))
    (h : UnitVector (Fin (d+1))) (hr : h.val r ≠ 0) :
    phaseChart r (Quotient.mk _ h) = fun j => h.val (r.succAbove j) / h.val r :=
  rayChart_formula r h.val (unitVector_ne_zero h) hr

theorem phaseChart_source_formula {d : ℕ} (r : Fin (d+1))
    (h : UnitVector (Fin (d+1))) :
    Quotient.mk _ h ∈ (phaseChart r).source ↔ h.val r ≠ 0 := by
  change (True ∧ unitRay h ∈ (rayChart r).source) ↔ _
  simpa only [true_and,unitRay] using rayChart_source_formula r h.val (unitVector_ne_zero h)

theorem phase_transition_smooth {d : ℕ} (r s : Fin (d+1)) :
    ContDiffOn ℝ ∞ ((phaseChart r).symm.trans (phaseChart s))
      ((phaseChart r).symm.trans (phaseChart s)).source := by
  change ContDiffOn ℝ ∞ (fun u => rayChart s (spherePhaseHomeomorph d
    ((spherePhaseHomeomorph d).symm ((rayChart r).symm u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert ray_transition_smooth r s using 1
  · rfl
  · ext u
    change (u ∈ (phaseChart r).target ∧
      (phaseChart r).symm u ∈ (phaseChart s).source) ↔
      (u ∈ (rayChart r).target ∧ (rayChart r).symm u ∈ (rayChart s).source)
    simp [phaseChart,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.trans_target]

instance phaseManifold (d : ℕ) :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (UnitPhaseQuotient (ι := Fin (d+1))) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨r,rfl⟩ ⟨s,rfl⟩
  simpa using phase_transition_smooth r s

theorem spherePhaseHomeomorph_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (spherePhaseHomeomorph d) := by
  apply contMDiff_iff.mpr
  refine ⟨(spherePhaseHomeomorph d).continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞ (fun u => rayChart
    (selectedIndex (rayProjectorHomeomorph d y)) (spherePhaseHomeomorph d
    ((spherePhaseHomeomorph d).symm ((rayChart (phaseSelectedIndex x)).symm u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert ray_transition_smooth (phaseSelectedIndex x)
    (selectedIndex (rayProjectorHomeomorph d y)) using 1
  · rfl
  ·
   ext u
   try simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
   change (u ∈ (phaseChart (phaseSelectedIndex x)).target ∧
    spherePhaseHomeomorph d ((phaseChart (phaseSelectedIndex x)).symm u) ∈
    (rayChart (selectedIndex (rayProjectorHomeomorph d y))).source) ↔ _
   simp [phaseChart,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.trans_target]

theorem spherePhaseHomeomorph_inverse_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (spherePhaseHomeomorph d).symm := by
  apply contMDiff_iff.mpr
  refine ⟨(spherePhaseHomeomorph d).symm.continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞ (fun u => rayChart (phaseSelectedIndex y)
    (spherePhaseHomeomorph d ((spherePhaseHomeomorph d).symm
    ((rayChart (selectedIndex (rayProjectorHomeomorph d x))).symm u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert ray_transition_smooth (selectedIndex (rayProjectorHomeomorph d x))
    (phaseSelectedIndex y) using 1
  · rfl
  ·
   ext u
   try simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
   change (u ∈ (rayChart (selectedIndex (rayProjectorHomeomorph d x))).target ∧
    (spherePhaseHomeomorph d).symm
    ((rayChart (selectedIndex (rayProjectorHomeomorph d x))).symm u) ∈
    (phaseChart (phaseSelectedIndex y)).source) ↔ _
   simp [phaseChart,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.trans_target]

def spherePhaseDiffeomorph (d : ℕ) :
    (UnitPhaseQuotient (ι := Fin (d+1))) ≃ₘ⟮𝓘(ℝ, Fin d → ℂ),𝓘(ℝ, Fin d → ℂ)⟯
      Projectivization ℂ (Fin (d+1) → ℂ) where
  toEquiv := spherePhaseEquivProjective
  contMDiff_toFun := spherePhaseHomeomorph_smooth d
  contMDiff_invFun := spherePhaseHomeomorph_inverse_smooth d

def spherePhaseProjectorDiffeomorph (d : ℕ) :
    (UnitPhaseQuotient (ι := Fin (d+1))) ≃ₘ⟮𝓘(ℝ, Fin d → ℂ),𝓘(ℝ, Fin d → ℂ)⟯
      PureProjector d :=
  (spherePhaseDiffeomorph d).trans (rayProjectorDiffeomorph d)

end
end QubitOracle.AdaptiveDesign.SpherePhaseQuotient
