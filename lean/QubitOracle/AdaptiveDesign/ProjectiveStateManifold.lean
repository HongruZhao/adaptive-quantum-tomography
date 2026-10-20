import QubitOracle.AdaptiveDesign.AffineProjectorCharts

/-! The standard affine smooth structure on complex rays, and its
identification with the matrix-defined pure-state manifold. The ray
chart formula is proved to be the ordinary homogeneous-coordinate ratio.
The projector chart inverse is smooth as an ambient matrix map and has
a smooth ambient left inverse, so its differential is injective.
-/
namespace QubitOracle.AdaptiveDesign.ProjectiveStateManifold
open QubitOracle.Paper ProjectiveStateGeometry ProjectiveProjectorEquivalence
  ProjectiveStateTopology AffineProjectorCharts
open scoped Manifold ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def selectedIndex {d : ℕ} (P : PureProjector d) : Fin (d+1) := (charts_cover P).choose

theorem selectedIndex_source {d : ℕ} (P : PureProjector d) :
    P ∈ source (selectedIndex P) := (charts_cover P).choose_spec

instance projectorChartedSpace (d : ℕ) : ChartedSpace (Fin d → ℂ) (PureProjector d) where
  atlas := Set.range (@chart d)
  chartAt P := chart (selectedIndex P)
  mem_chart_source P := selectedIndex_source P
  chart_mem_atlas P := ⟨selectedIndex P,rfl⟩

instance projectorManifold (d : ℕ) : IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (PureProjector d) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨r,rfl⟩ ⟨s,rfl⟩
  change ContDiffOn ℝ ∞ (fun u => coordinates s (inverseChart r u)) _
  convert (chart_transition_smooth r s).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp [OpenPartialHomeomorph.trans_source,chart]

def rayChart {d : ℕ} (r : Fin (d+1)) :
    OpenPartialHomeomorph (Projectivization ℂ (Fin (d+1) → ℂ)) (Fin d → ℂ) :=
  (rayProjectorHomeomorph d).toOpenPartialHomeomorph.trans (chart r)

instance rayChartedSpace (d : ℕ) :
    ChartedSpace (Fin d → ℂ) (Projectivization ℂ (Fin (d+1) → ℂ)) where
  atlas := Set.range (@rayChart d)
  chartAt p := rayChart (selectedIndex (rayProjectorHomeomorph d p))
  mem_chart_source p := ⟨Set.mem_univ p,selectedIndex_source _⟩
  chart_mem_atlas p := ⟨selectedIndex (rayProjectorHomeomorph d p),rfl⟩

theorem rayChart_formula {d : ℕ} (r : Fin (d+1)) (z : Fin (d+1) → ℂ)
    (hz : z ≠ 0) (hr : z r ≠ 0) :
    rayChart r (Projectivization.mk ℂ z hz) = fun j => z (r.succAbove j) / z r := by
  have hn : (pureStateNormSq z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z hz))
  funext j
  change coordinates r (rayProjectorHomeomorph d (Projectivization.mk ℂ z hz)) j = _
  rw [coordinates,homeomorph_formula]
  simp only [rayProjector,rankOneDensity,Matrix.smul_apply,smul_eq_mul]
  field_simp [hn,hr]

theorem rayChart_source_formula {d : ℕ} (r : Fin (d+1)) (z : Fin (d+1) → ℂ)
    (hz : z ≠ 0) : Projectivization.mk ℂ z hz ∈ (rayChart r).source ↔ z r ≠ 0 := by
  have hn : (pureStateNormSq z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z hz))
  change (True ∧ (rayProjectorHomeomorph d (Projectivization.mk ℂ z hz)).val r r ≠ 0) ↔ _
  rw [homeomorph_formula]
  simp [rayProjector,rankOneDensity,Matrix.smul_apply,hn]

theorem ray_transition_smooth {d : ℕ} (r s : Fin (d+1)) :
    ContDiffOn ℝ ∞ ((rayChart r).symm.trans (rayChart s))
      ((rayChart r).symm.trans (rayChart s)).source := by
  change ContDiffOn ℝ ∞
    (fun u => coordinates s (rayProjectorHomeomorph d
      ((rayProjectorHomeomorph d).symm (inverseChart r u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth r s).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp [OpenPartialHomeomorph.trans_source,rayChart,chart]

instance rayManifold (d : ℕ) :
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (Projectivization ℂ (Fin (d+1) → ℂ)) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨r,rfl⟩ ⟨s,rfl⟩
  simpa using ray_transition_smooth r s

theorem rayToProjector_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (rayProjectorHomeomorph d) := by
  apply contMDiff_iff.mpr
  refine ⟨(rayProjectorHomeomorph d).continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞
    (fun u => coordinates (selectedIndex y) (rayProjectorHomeomorph d
      ((rayProjectorHomeomorph d).symm
        (inverseChart (selectedIndex (rayProjectorHomeomorph d x)) u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth (selectedIndex (rayProjectorHomeomorph d x))
    (selectedIndex y)).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
  change (u ∈ (rayChart (selectedIndex (rayProjectorHomeomorph d x))).target ∧
    rayProjectorHomeomorph d
      ((rayChart (selectedIndex (rayProjectorHomeomorph d x))).symm u) ∈
      (chart (selectedIndex y)).source) ↔ _
  simp [rayChart,OpenPartialHomeomorph.trans_target,chart]

theorem projectorToRay_smooth (d : ℕ) :
    ContMDiff 𝓘(ℝ, Fin d → ℂ) 𝓘(ℝ, Fin d → ℂ) ∞ (rayProjectorHomeomorph d).symm := by
  apply contMDiff_iff.mpr
  refine ⟨(rayProjectorHomeomorph d).symm.continuous,?_⟩
  intro x y
  change ContDiffOn ℝ ∞
    (fun u => coordinates (selectedIndex (rayProjectorHomeomorph d y))
      (rayProjectorHomeomorph d
        ((rayProjectorHomeomorph d).symm (inverseChart (selectedIndex x) u)))) _
  simp only [Homeomorph.apply_symm_apply]
  convert (chart_transition_smooth (selectedIndex x)
    (selectedIndex (rayProjectorHomeomorph d y))).of_le
      (show (∞ : ℕ∞ω) ≤ ⊤ from le_top) using 1
  ext u
  simp only [extChartAt,OpenPartialHomeomorph.extend_source,
    OpenPartialHomeomorph.extend_target,ModelWithCorners.source_eq,
    modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.preimage_id,
    OpenPartialHomeomorph.extend_coe_symm,Set.range_id,Set.inter_univ,
    Set.mem_inter_iff,Set.mem_preimage,Function.comp_def]
  change (u ∈ (chart (selectedIndex x)).target ∧
    (rayProjectorHomeomorph d).symm ((chart (selectedIndex x)).symm u) ∈
      (rayChart (selectedIndex (rayProjectorHomeomorph d y))).source) ↔ _
  simp [rayChart,OpenPartialHomeomorph.trans_source,chart]

def rayProjectorDiffeomorph (d : ℕ) :
    (Projectivization ℂ (Fin (d+1) → ℂ)) ≃ₘ⟮𝓘(ℝ, Fin d → ℂ),𝓘(ℝ, Fin d → ℂ)⟯ PureProjector d where
  toEquiv := rayToProjector d
  contMDiff_toFun := rayToProjector_smooth d
  contMDiff_invFun := projectorToRay_smooth d

theorem real_dimension (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2*d := by
  rw [finrank_real_of_complex]
  simp

def ambientCoordinates {d : ℕ} (r : Fin (d+1))
    (M : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : Fin d → ℂ :=
  fun j => M (r.succAbove j) r / M r r

theorem inverseChart_differential_leftInverse {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    (fderiv ℝ (ambientCoordinates r) (inverseChart r u).val).comp
      (fderiv ℝ (fun v : Fin d → ℂ => (inverseChart r v).val) u) =
      ContinuousLinearMap.id ℝ (Fin d → ℂ) := by
  have hg : DifferentiableAt ℝ (ambientCoordinates r) (inverseChart r u).val :=
    (coordinates_ambient_smooth r (inverseChart r u).val
    (inverseChart_mem_source r u)).differentiableAt (by norm_num)
  have hf := (inverseChart_matrix_smooth r).differentiable (by norm_num) u
  have he : ambientCoordinates r ∘ (fun v : Fin d → ℂ => (inverseChart r v).val) = id := by
    funext v
    exact coordinates_inverseChart r v
  have hc := fderiv_comp u hg hf
  rw [he,fderiv_id] at hc
  exact hc.symm

theorem inverseChart_differential_injective {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    Function.Injective (fderiv ℝ (fun v : Fin d → ℂ => (inverseChart r v).val) u) := by
  intro v w hvw
  have he := inverseChart_differential_leftInverse r u
  have hev := congrArg (fun L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) => L v) he
  have hew := congrArg (fun L : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) => L w) he
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hev hew
  rw [hvw] at hev
  exact hev.symm.trans hew

end
end QubitOracle.AdaptiveDesign.ProjectiveStateManifold
