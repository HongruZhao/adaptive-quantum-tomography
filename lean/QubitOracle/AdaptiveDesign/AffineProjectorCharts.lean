import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PhysicalModelCharacterization
import QubitOracle.AdaptiveDesign.ProjectiveProjectorEquivalence
import QubitOracle.AdaptiveDesign.ProjectiveStateTopology
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
/-! Affine projective charts for the actual matrix-defined pure-state space.
These rational charts use the induced matrix topology. Inverse and
overlap smoothness are proved from their formulas.
-/
namespace QubitOracle.AdaptiveDesign.AffineProjectorCharts
open QubitOracle.Paper ProjectiveStateGeometry ProjectiveProjectorEquivalence ProjectiveStateTopology
open GlobalPFSICHermitian
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise Manifold
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def affineVector {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) : Fin (d+1) → ℂ :=
  Fin.insertNth r 1 u

theorem affineVector_nonzero {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) : affineVector r u ≠ 0 := by
  intro h
  have hh := congrFun h r
  simpa [affineVector] using hh

def inverseChart {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) : PureProjector d :=
  rayToProjector d (Projectivization.mk ℂ (affineVector r u) (affineVector_nonzero r u))

theorem inverseChart_formula {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    (inverseChart r u).val = rayProjector (affineVector r u) :=
  rayToProjector_formula d _ _

def coordinates {d : ℕ} (r : Fin (d+1)) (P : PureProjector d) : Fin d → ℂ :=
  fun j => P.val (r.succAbove j) r / P.val r r

def source {d : ℕ} (r : Fin (d+1)) : Set (PureProjector d) := {P | P.val r r ≠ 0}

theorem inverseChart_diagonal {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    (inverseChart r u).val r r = (pureStateNormSq (affineVector r u) : ℂ)⁻¹ := by
  rw [inverseChart_formula]
  simp [rayProjector,rankOneDensity,Matrix.smul_apply,affineVector]

theorem inverseChart_mem_source {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    inverseChart r u ∈ source r := by
  change (inverseChart r u).val r r ≠ 0
  rw [inverseChart_diagonal]
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (normSq_positive _ (affineVector_nonzero r u))))

theorem coordinates_inverseChart {d : ℕ} (r : Fin (d+1)) (u : Fin d → ℂ) :
    coordinates r (inverseChart r u) = u := by
  have hn : (pureStateNormSq (affineVector r u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive _ (affineVector_nonzero r u)))
  funext j
  simp only [coordinates,inverseChart_formula,rayProjector,rankOneDensity,
    Matrix.smul_apply,smul_eq_mul]
  simp only [affineVector,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,
    star_one,mul_one]
  change (pureStateNormSq (r.insertNth 1 u) : ℂ) ≠ 0 at hn
  field_simp [hn]

theorem inverseChart_coordinates {d : ℕ} (r : Fin (d+1)) (P : PureProjector d)
    (hP : P ∈ source r) : inverseChart r (coordinates r P) = P := by
  obtain ⟨h,hh⟩ := PhysicalModelCharacterization.hermitian_projector_is_pure
    (ofMatrix P.val P.property.1) P.property.2.1 P.property.2.2
  have he : P.val = rankOneDensity h.val := (congrArg toMatrix hh)
  have hr : h.val r ≠ 0 := by
    intro hz
    apply hP
    simp [he,rankOneDensity,hz]
  have hv : affineVector r (coordinates r P) = (h.val r)⁻¹ • h.val := by
    apply (Fin.insertNth_eq_iff).mpr
    constructor
    · simp [hr]
    · funext j
      simp only [coordinates,he,rankOneDensity,Pi.smul_apply,smul_eq_mul,Fin.removeNth]
      field_simp [hr]
  apply Subtype.ext
  rw [inverseChart_formula,hv,rayProjector_scalar_invariant _ _ (inv_ne_zero hr),
    he,rayProjector,h.property]
  simp

theorem charts_cover {d : ℕ} (P : PureProjector d) : ∃ r : Fin (d+1), P ∈ source r := by
  by_contra h
  push_neg at h
  have ht := P.property.2.2
  have hz : Matrix.trace P.val = 0 := by
    simp only [Matrix.trace,Matrix.diag]
    apply Finset.sum_eq_zero
    intro r _
    simpa [source] using h r
  rw [hz] at ht
  exact zero_ne_one ht

theorem affineVector_smooth {d : ℕ} (r : Fin (d+1)) : ContDiff ℝ ⊤ (affineVector r) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.succAboveCases r ?_ (fun j => ?_) i
  · simpa [affineVector] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin d → ℂ => (1:ℂ)))
  · simpa [affineVector] using (contDiff_apply ℝ ℂ j : ContDiff ℝ ⊤ (fun u : Fin d → ℂ => u j))

theorem normSq_smooth {d : ℕ} : ContDiff ℝ ⊤ (@pureStateNormSq (Fin (d+1)) _) := by
  unfold pureStateNormSq
  simp only [Complex.normSq_apply]
  apply ContDiff.sum
  intro i _
  have hr : ContDiff ℝ ⊤ (fun x : Fin (d+1) → ℂ => (x i).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i)
  have hi : ContDiff ℝ ⊤ (fun x : Fin (d+1) → ℂ => (x i).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ i)
  exact (hr.mul hr).add (hi.mul hi)

theorem inverseChart_matrix_smooth {d : ℕ} (r : Fin (d+1)) :
    ContDiff ℝ ⊤ (fun u : Fin d → ℂ => (inverseChart r u).val) := by
  have hn : ContDiff ℝ ⊤ (fun u : Fin d → ℂ => (pureStateNormSq (affineVector r u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (normSq_smooth.comp (affineVector_smooth r))
  have hi := hn.inv (fun u => Complex.ofReal_ne_zero.mpr
    (ne_of_gt (normSq_positive _ (affineVector_nonzero r u))))
  have hd : ContDiff ℝ ⊤ (fun u : Fin d → ℂ => rankOneDensity (affineVector r u)) := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact ((contDiff_apply ℝ ℂ i).comp (affineVector_smooth r)).mul
      (Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ j).comp (affineVector_smooth r)))
  simpa only [Pi.smul_apply,inverseChart_formula,rayProjector,Pi.inv_apply] using! hi.smul hd

theorem coordinates_ambient_smooth {d : ℕ} (r : Fin (d+1))
    (M : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hM : M r r ≠ 0) :
    ContDiffAt ℝ ⊤ (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ =>
      fun j : Fin d => A (r.succAbove j) r / A r r) M := by
  apply contDiffAt_pi.mpr; intro j
  have hf : ContDiffAt ℝ ⊤ (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ =>
      A (r.succAbove j) r) M := by fun_prop
  have hg : ContDiffAt ℝ ⊤ (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ =>
      A r r) M := by fun_prop
  simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! hf.mul (hg.inv hM)

theorem source_open {d : ℕ} (r : Fin (d+1)) : IsOpen (source r) := by
  exact isOpen_ne.preimage ((continuous_apply r).comp
    ((continuous_apply r).comp continuous_subtype_val))

theorem coordinates_continuousOn {d : ℕ} (r : Fin (d+1)) :
    ContinuousOn (coordinates r) (source r) := by
  intro P hP
  exact ((coordinates_ambient_smooth r P.val hP).continuousAt.comp
    continuous_subtype_val.continuousAt).continuousWithinAt

theorem inverseChart_continuous {d : ℕ} (r : Fin (d+1)) : Continuous (inverseChart r) :=
  Topology.IsInducing.subtypeVal.continuous_iff.mpr (inverseChart_matrix_smooth r).continuous

def chart {d : ℕ} (r : Fin (d+1)) : OpenPartialHomeomorph (PureProjector d) (Fin d → ℂ) where
  toFun := coordinates r
  invFun := inverseChart r
  source := source r
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' u _ := inverseChart_mem_source r u
  left_inv' P hP := inverseChart_coordinates r P hP
  right_inv' u _ := coordinates_inverseChart r u
  open_source := source_open r
  open_target := isOpen_univ
  continuousOn_toFun := coordinates_continuousOn r
  continuousOn_invFun := (inverseChart_continuous r).continuousOn

theorem chart_transition_smooth {d : ℕ} (r s : Fin (d+1)) :
    ContDiffOn ℝ ⊤ (fun u : Fin d → ℂ => coordinates s (inverseChart r u))
      {u | inverseChart r u ∈ source s} := by
  intro u hu
  exact ((coordinates_ambient_smooth s (inverseChart r u).val hu).comp u
    (inverseChart_matrix_smooth r).contDiffAt).contDiffWithinAt

end
end QubitOracle.AdaptiveDesign.AffineProjectorCharts
