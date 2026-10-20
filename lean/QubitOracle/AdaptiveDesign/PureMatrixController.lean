import QubitOracle.AdaptiveDesign.ExactHouseholder
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.Paper.PureMultilevelNearestPureProjection
import QubitOracle.Paper.PureMultilevelRankOneProjectorCompact
import QubitOracle.Paper.PureStateFoundations
/-!
# A pure-state adaptive controller independent of the unknown truth

The controller first selects a nearest rank-one projector in Frobenius norm,
then completes its normalized vector by the exact phase-adjusted Householder matrix. The nonemptiness
witness is the known computational vector `e0`; no unknown state is supplied
to the estimator. Its projector is consistent even though vector phases and
complement frames need not converge.
-/

namespace QubitOracle.AdaptiveDesign.PureMatrixController

open Filter
open QubitOracle.Paper
open PureMultilevelRankOneProjectorCompact
open scoped BigOperators Topology ComplexOrder Matrix.Norms.Frobenius

noncomputable section

abbrev PureVector (d : ℕ) := NormalizedPureVector (d+1)

def knownReference (d : ℕ) : PureVector d :=
  ⟨Pi.single 0 1, GlobalPFSIC.coordinate_normSq (0 : Fin (d+1))⟩

def nearestVector (d : ℕ) (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : PureVector d :=
  nearestNormalizedRankOneProjector (d+1) (knownReference d) raw

def projectedMatrix (d : ℕ) (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  rankOneDensity (nearestVector d raw).val

theorem projectedMatrix_posSemidef (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (projectedMatrix d raw).PosSemidef :=
  GlobalPFSIC.projector_posSemidef (nearestVector d raw).val

theorem projectedMatrix_trace (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix.trace (projectedMatrix d raw) = 1 :=
  rankOneDensity_trace_eq_one (nearestVector d raw).val (nearestVector d raw).property

theorem projectedMatrix_idempotent (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    projectedMatrix d raw * projectedMatrix d raw = projectedMatrix d raw := by
  let v := (nearestVector d raw).val
  have hv : (∑ i, star (v i) * v i) = (1 : ℂ) := by
    have h := congrArg Complex.ofReal (nearestVector d raw).property
    simpa [normalizedPureVectorSet, pureStateNormSq,
      Complex.normSq_eq_conj_mul_self, v] using h
  ext j k
  change (∑ i, (v j * star (v i)) * (v i * star (v k))) = v j * star (v k)
  calc
    _ = v j * (∑ i, star (v i) * v i) * star (v k) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hv]; ring

theorem nearestVector_is_nearest (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (candidate : PureVector d) :
    ‖projectedMatrix d raw - raw‖ ≤ ‖rankOneDensity candidate.val - raw‖ :=
  nearestNormalizedRankOneProjector_is_nearest (d+1) (knownReference d) raw candidate

theorem projectedMatrix_error_le_two (d : ℕ) (truth : PureVector d)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    ‖projectedMatrix d raw - rankOneDensity truth.val‖ ≤
      2 * ‖raw - rankOneDensity truth.val‖ := by
  exact PureMultilevelNearestPureProjection.nearestPureProjection_error_le_two
    (normalizedRankOneProjectorEmbed (d+1)) truth raw (nearestVector d raw)
    (nearestVector_is_nearest d raw)

theorem projectedMatrix_tendsto (d : ℕ) (truth : PureVector d)
    (raw : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hraw : Tendsto raw atTop (𝓝 (rankOneDensity truth.val))) :
    Tendsto (fun n => projectedMatrix d (raw n)) atTop (𝓝 (rankOneDensity truth.val)) := by
  exact PureMultilevelNearestPureProjection.nearestPureProjection_tendsto
    (normalizedRankOneProjectorEmbed (d+1)) truth raw (fun n => nearestVector d (raw n))
    (fun n => nearestVector_is_nearest d (raw n)) hraw

/-- Deterministic orthonormal-basis extension, with no Haar or probability axiom. -/
theorem exists_unitary_firstColumn {d : ℕ} (psi : PureVector d) :
    ∃ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ ∧ (fun i => U i 0) = psi.val := by
  let u : EuclideanSpace ℂ (Fin (d+1)) :=
    (EuclideanSpace.equiv (Fin (d+1)) ℂ).symm psi.val
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ i, ‖psi.val i‖^2) = 1
      simp only [Complex.sq_norm]
      exact psi.property
    nlinarith [norm_nonneg u]
  let v : Fin (d+1) → EuclideanSpace ℂ (Fin (d+1)) :=
    fun i => if i = 0 then u else EuclideanSpace.basisFun (Fin (d+1)) ℂ i
  have hv : Orthonormal ℂ (({0} : Set (Fin (d+1))).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin (d+1)) = 0 := i.property
    have hj : (j : Fin (d+1)) = 0 := j.property
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst j
    simp only [Set.domRestrict, v, hi, if_pos]
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (ι := Fin (d+1)) (𝕜 := ℂ)) hv
  have hB0 : B 0 = u := by
    rw [hB 0 (by simp)]
    simp [v]
  let E0 := EuclideanSpace.basisFun (Fin (d+1)) ℂ
  refine ⟨E0.toBasis.toMatrix B,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary E0 B, ?_⟩
  funext i
  simp [E0, Module.Basis.toMatrix_apply, hB0, u]

def controllerFrame (d : ℕ) (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  ExactHouseholder.matrix (nearestVector d raw).val

theorem controllerFrame_unitary (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    controllerFrame d raw ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  ExactHouseholder.matrix_unitary (nearestVector d raw).val (nearestVector d raw).property

theorem controllerFrame_firstColumn (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (fun i => controllerFrame d raw i 0) = (nearestVector d raw).val :=
  ExactHouseholder.matrix_firstColumn (nearestVector d raw).val

theorem controllerFrame_firstProjector (d : ℕ)
    (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    GlobalPFSIC.projector (fun i => controllerFrame d raw i 0) = projectedMatrix d raw := by
  rw [controllerFrame_firstColumn]
  rfl

theorem controllerFrame_firstProjector_tendsto (d : ℕ) (truth : PureVector d)
    (raw : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hraw : Tendsto raw atTop (𝓝 (rankOneDensity truth.val))) :
    Tendsto (fun n => GlobalPFSIC.projector (fun i => controllerFrame d (raw n) i 0))
      atTop (𝓝 (rankOneDensity truth.val)) := by
  simpa only [controllerFrame_firstProjector] using projectedMatrix_tendsto d truth raw hraw

end

end QubitOracle.AdaptiveDesign.PureMatrixController
