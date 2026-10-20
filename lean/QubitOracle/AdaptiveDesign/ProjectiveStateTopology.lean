import QubitOracle.AdaptiveDesign.ProjectiveProjectorEquivalence
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
/-! The quotient and subspace topologies in the ray-to-projector map.
These are the actual quotient topology on nonzero vectors and the
induced topology on Hermitian idempotents, not transported definitions.
The smooth-manifold structure is a separate obligation.
-/
namespace QubitOracle.AdaptiveDesign.ProjectiveStateTopology
open QubitOracle.Paper ProjectiveStateGeometry ProjectiveProjectorEquivalence
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

instance projectiveTopology (d : ℕ) : TopologicalSpace (Projectivization ℂ (Fin (d+1) → ℂ)) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin (d+1) → ℂ))))
instance projectorTopology (d : ℕ) : TopologicalSpace (PureProjector d) :=
  inferInstanceAs (TopologicalSpace {P : Matrix (Fin (d+1)) (Fin (d+1)) ℂ //
    P.IsHermitian ∧ P*P=P ∧ Matrix.trace P=1})
instance projectorT2 (d : ℕ) : T2Space (PureProjector d) :=
  inferInstanceAs (T2Space {P : Matrix (Fin (d+1)) (Fin (d+1)) ℂ //
    P.IsHermitian ∧ P*P=P ∧ Matrix.trace P=1})

theorem normSq_continuous {ι : Type*} [Fintype ι] : Continuous (@pureStateNormSq ι _) := by
  unfold pureStateNormSq
  exact continuous_finset_sum _ (fun i _ => Complex.continuous_normSq.comp (continuous_apply i))

theorem unitVectors_compact (d : ℕ) :
    IsCompact {z : Fin (d+1) → ℂ | pureStateNormSq z = 1} := by
  apply (isCompact_closedBall (0 : Fin (d+1) → ℂ) 1).of_isClosed_subset
  · exact isClosed_eq normSq_continuous continuous_const
  · intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    have hi : Complex.normSq (z i) ≤ pureStateNormSq z :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
    rw [hz, ← Complex.sq_norm] at hi
    nlinarith [norm_nonneg (z i)]

instance unitVectors_compactSpace (d : ℕ) : CompactSpace (UnitVector (Fin (d+1))) :=
  isCompact_iff_compactSpace.mp (unitVectors_compact d)

theorem unitRay_continuous (d : ℕ) : Continuous (unitRay (ι := Fin (d+1))) := by
  have he : unitRay (ι := Fin (d+1)) = fun z : UnitVector (Fin (d+1)) =>
      Projectivization.mk' ℂ ⟨z.val,unitVector_ne_zero z⟩ := rfl
  rw [he]
  exact continuous_quotient_mk'.comp (continuous_subtype_val.subtype_mk _)

theorem unitRay_surjective (d : ℕ) : Function.Surjective (unitRay (ι := Fin (d+1))) := by
  intro p
  refine ⟨normalizedUnit p.rep p.rep_nonzero,?_⟩
  rw [normalizedUnit_ray,Projectivization.mk_rep]

instance projectiveCompact (d : ℕ) : CompactSpace (Projectivization ℂ (Fin (d+1) → ℂ)) := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (unitRay_surjective d)]
  exact isCompact_range (unitRay_continuous d)

theorem rayProjector_continuous_nonzero (d : ℕ) :
    Continuous (fun z : {z : Fin (d+1) → ℂ // z ≠ 0} => rayProjector z.val) := by
  unfold rayProjector
  have hn : Continuous (fun z : {z : Fin (d+1) → ℂ // z ≠ 0} =>
      (pureStateNormSq z.val : ℂ)⁻¹) := by
    apply Continuous.inv₀
    · exact Complex.continuous_ofReal.comp (normSq_continuous.comp continuous_subtype_val)
    · intro z
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive z.val z.property))
  have hd : Continuous (fun z : {z : Fin (d+1) → ℂ // z ≠ 0} => rankOneDensity z.val) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact ((continuous_apply i).comp continuous_subtype_val).mul
      (((continuous_apply j).comp continuous_subtype_val).star)
  simpa only [Pi.smul_apply] using! hn.smul hd

theorem rayToProjector_continuous (d : ℕ) : Continuous (rayToProjector d) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  convert rayProjector_continuous_nonzero d using 1
  funext z
  exact rayToProjector_formula d z.val z.property

def rayProjectorHomeomorph (d : ℕ) :
    Projectivization ℂ (Fin (d+1) → ℂ) ≃ₜ PureProjector d :=
  (rayToProjector d).toHomeomorphOfContinuousClosed
    (rayToProjector_continuous d) (rayToProjector_continuous d).isClosedMap

theorem homeomorph_formula (d : ℕ) (z : Fin (d+1) → ℂ) (hz : z ≠ 0) :
    (rayProjectorHomeomorph d (Projectivization.mk ℂ z hz)).val = rayProjector z :=
  rayToProjector_formula d z hz

end
end QubitOracle.AdaptiveDesign.ProjectiveStateTopology
