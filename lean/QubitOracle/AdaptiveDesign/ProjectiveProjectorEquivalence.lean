import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.AdaptiveDesign.PhysicalModelCharacterization

/-! The literal ray-to-projector bijection of Section 2.3.
The set of projectors is defined by Hermitian symmetry, idempotence,
and trace one. Surjectivity uses the proved spectral characterization,
not a hypothesis asserting a rank-one decomposition.
This module does not yet endow the quotient with a smooth structure.
-/
namespace QubitOracle.AdaptiveDesign.ProjectiveProjectorEquivalence
open QubitOracle.Paper QubitOracle.Paper.ProjectiveStateGeometry
open GlobalPFSICHermitian
open scoped ComplexOrder
noncomputable section

def PureProjector (d : ℕ) := {P : Matrix (Fin (d+1)) (Fin (d+1)) ℂ //
  P.IsHermitian ∧ P * P = P ∧ Matrix.trace P = 1}

def phaseClassProjector (d : ℕ) (q : UnitPhaseQuotient (ι := Fin (d+1))) : PureProjector d :=
  ⟨quotientProjector q, by
    induction q using Quotient.inductionOn with | _ h =>
    change (rankOneDensity h.val).IsHermitian ∧
      rankOneDensity h.val * rankOneDensity h.val = rankOneDensity h.val ∧
      Matrix.trace (rankOneDensity h.val) = 1
    refine ⟨(density_positive h.val).isHermitian, ?_, rankOneDensity_trace_eq_one h.val h.property⟩
    rw [density_square, h.property]
    simp⟩

theorem phaseClassProjector_bijective (d : ℕ) : Function.Bijective (phaseClassProjector d) := by
  constructor
  · intro q r h
    apply quotientProjector_injective
    exact congrArg Subtype.val h
  · intro P
    obtain ⟨h, hh⟩ := PhysicalModelCharacterization.hermitian_projector_is_pure
      (ofMatrix P.val P.property.1) P.property.2.1 P.property.2.2
    refine ⟨Quotient.mk _ ⟨h.val, h.property⟩, ?_⟩
    apply Subtype.ext
    have he := congrArg toMatrix hh
    exact he.symm

def phaseClassProjectorEquiv (d : ℕ) : UnitPhaseQuotient (ι := Fin (d+1)) ≃ PureProjector d :=
  Equiv.ofBijective (phaseClassProjector d) (phaseClassProjector_bijective d)

def rayToProjector (d : ℕ) : Projectivization ℂ (Fin (d+1) → ℂ) ≃ PureProjector d :=
  spherePhaseEquivProjective.symm.trans (phaseClassProjectorEquiv d)

theorem rayToProjector_formula (d : ℕ) (z : Fin (d+1) → ℂ) (hz : z ≠ 0) :
    (rayToProjector d (Projectivization.mk ℂ z hz)).val = rayProjector z := by
  have he : spherePhaseEquivProjective (Quotient.mk _ (normalizedUnit z hz)) =
      Projectivization.mk ℂ z hz := normalizedUnit_ray z hz
  rw [← he]
  change (phaseClassProjectorEquiv d
    (spherePhaseEquivProjective.symm (spherePhaseEquivProjective
      (Quotient.mk _ (normalizedUnit z hz))))).val = _
  rw [Equiv.symm_apply_apply]
  exact normalize_density z

theorem rayToProjector_range (d : ℕ) (p : Projectivization ℂ (Fin (d+1) → ℂ)) :
    (rayToProjector d p).val.mulVecLin.range = p.submodule := by
  induction p using Projectivization.ind with | h z hz =>
  rw [rayToProjector_formula d z hz, rayProjector_range z hz, Projectivization.submodule_mk]

theorem rayToProjector_inverse_range (d : ℕ) (P : PureProjector d) :
    ((rayToProjector d).symm P).submodule = P.val.mulVecLin.range := by
  have he := rayToProjector_range d ((rayToProjector d).symm P)
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

end
end QubitOracle.AdaptiveDesign.ProjectiveProjectorEquivalence
