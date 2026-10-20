import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.ElementaryPVMIdentification
import QubitOracle.AdaptiveDesign.FiniteFrameCoercivity
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.PVMGeometry
import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.RandomizedPVM
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.ElementaryPVMBases
import QubitOracle.Paper.ElementaryReferenceAlgebra
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.ReferenceReflection
import QubitOracle.Paper.ReferenceRegularity
/-! The elementary reference POVM, with C1/C2 witnesses and a sharp
reference-probability bound. The finite-library covariance example is
handled separately in the supplement.
-/
namespace QubitOracle.AdaptiveDesign.ElementaryReferencePOVM
open QubitOracle QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra
  ElementaryPVMBases ReferenceReflection ReferenceRegularity
open ElementaryPVMIdentification GlobalPFSICHermitian GlobalPFSICBorn
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1500000

abbrev Outcome (d : ℕ) := BasisLabel (d+1) × Fin (d+1)

def rotatedBasis (d : ℕ) (hd : 0 < d) (l : BasisLabel (d+1)) : Action d :=
  ⟨referenceRotation d * basisMatrix l,
    (Matrix.unitaryGroup (Fin (d+1)) ℂ).mul_mem
      (referenceRotation_unitary d hd) (basisMatrix_unitary l)⟩

def reference (d : ℕ) (hd : 0 < d) : FinitePOVM (Fin (d+1)) (Outcome d) :=
  RandomizedPVM.measurement (RandomizedPVM.uniformWeight (BasisLabel (d+1)))
    (rotatedBasis d hd) RandomizedPVM.uniformWeight_nonnegative RandomizedPVM.uniformWeight_sum

def weight (d : ℕ) : ℝ := (Fintype.card (BasisLabel (d+1)) : ℝ)⁻¹

theorem weight_positive (d : ℕ) : 0 < weight d := by
  unfold weight
  exact inv_pos.mpr (by exact_mod_cast (Fintype.card_pos (α := BasisLabel (d+1))))

theorem effect_formula (d : ℕ) (hd : 0 < d) (o : Outcome d) :
    (reference d hd).effect o = weight d •
      rankOneDensity ((referenceRotation d).mulVec (basisVector o.1 o.2)) := by
  change weight d • toMatrix (PVMGeometry.basisEffect (rotatedBasis d hd o.1) o.2) = _
  rw [PVMGeometry.basisEffect_matrix]
  congr 1

theorem rotated_effect_formula (d : ℕ) (hd : 0 < d) (o : Outcome d) :
    GeneralPOVM.effectVector (reference d hd) o = weight d •
      conjugationIsometry (referenceRotation d) (referenceRotation_unitary d hd) (basisEffect o) := by
  apply toMatrix_injective
  rw [toMatrix_smul]
  change (reference d hd).effect o = weight d •
    (referenceRotation d * rankOneDensity (basisVector o.1 o.2) * (referenceRotation d).conjTranspose)
  rw [effect_formula]
  congr 1
  exact GlobalPFSIC.projector_mulVec _ _

theorem identifying (d : ℕ) (hd : 0 < d) : GeneralPOVM.Identifying (reference d hd) := by
  intro A hA
  let U := conjugationIsometry (referenceRotation d) (referenceRotation_unitary d hd)
  have hz : U.symm A = 0 := by
    apply effects_separate
    intro o
    have h := hA o
    rw [rotated_effect_formula, real_inner_smul_left,
      FiniteFrameCoercivity.transported_measurement] at h
    exact (mul_eq_zero.mp h).resolve_left (weight_positive d).ne'
  exact U.symm.injective (by simpa using hz)

theorem rankOne (d : ℕ) (hd : 0 < d) : PhasePair.RankOne (reference d hd) := by
  intro o
  refine ⟨(Real.sqrt (weight d) : ℂ) •
    (referenceRotation d).mulVec (basisVector o.1 o.2), ?_⟩
  change (reference d hd).effect o = rankOneDensity _
  rw [effect_formula, density_smul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (weight_positive d).le]
  ext i j
  simp [GlobalPFSIC.projector, rankOneDensity, Matrix.smul_apply, Complex.real_smul]

theorem rotation_reference_row (d : ℕ) (hd : 0 < d) (k : Fin (d+1)) :
    referenceRotation d 0 k = star (referenceVector d k) := by
  have h := congrFun (referenceRotation_adjoint_reference d hd) k
  simp [Matrix.mulVec, dotProduct, GlobalPFSIC.coordinate, Pi.single_apply,
    Matrix.conjTranspose_apply] at h
  rw [← h]
  simp

theorem rotation_reference_component (d : ℕ) (hd : 0 < d) (v : Fin (d+1) → ℂ) :
    ((referenceRotation d).mulVec v) 0 = basisBornAmplitude (referenceVector d) v := by
  simp only [Matrix.mulVec, dotProduct, rotation_reference_row d hd, basisBornAmplitude]

theorem reference_probability (d : ℕ) (hd : 0 < d) (o : Outcome d) :
    referenceProbability (reference d hd) o = weight d *
      Complex.normSq (basisBornAmplitude (referenceVector d) (basisVector o.1 o.2)) := by
  rw [referenceProbability, effect_formula]
  simp only [Matrix.smul_apply, rankOneDensity, rotation_reference_component d hd,
    Complex.star_def, Complex.mul_conj, Complex.real_smul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem probability_lower (d : ℕ) (hd : 0 < d) (o : Outcome d) :
    weight d / (2*cSquared d) ≤ referenceProbability (reference d hd) o := by
  rw [reference_probability]
  simpa [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left (reference_basis_lower d o.1 o.2) (weight_positive d).le

theorem regular (d : ℕ) (hd : 0 < d) : GeneralPOVM.Regular (reference d hd) := by
  intro o
  exact lt_of_lt_of_le (div_pos (weight_positive d) (mul_pos (by norm_num) (cSquared_positive d)))
    (probability_lower d hd o)

theorem probability_lower_attained (d : ℕ) (hd : 0 < d) :
    ∃ o : Outcome d, referenceProbability (reference d hd) o = weight d / (2*cSquared d) := by
  let s : Fin (d+1) := ⟨1,by omega⟩
  let p : OrderedPair (d+1) := ⟨(0,s),by change (0:ℕ) < 1; decide⟩
  refine ⟨(.inr (false,p),s),?_⟩
  rw [reference_probability, pair_second]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul, p]
  rw [normalized_amplitude_normSq, raw_adjacent_difference d hd]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

theorem paired_probability_lower (d : ℕ) (hd : 0 < d) (o : Bool × Outcome d) :
    weight d / (4*cSquared d) ≤ referenceProbability (PhasePair.paired (reference d hd)) o := by
  rw [PhasePair.paired_referenceProbability]
  have h := mul_le_mul_of_nonneg_left (probability_lower d hd o.2) (by norm_num : (0:ℝ) ≤ 1/2)
  convert h using 1 <;> (first | rfl | ring)

theorem paired_probability_lower_attained (d : ℕ) (hd : 0 < d) :
    ∃ o : Bool × Outcome d,
      referenceProbability (PhasePair.paired (reference d hd)) o = weight d / (4*cSquared d) := by
  obtain ⟨o,ho⟩ := probability_lower_attained d hd
  refine ⟨(false,o),?_⟩
  rw [PhasePair.paired_referenceProbability,ho]
  ring

theorem paired_reference_floor (d : ℕ) (hd : 0 < d) :
    TangentGLS.referenceFloor (PhasePair.paired (reference d hd)) = weight d / (16*cSquared d) := by
  classical
  have hmin : Finset.univ.inf' Finset.univ_nonempty
      (referenceProbability (PhasePair.paired (reference d hd))) = weight d / (4*cSquared d) := by
    apply le_antisymm
    · obtain ⟨o,ho⟩ := paired_probability_lower_attained d hd
      rw [← ho]
      exact Finset.inf'_le _ (Finset.mem_univ o)
    · exact Finset.le_inf' _ _ (fun o _ => paired_probability_lower d hd o)
  rw [TangentGLS.referenceFloor,hmin]
  ring

theorem assumptions_implementable (d : ℕ) (hd : 0 < d) :
    GeneralPOVM.Identifying (reference d hd) ∧ GeneralPOVM.Regular (reference d hd) ∧
      PhasePair.RankOne (reference d hd) :=
  ⟨identifying d hd, regular d hd, rankOne d hd⟩

theorem paired_fisher (d : ℕ) (hd : 0 < d) :
    GeneralPOVM.FisherSymmetric (PhasePair.paired (reference d hd)) :=
  PhasePair.paired_fisher_of_rankOne _ (regular d hd) (rankOne d hd)

theorem complete_born_law (d : ℕ) (hd : 0 < d)
    (rho : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (o : Outcome d) :
    (Matrix.trace (rho * (reference d hd).effect o)).re =
      weight d * (Matrix.trace (rho * rankOneDensity
        ((referenceRotation d).mulVec (basisVector o.1 o.2)))).re := by
  rw [effect_formula]
  simp [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]

end
end QubitOracle.AdaptiveDesign.ElementaryReferencePOVM
