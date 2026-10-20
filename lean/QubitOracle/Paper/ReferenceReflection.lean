import QubitOracle.Paper.ElementaryPVMBases
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.Paper.ElementaryReferenceAlgebra
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
/-! The fixed minus Householder reflection used by the reference PVMs.
It differs from the adaptive phase-adjusted Householder completion.
-/
namespace QubitOracle.Paper.ReferenceReflection
open QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra
open QubitOracle.AdaptiveDesign.GlobalPFSIC (coordinate coordinate_normSq)
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1200000

theorem difference_normSq {d : ℕ} (w : Fin (d+1) → ℂ) (hw : pureStateNormSq w = 1) :
    pureStateNormSq (w - coordinate 0) = 2 * (1 - (w 0).re) := by
  simp only [pureStateNormSq, Pi.sub_apply, Complex.normSq_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  change pureStateNormSq w + pureStateNormSq (coordinate 0) -
    2 * (∑ i, (w i * (starRingEnd ℂ) (coordinate 0 i)).re) = _
  rw [hw]
  have hc : pureStateNormSq (coordinate (0 : Fin (d+1))) = 1 := coordinate_normSq 0
  rw [hc]
  simp only [coordinate, Pi.single_apply, map_one, map_zero,
    mul_ite, mul_one, mul_zero, apply_ite, Complex.zero_re,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem reflection_sends_reference {d : ℕ} (w : Fin (d+1) → ℂ)
    (hw : pureStateNormSq w = 1) (hreal : (w 0).im = 0) (hne : w ≠ coordinate 0) :
    (reflection (w-coordinate 0)).mulVec (coordinate 0) = w := by
  let u := w-coordinate 0
  have hu : u ≠ 0 := sub_ne_zero.mpr hne
  have hn : (pureStateNormSq u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive u hu))
  have hd : (pureStateNormSq u : ℂ) = 2 * (1 - ((w 0).re : ℂ)) := by
    rw [difference_normSq w hw]
    push_cast
    rfl
  have ha : basisBornAmplitude u (coordinate 0) = ((w 0).re : ℂ) - 1 := by
    simp [basisBornAmplitude, u, coordinate, Pi.single_apply, Complex.star_def]
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, hreal]
  have hcoef : 2 / (pureStateNormSq u : ℂ) * basisBornAmplitude u (coordinate 0) = -1 := by
    rw [ha]
    apply (div_mul_eq_mul_div _ _ _).trans
    apply (div_eq_iff hn).mpr
    rw [hd]
    ring
  rw [reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, density_mulVec,
    smul_smul, hcoef]
  simp [u]

def rawWeights (d : ℕ) : Fin (d+1) → ℂ := fun i => (i.val+1 : ℕ)
def referenceVector (d : ℕ) : Fin (d+1) → ℂ := ProjectiveStateGeometry.normalize (rawWeights d)

theorem rawWeights_ne_zero (d : ℕ) : rawWeights d ≠ 0 := by
  intro h
  have he := congrFun h 0
  norm_num [rawWeights] at he

theorem referenceVector_normSq (d : ℕ) : pureStateNormSq (referenceVector d) = 1 :=
  normalize_normSq _ (rawWeights_ne_zero d)

theorem referenceVector_zero_real (d : ℕ) : (referenceVector d 0).im = 0 := by
  simp [referenceVector, ProjectiveStateGeometry.normalize, rawWeights, Complex.inv_im]

theorem referenceVector_ne_coordinate (d : ℕ) (hd : 0 < d) : referenceVector d ≠ coordinate 0 := by
  intro he
  let i : Fin (d+1) := ⟨1, by omega⟩
  have hp := normSq_positive (rawWeights d) (rawWeights_ne_zero d)
  have hs : (Real.sqrt (pureStateNormSq (rawWeights d)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hp))
  have hi := congrFun he i
  have hini : i ≠ 0 := by intro h; have hh := congrArg Fin.val h; simp [i] at hh
  simp only [referenceVector, ProjectiveStateGeometry.normalize, Pi.smul_apply, smul_eq_mul, rawWeights,
    coordinate, Pi.single_apply, if_neg hini, Pi.zero_apply] at hi
  have hw : (↑(i.val+1) : ℂ) ≠ 0 := by exact_mod_cast (by omega : i.val+1 ≠ 0)
  exact (mul_ne_zero (inv_ne_zero hs) hw) hi

def referenceRotation (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  reflection (referenceVector d-coordinate 0)

theorem referenceRotation_unitary (d : ℕ) (hd : 0 < d) :
    referenceRotation d ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  reflection_unitary _ (sub_ne_zero.mpr (referenceVector_ne_coordinate d hd))

theorem referenceRotation_adjoint_reference (d : ℕ) (hd : 0 < d) :
    (referenceRotation d).conjTranspose.mulVec (coordinate 0) = referenceVector d := by
  rw [referenceRotation, reflection_selfadjoint]
  exact reflection_sends_reference _ (referenceVector_normSq d)
    (referenceVector_zero_real d) (referenceVector_ne_coordinate d hd)

theorem referenceVector_real (d : ℕ) (i : Fin (d+1)) :
    (referenceVector d i).im=0 := by
  simp [referenceVector,ProjectiveStateGeometry.normalize,rawWeights,
    Pi.smul_apply,smul_eq_mul]

theorem referenceRotation_real (d : ℕ) (i j : Fin (d+1)) :
    (referenceRotation d i j).im=0 := by
  have hc (k : Fin (d+1)) : (coordinate (0 : Fin (d+1)) k).im=0 := by
    by_cases hk : k=0 <;> simp [coordinate,Pi.single_apply,hk]
  by_cases hij : i=j <;>
    simp [referenceRotation,reflection,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      rankOneDensity,Complex.mul_im,Complex.div_im,Complex.star_def,
      referenceVector_real,hc,Matrix.one_apply,hij]

end
end QubitOracle.Paper.ReferenceReflection
