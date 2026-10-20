import QubitOracle.AdaptiveDesign.ElementaryPVMIdentification

/-! The literal entrywise expansion in Appendix S4.1, including the
minus sign in front of the imaginary projector differences. -/
namespace QubitOracle.Paper.HermitianEntryExpansion
open QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra
open QubitOracle.AdaptiveDesign GlobalPFSIC ElementaryPVMIdentification
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ}

def matrixUnit (r s : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.vecMulVec (coordinate r) (star (coordinate s))

theorem matrixUnit_entry (r s i j : Fin D) :
    matrixUnit r s i j = if i=r ∧ j=s then 1 else 0 := by
  simp [matrixUnit,Matrix.vecMulVec_apply,coordinate,Pi.single_apply]
  split_ifs <;> simp_all

theorem sum_units (c : Fin D → Fin D → ℂ) :
    (∑ r, ∑ s, c r s • matrixUnit r s) = c := by
  ext i j
  simp [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,matrixUnit_entry,
    ite_and,eq_comm]

theorem diagonal_units (A : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (∑ r, A r r • matrixUnit r r) i j = if i=j then A i i else 0 := by
  simp [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,matrixUnit_entry,
    ite_and,eq_comm]

theorem upper_units (c : Fin D → Fin D → ℂ) (i j : Fin D) :
    (∑ r, ∑ s, if r < s then c r s • matrixUnit r s else 0) i j =
      if i < j then c i j else 0 := by
  have h := congrFun (congrFun (sum_units
    (fun r s => if r < s then c r s else 0)) i) j
  simpa only [ite_smul,zero_smul] using h

theorem lower_units (c : Fin D → Fin D → ℂ) (i j : Fin D) :
    (∑ r, ∑ s, if r < s then c r s • matrixUnit s r else 0) i j =
      if j < i then c j i else 0 := by
  have h := congrFun (congrFun (sum_units
    (fun r s => if s < r then c s r else 0)) i) j
  rw [Finset.sum_comm]
  simpa only [ite_smul,zero_smul] using h

theorem hermitian_entries (A : Matrix (Fin D) (Fin D) ℂ) (hA : A.IsHermitian) :
    A = (∑ r, A r r • matrixUnit r r) +
      (∑ r, ∑ s, if r<s then A r s • matrixUnit r s else 0) +
      (∑ r, ∑ s, if r<s then star (A r s) • matrixUnit s r else 0) := by
  ext i j
  rw [Matrix.add_apply,Matrix.add_apply,diagonal_units,upper_units,lower_units]
  rcases lt_trichotomy i j with h | h | h
  · simp [h,ne_of_lt h,not_lt_of_gt h]
  · subst j; simp
  · have he : star (A j i) = A i j := congrFun (congrFun hA i) j
    simp [h,ne_of_gt h,not_lt_of_gt h,he]

def realDifference (r s : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  rankOneDensity (balanced (coordinate r) (coordinate s)) -
  rankOneDensity (balanced (coordinate r) (-(coordinate s)))

def imaginaryDifference (r s : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  rankOneDensity (balanced (coordinate r) (Complex.I • coordinate s)) -
  rankOneDensity (balanced (coordinate r) (-(Complex.I • coordinate s)))

theorem realDifference_formula (r s : Fin D) :
    realDifference r s = matrixUnit r s + matrixUnit s r :=
  real_pair_difference _ _

theorem imaginaryDifference_formula (r s : Fin D) :
    imaginaryDifference r s = Complex.I • (matrixUnit s r - matrixUnit r s) :=
  imaginary_pair_difference _ _

theorem complex_entry_expansion (z : ℂ) (r s : Fin D) :
    (z.re : ℂ) • realDifference r s - (z.im : ℂ) • imaginaryDifference r s =
      z • matrixUnit r s + star z • matrixUnit s r := by
  rw [realDifference_formula,imaginaryDifference_formula]
  ext i j
  change (z.re : ℂ) * (matrixUnit r s i j + matrixUnit s r i j) -
    (z.im : ℂ) * (Complex.I * (matrixUnit s r i j-matrixUnit r s i j)) =
    z*matrixUnit r s i j + star z*matrixUnit s r i j
  have hc : star z = (z.re : ℂ) - (z.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [hc]
  linear_combination (matrixUnit r s i j) * (Complex.re_add_im z)

theorem explicit_projector_expansion (A : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.IsHermitian) :
    A = (∑ r, (A r r).re • rankOneDensity (coordinate r)) +
      ∑ r, ∑ s, if r<s then
        (A r s).re • realDifference r s - (A r s).im • imaginaryDifference r s
      else 0 := by
  have hd (r : Fin D) : (A r r).re • rankOneDensity (coordinate r) =
      A r r • matrixUnit r r := by
    have he : (A r r).im=0 := by
      have hh : star (A r r)=A r r := congrFun (congrFun hA r) r
      have hi := congrArg Complex.im hh
      simp [Complex.star_def] at hi
      linarith
    have hr : ((A r r).re : ℂ)=A r r := by
      simpa only [he,Complex.ofReal_zero,zero_mul,add_zero] using
        Complex.re_add_im (A r r)
    ext i j
    change ((A r r).re : ℂ) * (coordinate r i * star (coordinate r j)) =
      A r r * (coordinate r i * star (coordinate r j))
    rw [hr]
  simp_rw [hd]
  have hreal (r s : Fin D) :
      (A r s).re • realDifference r s - (A r s).im • imaginaryDifference r s =
        ((A r s).re : ℂ) • realDifference r s - ((A r s).im : ℂ) • imaginaryDifference r s := by
    ext i j
    rfl
  simp_rw [hreal]
  simp_rw [complex_entry_expansion]
  calc
    A = (∑ r, A r r • matrixUnit r r) +
      (∑ r, ∑ s, if r < s then A r s • matrixUnit r s else 0) +
      (∑ r, ∑ s, if r < s then star (A r s) • matrixUnit s r else 0) :=
      hermitian_entries A hA
    _ = _ := by
      rw [add_assoc]
      congr 1
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp

end
end QubitOracle.Paper.HermitianEntryExpansion
