import QubitOracle.AdaptiveDesign.ElementaryPVMIdentification
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.Paper.ElementaryPVMBases
import QubitOracle.Paper.ElementaryReferenceAlgebra
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.ReferenceReflection
/-! The explicit positive overlap and its attained lower bound, for the
exact elementary basis family in Appendix S4.1. The normalizer is the
sum of squares of the positive, distinct integer coordinates.
-/
namespace QubitOracle.Paper.ReferenceRegularity
open QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra
  ElementaryPVMBases ReferenceReflection
open QubitOracle.AdaptiveDesign.ElementaryPVMIdentification
open QubitOracle.AdaptiveDesign.GlobalPFSIC (coordinate)
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1500000

def cSquared (d : ℕ) : ℝ := pureStateNormSq (rawWeights d)

theorem rawWeights_apply (d : ℕ) (i : Fin (d+1)) :
    rawWeights d i = ((i.val+1 : ℝ) : ℂ) := by
  simp [rawWeights]

theorem cSquared_formula (d : ℕ) : cSquared d = ∑ i : Fin (d+1), (i.val+1 : ℝ)^2 := by
  simp only [cSquared, pureStateNormSq, rawWeights_apply, Complex.normSq_ofReal, ← pow_two]

theorem cSquared_positive (d : ℕ) : 0 < cSquared d :=
  normSq_positive _ (rawWeights_ne_zero d)

theorem amplitude_coordinate {D : ℕ} (v : Fin D → ℂ) (k : Fin D) :
    basisBornAmplitude v (coordinate k) = star (v k) := by
  simp [basisBornAmplitude, coordinate, Pi.single_apply]

theorem amplitude_balanced {D : ℕ} (v : Fin D → ℂ) (r s : Fin D) (q : ℂ) :
    basisBornAmplitude v (balanced (coordinate r) (q • coordinate s)) =
      (Real.sqrt 2 : ℂ)⁻¹ * (star (v r) + q * star (v s)) := by
  simp only [basisBornAmplitude, balanced, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp [coordinate, Pi.single_apply, Finset.sum_ite_eq', mul_assoc, mul_comm, mul_left_comm]

theorem raw_coordinate_lower (d : ℕ) (k : Fin (d+1)) :
    1 ≤ Complex.normSq (basisBornAmplitude (rawWeights d) (coordinate k)) := by
  rw [amplitude_coordinate]
  simp only [rawWeights_apply, Complex.star_def, Complex.conj_ofReal,
    Complex.normSq_ofReal, ← pow_two]
  have hp : (1 : ℝ) ≤ (k.val+1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ k.val+1)
  nlinarith

theorem raw_real_pair_lower {d : ℕ} (r s : Fin (d+1)) (hrs : r < s)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    1/2 ≤ Complex.normSq (basisBornAmplitude (rawWeights d)
      (balanced (coordinate r) ((sign : ℂ) • coordinate s))) := by
  rw [amplitude_balanced]
  have hn : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    simp [Complex.normSq_ofReal, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hm : (1 : ℝ) ≤ (r.val+1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ r.val+1)
  have hd : (r.val+1 : ℝ) + 1 ≤ (s.val+1 : ℝ) := by
    exact_mod_cast (show r.val+1+1 ≤ s.val+1 by omega)
  simp only [Complex.normSq_mul, map_inv₀, hn, rawWeights_apply, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.normSq_ofReal]
  rcases hsign with rfl | rfl <;> norm_num <;> nlinarith

theorem raw_imag_pair_lower {d : ℕ} (r s : Fin (d+1)) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    1/2 ≤ Complex.normSq (basisBornAmplitude (rawWeights d)
      (balanced (coordinate r) (((sign : ℂ)*Complex.I) • coordinate s))) := by
  rw [amplitude_balanced]
  have hn : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    simp [Complex.normSq_ofReal, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hm : (1 : ℝ) ≤ (r.val+1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ r.val+1)
  have hs : (1 : ℝ) ≤ (s.val+1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ s.val+1)
  simp only [Complex.normSq_mul, map_inv₀, hn, rawWeights_apply, Complex.star_def, Complex.conj_ofReal]
  rcases hsign with rfl | rfl <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem raw_basis_lower {d : ℕ} (l : BasisLabel (d+1)) (k : Fin (d+1)) :
    1/2 ≤ Complex.normSq (basisBornAmplitude (rawWeights d) (basisVector l k)) := by
  rcases l with _ | ⟨b,p⟩
  · rw [coordinate_vector]
    linarith [raw_coordinate_lower d k]
  · by_cases hk : k = p.val.1
    · subst k
      rw [pair_first]
      cases b
      · simpa using raw_real_pair_lower p.val.1 p.val.2 p.property 1 (Or.inl rfl)
      · simpa using raw_imag_pair_lower p.val.1 p.val.2 1 (Or.inl rfl)
    · by_cases hks : k = p.val.2
      · subst k
        rw [pair_second]
        cases b
        · simpa only [Bool.false_eq_true, ↓reduceIte, neg_smul, Complex.ofReal_neg,
            Complex.ofReal_one] using raw_real_pair_lower p.val.1 p.val.2 p.property (-1) (Or.inr rfl)
        · simpa only [↓reduceIte, neg_smul, Complex.ofReal_neg, Complex.ofReal_one,
            neg_mul, one_mul] using raw_imag_pair_lower p.val.1 p.val.2 (-1) (Or.inr rfl)
      · have hb : basisVector (.inr (b,p)) k = coordinate k :=
          pairVectors_other _ _ _ hk hks _
        rw [hb]
        linarith [raw_coordinate_lower d k]

theorem normalized_amplitude_normSq (d : ℕ) (v : Fin (d+1) → ℂ) :
    Complex.normSq (basisBornAmplitude (referenceVector d) v) =
      (cSquared d)⁻¹ * Complex.normSq (basisBornAmplitude (rawWeights d) v) := by
  have he : basisBornAmplitude (referenceVector d) v =
      (Real.sqrt (cSquared d) : ℂ)⁻¹ * basisBornAmplitude (rawWeights d) v := by
    simp only [referenceVector, ProjectiveStateGeometry.normalize, basisBornAmplitude,
      Pi.smul_apply, smul_eq_mul, cSquared, star_mul, star_inv₀, Complex.star_def,
      Complex.conj_ofReal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, Complex.normSq_mul, map_inv₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (cSquared_positive d).le]

theorem reference_basis_lower (d : ℕ) (l : BasisLabel (d+1)) (k : Fin (d+1)) :
    1 / (2*cSquared d) ≤ Complex.normSq (basisBornAmplitude (referenceVector d) (basisVector l k)) := by
  rw [normalized_amplitude_normSq]
  have h := mul_le_mul_of_nonneg_left (raw_basis_lower l k) (inv_nonneg.mpr (cSquared_positive d).le)
  calc
    1 / (2*cSquared d) = (cSquared d)⁻¹ * (1/2) := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    _ ≤ _ := h

theorem raw_adjacent_difference (d : ℕ) (hd : 0 < d) :
    Complex.normSq (basisBornAmplitude (rawWeights d)
      (balanced (coordinate 0) (-coordinate (⟨1,by omega⟩ : Fin (d+1))))) = 1/2 := by
  have h := amplitude_balanced (rawWeights d) (0 : Fin (d+1)) ⟨1,by omega⟩ (-1)
  simp only [neg_one_smul] at h
  rw [h]
  norm_num [rawWeights, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

end
end QubitOracle.Paper.ReferenceRegularity
