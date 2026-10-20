import QubitOracle.AdaptiveDesign.AdaptiveBornRegularModel
import QubitOracle.AdaptiveDesign.QubitEffectRepresentation
import QubitOracle.AdaptiveDesign.WeightedInformationOptimization
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.P1BuresOptimality
/-! Eigenvalue bounds for the actual qubit information relative to the
SLD metric, for every finite complete positive measurement. -/
namespace QubitOracle.AdaptiveDesign.MixedRelativeInformation
open QubitOracle.Paper
open scoped BigOperators MatrixOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {O : Type} [Fintype O]

theorem information_positive (P : QubitBlochPOVM O) (r : Fin 3 → ℝ)
    (hr : blochNormSq r<1) : (qubitClassicalFisher r P).PosSemidef := by
  unfold qubitClassicalFisher
  apply Matrix.posSemidef_sum
  intro y hy
  have ho : (blochOuter (P.vector y)).PosSemidef := by
    change (Matrix.vecMulVec (P.vector y) (P.vector y)).PosSemidef
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (P.vector y)
  apply ho.smul
  unfold safeInv
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (AdaptiveBornRegularModel.mixed_probability_nonnegative P r hr y)

def relativeInformation (P : QubitBlochPOVM O) (r : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  CFC.sqrt (qubitSLDFisherInv r)*qubitClassicalFisher r P*CFC.sqrt (qubitSLDFisherInv r)

theorem relative_positive (P : QubitBlochPOVM O) (r : Fin 3 → ℝ)
    (hr : blochNormSq r<1) : (relativeInformation P r).PosSemidef := by
  have h := (information_positive P r hr).mul_mul_conjTranspose_same (CFC.sqrt (qubitSLDFisherInv r))
  unfold relativeInformation
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    WeightedInformationOptimization.sqrt_transpose] using h

theorem relative_trace (P : QubitBlochPOVM O) (r : Fin 3 → ℝ)
    (hr : blochNormSq r<1) : (relativeInformation P r).trace≤1 := by
  unfold relativeInformation
  rw [Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self _ (P1.qubitSLDFisherInv_posDef r hr).posSemidef.nonneg]
  exact qubit_interior_gillMassar r P hr

theorem eigenvalues_in_unit_interval {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.PosSemidef) (ht : A.trace≤1) (i : I) :
    0≤hA.isHermitian.eigenvalues i ∧ hA.isHermitian.eigenvalues i≤1 := by
  constructor
  · exact hA.eigenvalues_nonneg i
  · have hs : ∑ j, hA.isHermitian.eigenvalues j=A.trace := by
      simpa using hA.isHermitian.trace_eq_sum_eigenvalues.symm
    calc
      _ ≤ ∑ j, hA.isHermitian.eigenvalues j :=
        Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
      _ = A.trace := hs
      _ ≤ 1 := ht

theorem all_qubit_relative_eigenvalues (P : FinitePOVM (Fin 2) O)
    (r : Fin 3 → ℝ) (hr : blochNormSq r<1) (i : Fin 3) :
    let B := QubitEffectRepresentation.ofPOVM P
    let hp := relative_positive B r hr
    0≤hp.isHermitian.eigenvalues i ∧ hp.isHermitian.eigenvalues i≤1 :=
  eigenvalues_in_unit_interval _ (relative_positive _ r hr) (relative_trace _ r hr) i

end
end QubitOracle.AdaptiveDesign.MixedRelativeInformation
