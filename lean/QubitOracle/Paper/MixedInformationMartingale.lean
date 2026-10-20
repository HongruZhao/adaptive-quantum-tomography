import QubitOracle.Paper.MartingaleStrongLaw
import QubitOracle.Paper.MixedInformationBound
import QubitOracle.Paper.SequentialMartingale

/-!
# Mixed-qubit information martingale

This file proves all deterministic bounds needed to apply the martingale
strong law to the randomized setting information.  The remaining premise is
the coordinatewise martingale property on the infinite path-space
realization of the finite policy kernel.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

theorem matrix_entry_sq_le_frobeniusSq
    (M : OracleMatrix) (i j : Fin 3) :
    (M i j) ^ 2 ≤ frobeniusSq M := by
  unfold frobeniusSq frobeniusInner
  have hrow : M i j * M i j ≤ ∑ k, M i k * M i k :=
    Finset.single_le_sum
      (fun k _ => mul_self_nonneg (M i k)) (Finset.mem_univ j)
  have hall : (∑ k, M i k * M i k) ≤
      ∑ r, ∑ k, M r k * M r k :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg fun k _ => mul_self_nonneg (M r k))
      (Finset.mem_univ i)
  simpa [pow_two] using hrow.trans hall

theorem abs_matrix_entry_le_frobeniusNorm
    (M : OracleMatrix) (i j : Fin 3) :
    |M i j| ≤ mixedInformationFrobeniusNorm M := by
  unfold mixedInformationFrobeniusNorm
  apply (Real.le_sqrt (abs_nonneg _) (frobeniusSq_nonneg M)).2
  simpa [sq_abs] using matrix_entry_sq_le_frobeniusSq M i j

theorem mixedAxisInformation_entry_norm_le
    (r u : Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (i j : Fin 3) :
    ‖QubitOracle.mixedAxisFisher r u i j‖ ≤
      (1 - QubitOracle.blochNormSq r)⁻¹ := by
  rw [Real.norm_eq_abs]
  exact (abs_matrix_entry_le_frobeniusNorm
    (QubitOracle.mixedAxisFisher r u) i j).trans
      (mixedAxisInformationFrobeniusNorm_le r u hr hu)

def mixedPolicyMeanInformation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (history : SequentialHistory M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ) : OracleMatrix :=
  finitePolicyExpectation q history
    (fun m => QubitOracle.mixedAxisFisher r (axis m))

theorem mixedPolicyMeanInformation_entry_norm_le
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (history : SequentialHistory M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (i j : Fin 3) :
    ‖mixedPolicyMeanInformation q history r axis i j‖ ≤
      (1 - QubitOracle.blochNormSq r)⁻¹ := by
  rw [Real.norm_eq_abs]
  unfold mixedPolicyMeanInformation finitePolicyExpectation
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    |∑ m, q.mass history m * QubitOracle.mixedAxisFisher r (axis m) i j| ≤
        ∑ m, |q.mass history m *
          QubitOracle.mixedAxisFisher r (axis m) i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ m, q.mass history m *
          ‖QubitOracle.mixedAxisFisher r (axis m) i j‖ := by
      apply Finset.sum_congr rfl
      intro m _
      rw [abs_mul, abs_of_nonneg (q.mass_nonneg history m),
        Real.norm_eq_abs]
    _ ≤ ∑ m, q.mass history m *
          (1 - QubitOracle.blochNormSq r)⁻¹ := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left
        (mixedAxisInformation_entry_norm_le r (axis m) hr (haxis m) i j)
        (q.mass_nonneg history m)
    _ = (1 - QubitOracle.blochNormSq r)⁻¹ := by
      rw [← Finset.sum_mul, q.sum_mass, one_mul]

def mixedInformationMartingaleIncrement
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : ℕ → Type*) := history

/-- Information innovation for a realized setting and its predictable policy
mean. -/
def mixedInformationInnovation
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : SequentialHistory M Y)
    (setting : M) : OracleMatrix :=
  QubitOracle.mixedAxisFisher r (axis setting) -
    mixedPolicyMeanInformation q history r axis

theorem mixedInformationInnovation_entry_norm_le
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : SequentialHistory M Y)
    (setting : M)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (i j : Fin 3) :
    ‖mixedInformationInnovation q r axis history setting i j‖ ≤
      2 * (1 - QubitOracle.blochNormSq r)⁻¹ := by
  unfold mixedInformationInnovation
  exact (norm_sub_le _ _).trans <| by
    have hreal := mixedAxisInformation_entry_norm_le
      r (axis setting) hr (haxis setting) i j
    have hmean := mixedPolicyMeanInformation_entry_norm_le
      q history r axis hr haxis i j
    linarith

/-- Strong law for the actual finite-policy information innovations.  The
only unproved protocol bridge is `hmartingale`, which connects the finite
kernel construction to an infinite filtered probability space. -/
theorem mixedInformationInnovation_strongLaw
    {Omega M Y : Type*} [MeasurableSpace Omega]
    [Fintype M]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ)
    (axis : M → Fin 3 → ℝ)
    (history : ℕ → Omega → SequentialHistory M Y)
    (setting : ℕ → Omega → M)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (hmartingale : ∀ i j, Martingale
      (scalarMartingalePartialSum
        (fun n omega => mixedInformationInnovation q r axis
          (history n omega) (setting n omega) i j))
      filtration mu) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            mixedInformationInnovation q r axis
              (history k omega) (setting k omega))
        atTop (nhds 0) := by
  apply finiteMatrix_martingale_strongLaw_of_uniform_bound
    mu filtration
    (fun n omega => mixedInformationInnovation q r axis
      (history n omega) (setting n omega))
    hmartingale
  refine ⟨2 * (1 - QubitOracle.blochNormSq r)⁻¹, ?_, ?_⟩
  · have hgap : 0 < 1 - QubitOracle.blochNormSq r := sub_pos.mpr hr
    positivity
  · intro n omega i j
    exact mixedInformationInnovation_entry_norm_le
      q r axis (history n omega) (setting n omega) hr haxis i j

end

end QubitOracle.Paper
