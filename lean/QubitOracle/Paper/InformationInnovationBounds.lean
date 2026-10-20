import QubitOracle.Paper.HistoryDependentInformationConvergence

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

/-- A probability-weighted mean inherits any uniform coordinate bound on the
per-setting information matrices. -/
theorem historyPolicyMeanInformation_entry_norm_le
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hInformation : ∀ history setting i j,
      ‖information history setting i j‖ ≤ B)
    (history : SequentialHistory M Y) (i j : D) :
    ‖historyPolicyMeanInformation q information history i j‖ ≤ B := by
  have hEntry :
      historyPolicyMeanInformation q information history i j =
        ∑ m, q.mass history m * information history m i j := by
    simp [historyPolicyMeanInformation, Matrix.sum_apply]
  rw [hEntry]
  calc
    ‖∑ m, q.mass history m * information history m i j‖
        ≤ ∑ m, ‖q.mass history m * information history m i j‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ m, q.mass history m * ‖information history m i j‖ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (q.mass_nonneg history m)]
    _ ≤ ∑ m, q.mass history m * B := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (hInformation history m i j) (q.mass_nonneg history m)
    _ = B := by
      rw [← Finset.sum_mul, q.sum_mass, one_mul]

/-- Subtracting the predictable probability-weighted mean costs at most a
factor of two in a uniform coordinate bound. -/
theorem historyInformationInnovation_entry_norm_le_two_mul
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hInformation : ∀ history setting i j,
      ‖information history setting i j‖ ≤ B)
    (history : SequentialHistory M Y) (setting : M) (i j : D) :
    ‖historyInformationInnovation q information history setting i j‖ ≤ 2 * B := by
  change ‖information history setting i j -
    historyPolicyMeanInformation q information history i j‖ ≤ 2 * B
  calc
    ‖information history setting i j -
        historyPolicyMeanInformation q information history i j‖
        ≤ ‖information history setting i j‖ +
          ‖historyPolicyMeanInformation q information history i j‖ :=
      norm_sub_le _ _
    _ ≤ B + B := add_le_add (hInformation history setting i j)
      (historyPolicyMeanInformation_entry_norm_le q information B hB hInformation history i j)
    _ = 2 * B := by ring

/-- A uniform bound on actual per-setting information supplies the uniform
innovation hypothesis required by the adaptive information strong law. -/
theorem historyInformationInnovation_uniformBound_of_informationBound
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (hInformationBound : ∃ B, 0 ≤ B ∧ ∀ history setting i j,
      ‖information history setting i j‖ ≤ B) :
    ∃ C, 0 ≤ C ∧ ∀ history setting i j,
      ‖historyInformationInnovation q information history setting i j‖ ≤ C := by
  obtain ⟨B, hB, hInformation⟩ := hInformationBound
  refine ⟨2 * B, mul_nonneg (by norm_num) hB, ?_⟩
  exact historyInformationInnovation_entry_norm_le_two_mul
    q information B hB hInformation

end

end QubitOracle.Paper
