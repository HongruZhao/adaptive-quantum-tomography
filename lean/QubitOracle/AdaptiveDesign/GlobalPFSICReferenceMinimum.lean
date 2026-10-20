import QubitOracle.AdaptiveDesign.GlobalPFSICFisher

/-! The exact minimum reference probability in the optional library. -/
namespace QubitOracle.AdaptiveDesign.GlobalPFSIC
open QubitOracle
noncomputable section

theorem effect_reference_probability_value {d : ℕ} (hd : 0 < d) (o : Outcome d) :
    (effect o 0 0).re =
      (if o.1 then 3 else 1) / (16*(d:ℝ)*(4*d+1)) := by
  rw [effect_reference_entry]
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  cases hb : o.1 <;> simp only [latitude, effectWeight, hb, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp
  all_goals ring

theorem effect_reference_probability_minimum {d : ℕ} (hd : 0 < d) :
    (∀ o : Outcome d, 1 / (16*(d:ℝ)*(4*d+1)) ≤ (effect o 0 0).re) ∧
      ∃ o : Outcome d, (effect o 0 0).re = 1 / (16*(d:ℝ)*(4*d+1)) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  constructor
  · intro o
    rw [effect_reference_probability_value hd]
    cases o.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact le_rfl
    · apply div_le_div_of_nonneg_right (by norm_num)
      positivity
  · let k : Fin d := ⟨0,hd⟩
    have hi : Nonempty (LibraryIndex d) := by
      have hc := library_card d
      apply Fintype.card_pos_iff.mp
      rw [hc]
      positivity
    let o : Outcome d := (false, 0, Classical.choice hi)
    exact ⟨o, by rw [effect_reference_probability_value hd]; rfl⟩

end
end QubitOracle.AdaptiveDesign.GlobalPFSIC
