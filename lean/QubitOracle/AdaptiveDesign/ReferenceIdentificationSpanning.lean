import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.TracelessHermitianDimension

/-! C1 as real spanning, and its necessary number of outcomes. -/
namespace QubitOracle.AdaptiveDesign.ReferenceIdentificationSpanning
open QubitOracle GeneralPOVM GlobalPFSICHermitian
open scoped InnerProductSpace
noncomputable section

theorem identifying_iff_span {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) :
    Identifying F ↔ Submodule.span ℝ (Set.range (effectVector F)) = ⊤ := by
  constructor
  · intro hF
    rw [← Submodule.orthogonal_eq_bot_iff]
    apply (Submodule.eq_bot_iff _).mpr
    intro A hA
    exact hF A (fun o => Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self o)) hA)
  · intro hs A hA
    have hsub : Submodule.span ℝ (Set.range (effectVector F)) ≤ (ℝ ∙ A)ᗮ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨o,rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hA o)
    have ho : A ∈ (ℝ ∙ A)ᗮ := hsub (by rw [hs]; trivial)
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_span_singleton_self A) ho)

theorem identifying_iff_real_combination {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) :
    Identifying F ↔ ∀ A : HermitianSpace (d+1), ∃ c : O → ℝ,
      ∑ o, c o • effectVector F o = A := by
  rw [identifying_iff_span]
  constructor
  · intro hs A
    apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    rw [hs]
    trivial
  · intro h
    apply top_unique
    intro A _
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr (h A)

theorem identifying_outcome_cardinality {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (hF : Identifying F) :
    (d+1)^2 ≤ Fintype.card O := by
  exact GeneralPOVM.identifying_card_bound F hF

end
end QubitOracle.AdaptiveDesign.ReferenceIdentificationSpanning
