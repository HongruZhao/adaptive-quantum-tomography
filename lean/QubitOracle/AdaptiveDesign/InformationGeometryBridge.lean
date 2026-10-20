import QubitOracle.AdaptiveDesign.IntrinsicInformationGeometry
import QubitOracle.Paper.InformationDefinitions
import QubitOracle.Paper.InformationSmoothness
import QubitOracle.Paper.SLDLinearAlgebra

/-! Specialize the score/support formulas to the manuscript's actual
finite POVM and Born probabilities. No replacement statistical model is
introduced and no positive-support conclusion is assumed.
-/
namespace QubitOracle.AdaptiveDesign.InformationGeometryBridge
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open InformationDefinitions IntrinsicInformationGeometry
open scoped BigOperators InnerProductSpace
noncomputable section
variable {d : ℕ} {O : Type} [Fintype O]

theorem fisherForm_positive_support (P : FinitePOVM (Fin (d+1)) O)
    (truth : PureVector d) (U : GlobalPFSICBorn.Action d) (A B : HermitianSpace (d+1)) :
    fisherForm P truth U A B = directionalFisher (GeneralPOVM.bornProbability P truth U)
      (fun y => ⟪GeneralPOVM.responseVector P U y, A⟫_ℝ)
      (fun y => ⟪GeneralPOVM.responseVector P U y, B⟫_ℝ) := by
  exact (fisher_eq_total_division _ _ _ (GeneralPOVM.bornProbability_nonnegative P truth U)).symm

theorem fisherForm_expected_scores (P : FinitePOVM (Fin (d+1)) O)
    (truth : PureVector d) (U : GlobalPFSICBorn.Action d) (A B : HermitianSpace (d+1)) :
    fisherForm P truth U A B = ∑ y, GeneralPOVM.bornProbability P truth U y *
      directionalScore (GeneralPOVM.bornProbability P truth U)
        (fun z => ⟪GeneralPOVM.responseVector P U z, A⟫_ℝ) y *
      directionalScore (GeneralPOVM.bornProbability P truth U)
        (fun z => ⟪GeneralPOVM.responseVector P U z, B⟫_ℝ) y := by
  rw [fisherForm_positive_support, fisher_eq_expected_scores]

theorem fisherForm_positive_iff (P : FinitePOVM (Fin (d+1)) O)
    (truth : PureVector d) (U : GlobalPFSICBorn.Action d) (A : HermitianSpace (d+1)) :
    0 < fisherForm P truth U A A ↔ ∃ y,
      0 < GeneralPOVM.bornProbability P truth U y ∧
      ⟪GeneralPOVM.responseVector P U y, A⟫_ℝ ≠ 0 := by
  rw [fisherForm_positive_support, fisher_positive_iff]

end
end QubitOracle.AdaptiveDesign.InformationGeometryBridge
