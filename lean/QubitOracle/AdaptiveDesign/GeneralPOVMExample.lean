import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive

/-! The explicit POVM is a verified instance of the general assumptions. -/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open QubitOracle QubitOracle.Paper GlobalPFSIC
open scoped BigOperators InnerProductSpace
noncomputable section

theorem explicit_identifying (d : ℕ) (hd : 0 < d) : Identifying (measurementPOVM d hd) := by
  intro A hA
  exact GlobalPFSICHermitian.effectVector_separates hd A hA

theorem explicit_regular (d : ℕ) (hd : 0 < d) : Regular (measurementPOVM d hd) := by
  intro o
  rw [measurementPOVM_referenceProbability]
  exact mul_pos (effectWeight_pos d hd) (latitude_pos d o.1)

theorem explicit_fisherSymmetric (d : ℕ) (hd : 0 < d) :
    FisherSymmetric (measurementPOVM d hd) := measurementPOVM_referenceFisher d hd

/-- Nonemptiness of the general apparatus class for every D=d+1 >= 2. -/
theorem explicit_satisfies_conditions (d : ℕ) (hd : 0 < d) :
    Identifying (measurementPOVM d hd) ∧ Regular (measurementPOVM d hd) ∧
    FisherSymmetric (measurementPOVM d hd) :=
  ⟨explicit_identifying d hd, explicit_regular d hd, explicit_fisherSymmetric d hd⟩

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
