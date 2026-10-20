import Mathlib.Analysis.InnerProductSpace.Calculus
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.IntrinsicInformationGeometry
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.FiniteGillMassar
/-! Smoothness of the intrinsic Born information where all probabilities
are positive. The ambient bilinear form restricts to the pure-state tangent
space; no claim of continuity at zero-probability effects is made. -/
namespace QubitOracle.AdaptiveDesign.SmoothBornInformation
open GlobalPFSICHermitian
open scoped BigOperators InnerProductSpace
noncomputable section

variable {E V O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype O]

def ambientForm (effects : O → E) (p a b : E) : ℝ :=
  ∑ y, ⟪effects y,a⟫_ℝ * ⟪effects y,b⟫_ℝ / ⟪effects y,p⟫_ℝ

/-- Every matrix entry of the information form is smooth on the regular
region, including when the two tangent arguments vary smoothly. -/
theorem smooth_pullback (effects : O → E) (p a b : V → E) (x : V)
    (hp : ContDiffAt ℝ ⊤ p x) (ha : ContDiffAt ℝ ⊤ a x) (hb : ContDiffAt ℝ ⊤ b x)
    (hregular : ∀ y, 0<⟪effects y,p x⟫_ℝ) :
    ContDiffAt ℝ ⊤ (fun z => ambientForm effects (p z) (a z) (b z)) x := by
  apply ContDiffAt.sum
  intro y hy
  exact ((contDiffAt_const.inner ℝ ha).mul (contDiffAt_const.inner ℝ hb)).div
    (contDiffAt_const.inner ℝ hp) (hregular y).ne'

theorem ambient_smooth (effects : O → E) (p a b : E)
    (hregular : ∀ y, 0<⟪effects y,p⟫_ℝ) :
    ContDiffAt ℝ ⊤ (fun z => ambientForm effects z a b) p :=
  smooth_pullback effects id (fun _ => a) (fun _ => b) p
    contDiffAt_id contDiffAt_const contDiffAt_const hregular

theorem equals_intrinsic {d : ℕ} {Y : Type} [Fintype Y]
    (P : FinitePOVM (Fin (d+1)) Y)
    (truth : PureMatrixController.PureVector d) (U : GlobalPFSICBorn.Action d)
    (a b : HermitianSpace (d+1)) :
    ambientForm (GeneralPOVM.responseVector P U) (P2Adaptive.pureParameter d truth).val a b=
      IntrinsicInformationGeometry.fisherForm P truth U a b := by
  simp only [ambientForm,IntrinsicInformationGeometry.fisherForm,
    GeneralPOVM.bornProbability]

end
end QubitOracle.AdaptiveDesign.SmoothBornInformation
