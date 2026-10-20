import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.Paper.PureStateFoundations
/-! # The pure-state controller applied to the actual Hermitian RLS estimate -/

namespace QubitOracle.AdaptiveDesign.PureMatrixController

open Filter
open QubitOracle.Paper
open GlobalPFSICHermitian
open scoped Topology Matrix.Norms.Frobenius

noncomputable section

def hermitianController (d : ℕ) (raw : HermitianSpace (d+1)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ := controllerFrame d (toMatrix raw)

theorem hermitianController_unitary (d : ℕ) (raw : HermitianSpace (d+1)) :
    hermitianController d raw ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  controllerFrame_unitary d (toMatrix raw)

theorem hermitianController_firstProjector_tendsto (d : ℕ) (truth : PureVector d)
    (theta0 : HermitianSpace (d+1)) (htruth : toMatrix theta0 = rankOneDensity truth.val)
    (raw : ℕ → HermitianSpace (d+1))
    (hraw : Tendsto raw atTop (𝓝 theta0)) :
    Tendsto (fun n => GlobalPFSIC.projector (fun i => hermitianController d (raw n) i 0))
      atTop (𝓝 (rankOneDensity truth.val)) := by
  have hcontinuous : Continuous (fun A : HermitianSpace (d+1) =>
      (toMatrix A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) :=
    (toMatrixLinear (d+1)).continuous_of_finiteDimensional
  apply controllerFrame_firstProjector_tendsto d truth (fun n => toMatrix (raw n))
  simpa only [Function.comp_def, htruth] using hcontinuous.continuousAt.tendsto.comp hraw

end

end QubitOracle.AdaptiveDesign.PureMatrixController
