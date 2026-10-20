import QubitOracle.AdaptiveDesign.PureChartDomain
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.P2BornFisherIdentification
import QubitOracle.AdaptiveDesign.PVMGeometry
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureChartCoverage
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-! A concrete finite atlas: the pure-state charts centred at the columns
of any unitary basis cover all pure projectors. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def basisPureVector {d : ℕ} (U : GlobalPFSICBorn.Action d) (k : Fin (d+1)) : PureVector d :=
  ⟨U.matrix.mulVec (coordinate k), by
    change pureStateNormSq (U.matrix.mulVec (coordinate k))=1
    rw [pureStateNormSq_unitary_mulVec U.matrix U.unitary]
    exact coordinate_normSq k⟩

theorem basisPureVector_parameter {d : ℕ} (U : GlobalPFSICBorn.Action d) (k : Fin (d+1)) :
    (pureParameter d (basisPureVector U k)).val=PVMGeometry.basisEffect U k := by
  apply toMatrix_injective
  rw [PVMGeometry.basisEffect_matrix]
  change projector (U.matrix.mulVec (coordinate k))=projector (fun i => U.matrix i k)
  congr 1
  funext i
  simp [coordinate,Matrix.mulVec_single_one]

theorem basis_charts_cover {d : ℕ} (U : GlobalPFSICBorn.Action d) (h : PureVector d) :
    ∃ k : Fin (d+1), ∃ u : EuclideanSpace ℝ (TangentIndex d),
      tangentRadiusSq u < 4 ∧ trueChartMatrix (basisPureVector U k) u=(pureParameter d h).val := by
  have hex : ∃ k, 0 < PVMGeometry.basisProbability (pureParameter d h) U k := by
    by_contra hh
    push_neg at hh
    have hs := Finset.sum_nonpos (s := Finset.univ) (fun k _ => hh k)
    rw [PVMGeometry.basisProbability_sum] at hs
    norm_num at hs
  obtain ⟨k,hk⟩ := hex
  have hov : 0 < ⟪(pureParameter d (basisPureVector U k)).val,(pureParameter d h).val⟫_ℝ := by
    rw [basisPureVector_parameter]
    exact hk
  exact ⟨k,amplitudeCoordinates (basisPureVector U k) (pureParameter d h).val,
    amplitudeCoordinates_in_domain _ _ hov,chart_amplitudeCoordinates _ _ hov⟩

end
end QubitOracle.AdaptiveDesign.TangentGLS
