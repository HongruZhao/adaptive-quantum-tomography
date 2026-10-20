import QubitOracle.AdaptiveDesign.PureTangentDimension

/-! The literal tangent least-squares solve and its reported projector
are independent of the phase of the preliminary unit eigenvector. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem tangentSpace_eq_of_projector_eq {d : ℕ} (h g : PureVector d)
    (hp : rankOneDensity h.val=rankOneDensity g.val) : tangentSpace h=tangentSpace g := by
  ext A
  simp only [tangentSpace_mem,hp]

def correctionOnSubmodule {d n : ℕ} {O : Type} [Fintype O]
    (S : Submodule ℝ (HermitianSpace (d+1))) (P : HermitianSpace (d+1))
    (data : Fin n → Record d O) (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    HermitianSpace (d+1) :=
  (fittedCorrection (fun r => S.orthogonalProjectionOnto (recordFeature data r))
    (fun r => inner ℝ (recordFeature data r) P)
    (fun r => observedIndicator data r-inner ℝ (recordFeature data r) P) floor ridge hf hr).val

theorem recordCorrection_phase_invariant {d n : ℕ} {O : Type} [Fintype O]
    (h g : PureVector d) (hp : rankOneDensity h.val=rankOneDensity g.val)
    (data : Fin n → Record d O) (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    (recordCorrection h data floor ridge hf hr).val=(recordCorrection g data floor ridge hf hr).val := by
  have ht := tangentSpace_eq_of_projector_eq h g hp
  have hP : (pureParameter d h).val=(pureParameter d g).val := toMatrix_injective hp
  change correctionOnSubmodule (tangentSpace h) (pureParameter d h).val data floor ridge hf hr=
    correctionOnSubmodule (tangentSpace g) (pureParameter d g).val data floor ridge hf hr
  rw [ht,hP]

theorem correctedState_phase_invariant {d n : ℕ} {O : Type} [Fintype O]
    (h g : PureVector d) (hp : rankOneDensity h.val=rankOneDensity g.val)
    (data : Fin n → Record d O) (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    updatedState h (recordCorrection h data floor ridge hf hr)=
      updatedState g (recordCorrection g data floor ridge hf hr) :=
  updatedState_phase_invariant h g _ _ hp (recordCorrection_phase_invariant h g hp data floor ridge hf hr)

end
end QubitOracle.AdaptiveDesign.TangentGLS
