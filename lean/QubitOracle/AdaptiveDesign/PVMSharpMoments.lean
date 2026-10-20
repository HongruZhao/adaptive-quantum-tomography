-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotRegression
import QubitOracle.AdaptiveDesign.PureAmplitudeLoss

/-! Exact, dimension-free one-copy exploration variance. -/
namespace QubitOracle.AdaptiveDesign.PVMSharpMoments
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry PVMGeneralGeometry PVMPilotBorn PVMPilotSchedule PVMPilotRegression
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem basisEffect_norm {d : ℕ} (U : Action d) (k : Fin (d+1)) :
    ‖basisEffect U k‖=1 := by
  rw [basisEffect,(conjugationIsometry U.matrix U.unitary).norm_map]
  let h : PureMatrixController.PureVector d :=
    ⟨coordinate k,by
      change (∑ i,Complex.normSq (coordinate k i))=1
      simp [coordinate,Pi.single_apply]⟩
  exact TangentGLS.pureParameter_norm h


variable [PVMPilotSchedule.Schedule] {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem response_norm_square (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, ‖response a.2 o‖^2 ∂PVMPilotBorn.bornKernel theta a=epsilon a.1 := by
  change (∫ o, ‖response a.2 o‖^2 ∂finiteMassMeasure (PVMPilotBorn.bornProbability theta a)
    (PVMPilotBorn.bornProbability_nonnegative theta a) (PVMPilotBorn.bornProbability_sum theta a)) = _
  rw [integral_finiteMassMeasure,Fintype.sum_prod_type,Fintype.sum_sum_type]
  simp only [response,norm_zero,zero_pow (by norm_num : 2≠0),smul_eq_mul,mul_zero,
    Finset.sum_const_zero,zero_add,basisEffect_norm,one_pow,mul_one,
    PVMPilotBorn.bornProbability,settingWeight,settingBasis]
  simp only [← Finset.mul_sum,basisProbability_sum,mul_one,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  have hk := (PVMGeneralGeometry.exploration_card_pos d).ne'
  field_simp

theorem noise_norm_square (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, ‖noise theta a o‖^2 ∂PVMPilotBorn.bornKernel theta a=
      epsilon a.1-‖frame a.1 a.2 theta.1‖^2 := by
  let m := frame a.1 a.2 theta.1
  have hi : (∫ o, ⟪response a.2 o,m⟫_ℝ ∂PVMPilotBorn.bornKernel theta a)=‖m‖^2 := by
    calc
      _ = ∫ o, ⟪m,response a.2 o⟫_ℝ ∂PVMPilotBorn.bornKernel theta a :=
        integral_congr_ae (ae_of_all _ (fun o => real_inner_comm _ _))
      _ = _ := by rw [integral_inner Integrable.of_finite,response_mean,real_inner_self_eq_norm_sq]
  simp only [noise,norm_sub_sq_real]
  change (∫ o, ‖response a.2 o‖^2-2*⟪response a.2 o,m⟫_ℝ+‖m‖^2
    ∂PVMPilotBorn.bornKernel theta a)=epsilon a.1-‖m‖^2
  rw [integral_add (f:=fun o => ‖response a.2 o‖^2-2*⟪response a.2 o,m⟫_ℝ)
    (g:=fun _ => ‖m‖^2) Integrable.of_finite Integrable.of_finite]
  rw [integral_sub (f:=fun o => ‖response a.2 o‖^2)
    (g:=fun o => 2*⟪response a.2 o,m⟫_ℝ) Integrable.of_finite Integrable.of_finite]
  rw [integral_const_mul,hi,response_norm_square]
  simp only [integral_const,probReal_univ,one_smul]

  dsimp [m]
  ring

theorem noise_norm_square_le (theta : PhysicalParameter (d+1)) (a : ℕ × Action d) :
    ∫ o, ‖noise theta a o‖^2 ∂PVMPilotBorn.bornKernel theta a ≤ epsilon a.1 := by
  rw [noise_norm_square]
  exact sub_le_self _ (sq_nonneg _)

end
end QubitOracle.AdaptiveDesign.PVMSharpMoments

-/
