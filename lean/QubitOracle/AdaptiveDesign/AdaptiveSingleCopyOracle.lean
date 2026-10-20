import QubitOracle.AdaptiveDesign.AdaptiveBornRegularModel
import QubitOracle.AdaptiveDesign.GeneralWeightedOracle
import QubitOracle.AdaptiveDesign.InformationCoordinateInvariance
import QubitOracle.AdaptiveDesign.PureFisherLoewner
import QubitOracle.Paper.P1BuresOptimality
import QubitOracle.Paper.QubitFoundations

/-!
# Theorem 5.1: the oracle bound for adaptive single-copy measurements

A policy takes the complete past record to a finite POVM. In particular,
it cannot depend on the unknown parameter with that record held fixed.
Classical setting randomization is included in the POVM outcome label.

The endpoints derive the Gill--Massar budget from positivity and
completeness of the effects. No information-budget, score-identity,
inverse-covariance, rank-one-effect, or positive-outcome assumption is
an input. Finite-record regularity comes from the actual Born model;
local unbiasedness remains an explicit condition on the estimator.
-/

namespace QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle

open QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open FiniteRegularOracle AdaptiveBornRegularModel
open scoped BigOperators InnerProductSpace Topology MatrixOrder

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {Y : Type} [Fintype Y]

/-- The usual positive-support Fisher formula follows from the score
definition, including at outcomes whose probability is zero. -/
theorem information_eq_safeRatio {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : RegularModel ι Ω) (i j : ι) :
    P.information i j = ∑ w, safeRatio (P.mass P.theta w)
      (P.derivative w i * P.derivative w j) := by
  simp only [RegularModel.information, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec, Matrix.of_apply, smul_eq_mul, RegularModel.score]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hp : P.mass P.theta w = 0
  · simp [safeRatio, hp]
  · simp only [safeRatio, if_neg hp]
    field_simp

/-- Identification with the actual qubit Born Fisher matrix. -/
theorem mixedModel_information (theta : Fin 3 → ℝ)
    (htheta : blochNormSq theta < 1) (P : FinitePOVM (Fin 2) Y) :
    (mixedModel theta htheta P).val.information =
      qubitClassicalFisher theta (QubitEffectRepresentation.ofPOVM P) := by
  ext i j
  rw [information_eq_safeRatio]
  have hmem : theta ∈ mixedDomain := htheta
  simp only [mixedModel, RegularModel.ofNeighborhood, if_pos hmem,
    qubitClassicalFisher, Matrix.sum_apply, Matrix.smul_apply, blochOuter,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro y _
  exact (safeInv_mul _ _).symm

/-- Gill--Massar for every conditional mixed-qubit measurement, derived
from its positive complete effects rather than assumed. -/
theorem mixedModel_gillMassar (theta : Fin 3 → ℝ)
    (htheta : blochNormSq theta < 1) (P : FinitePOVM (Fin 2) Y) :
    Matrix.trace (qubitSLDFisherInv theta *
      (mixedModel theta htheta P).val.information) ≤ 1 := by
  rw [mixedModel_information]
  exact QubitEffectRepresentation.all_qubit_gillMassar P theta htheta

/-- The matrix in the oracle constant is the actual SLD trace pairing. -/
theorem mixed_quantumInformation (theta : Fin 3 → ℝ)
    (htheta : blochNormSq theta < 1) :
    qubitSLDFisherFromSLD theta = (qubitSLDFisherInv theta)⁻¹ :=
  (qubitSLDFisherFromSLD_eq_formula theta htheta).trans
    (qubitSLDFisher_eq_inv theta htheta)

/-- The mixed-qubit alternative of Theorem 5.1, for every finite
adaptive single-copy policy and every positive-semidefinite loss weight. -/
theorem theorem_5_1_mixed (theta : Fin 3 → ℝ)
    (htheta : blochNormSq theta < 1)
    (policy : List Y → FinitePOVM (Fin 2) Y)
    (W : Matrix (Fin 3) (Fin 3) ℝ) (hW : W.PosSemidef)
    (n : ℕ) (_hn : 1 ≤ n) (T : Record Y n → Fin 3 → ℝ)
    (hT : (mixedAdaptiveModel theta htheta policy n).val.LocallyUnbiased T) :
    oracleConstant W (qubitSLDFisherFromSLD theta) 1 ≤
      (n : ℝ) * (mixedAdaptiveModel theta htheta policy n).val.quadraticRisk W T := by
  rw [mixed_quantumInformation theta htheta]
  have hH := (P1.qubitSLDFisherInv_posDef theta htheta).inv
  letI : Invertible (qubitSLDFisherInv theta) :=
    (P1.qubitSLDFisherInv_posDef theta htheta).isUnit.invertible
  apply general_adaptive_oracle_qfi theta
    (fun h => mixedModel theta htheta (policy h)) W _ hW hH 1 (by norm_num)
  · intro history
    simpa only [Matrix.inv_inv_of_invertible] using
      mixedModel_gillMassar theta htheta (policy history)
  · exact hT

/-- The Born differential for any real tangent-coordinate direction. -/
theorem pureDerivative_inner {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) (y : Y) (u : TangentIndex d → ℝ) :
    ⟪GeneralPOVM.responseVector P (identityAction d) y, pureDerivative truth u⟫_ℝ =
      ∑ k, u k * GeneralPOVM.gradient P ((trueFrame d truth).conjTranspose) y k := by
  simp only [pureDerivative, ContinuousLinearMap.comp_apply,
    smul_apply, real_inner_smul_right]
  rw [real_inner_comm, trueLift_inner, trueCoordinate_responseVector]
  simp [coordinates, identityAction, PiLp.inner_apply, mul_comm]

/-- The Born derivative in the normalized true-state amplitude chart. -/
theorem pureModel_derivative {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) (y : Y) (j : TangentIndex d) :
    (pureModel truth P).val.derivative y j =
      GeneralPOVM.gradient P ((trueFrame d truth).conjTranspose) y j := by
  change ⟪GeneralPOVM.responseVector P (identityAction d) y,
    pureDerivative truth (Pi.single j 1)⟫_ℝ = _
  rw [pureDerivative_inner]
  simp [Pi.single_apply]

theorem pureChart_zero {d : ℕ} (truth : PureVector d) :
    pureChart truth 0 = (pureParameter d truth).val := by
  have hzero : referenceChartMatrix (0 : EuclideanSpace ℝ (TangentIndex d)) =
      (pureParameter d (knownReference d)).val := by
    apply toMatrix_injective
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [referenceChartMatrix, pureParameter, chartState, tangentRadiusSq,
        knownReference, GlobalPFSIC.projector, rankOneDensity, Matrix.vecMulVec,
        Pi.single_apply]
    all_goals apply Complex.ext <;> simp
  simpa only [pureChart, Function.comp_apply, map_zero, trueChartMatrix, hzero] using
    trueFrame_referenceParameter truth

/-- Probability at the true state, including zero-probability outcomes. -/
theorem pureModel_probability {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) (y : Y) :
    (pureModel truth P).val.mass 0 y =
      GeneralPOVM.mass P ((trueFrame d truth).conjTranspose) y := by
  rw [pureModel_mass truth P 0 (mem_of_mem_nhds (pureDomain_nhds d)), pureChart_zero]
  have he : GeneralPOVM.responseVector P (identityAction d) y =
      GeneralPOVM.effectVector P y := by
    apply toMatrix_injective
    change (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) *
      toMatrix (GeneralPOVM.effectVector P y) * (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ).conjTranspose = _
    simp
  have h := GeneralPOVM.bornProbability_pure_eq_mass P truth (identityAction d) y
  unfold GeneralPOVM.bornProbability at h
  rw [he] at h
  simpa only [identityAction, Matrix.mul_one] using h

/-- Identification of the regular classical information with the
physical finite-POVM Fisher matrix in true-state coordinates. -/
theorem pureModel_information {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) :
    (pureModel truth P).val.information =
      GeneralPOVM.fisher P ((trueFrame d truth).conjTranspose) := by
  ext i j
  rw [information_eq_safeRatio]
  change (∑ y, safeRatio ((pureModel truth P).val.mass 0 y)
    ((pureModel truth P).val.derivative y i *
      (pureModel truth P).val.derivative y j)) = _
  simp only [pureModel_probability, pureModel_derivative, GeneralPOVM.fisher]

/-- Gill--Massar holds for arbitrary finite effects and arbitrary pure
truths, with no positivity-of-probabilities assumption. -/
theorem pureModel_gillMassar {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) :
    Matrix.trace (pureModel truth P).val.information ≤ (d : ℝ) := by
  rw [pureModel_information]
  exact rankOne_reference_gillMassar
    (PureFisherLoewner.rotated P ((trueFrame d truth).conjTranspose)
      (by
        apply Matrix.mem_unitaryGroup_iff.mpr
        simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
          Matrix.mem_unitaryGroup_iff'.mp (trueFrame_unitary d truth)))

/-- The pure-state alternative of Theorem 5.1 in the normalized amplitude
chart, where the SLD information matrix at the truth is the identity. -/
theorem theorem_5_1_pure_normalized {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (policy : List Y → FinitePOVM (Fin (d+1)) Y)
    (W : Matrix (TangentIndex d) (TangentIndex d) ℝ) (hW : W.PosSemidef)
    (n : ℕ) (_hn : 1 ≤ n) (T : Record Y n → TangentIndex d → ℝ)
    (hT : (pureAdaptiveModel truth policy n).val.LocallyUnbiased T) :
    oracleConstant W 1 (d : ℝ) ≤
      (n : ℝ) * (pureAdaptiveModel truth policy n).val.quadraticRisk W T := by
  apply general_adaptive_oracle_qfi 0 (fun h => pureModel truth (policy h))
    W 1 hW Matrix.PosDef.one (d : ℝ) (by exact_mod_cast hd)
  · intro history
    simpa using pureModel_gillMassar truth (policy history)
  · exact hT

end
end QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle
