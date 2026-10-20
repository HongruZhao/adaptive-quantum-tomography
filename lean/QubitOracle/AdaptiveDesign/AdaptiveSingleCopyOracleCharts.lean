import QubitOracle.AdaptiveDesign.AdaptiveBornRegularModel
import QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle
import QubitOracle.AdaptiveDesign.FiniteAdaptiveOracle
import QubitOracle.AdaptiveDesign.FiniteRegularOracle
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GeneralWeightedOracle
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.InformationCoordinateInvariance
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureChartDomain
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.PureSLDMetric
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.QubitFoundations
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-!
# Theorem 5.1 in arbitrary smooth pure-state coordinates

`PureChartData` exposes the actual locally physical parametrization and
its invertible first derivative in normalized tangent coordinates. These
are chart and Born-regularity data, not statistical information bounds.
The SLD information matrix, the classical information pullback, and the
Gill--Massar budget are proved from those data.
-/

namespace QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle

open QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open FiniteRegularOracle AdaptiveBornRegularModel
open Matrix
open scoped BigOperators InnerProductSpace Topology MatrixOrder

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {Y : Type} [Fintype Y]

/-- Local pure-state parametrization, with its invertible tangent
Jacobian written in the normalized true-state amplitude coordinates. -/
structure PureChartData (d : ℕ) where
  truth : PureVector d
  theta : TangentIndex d → ℝ
  domain : Set (TangentIndex d → ℝ)
  domain_nhds : domain ∈ 𝓝 theta
  state : (TangentIndex d → ℝ) → HermitianSpace (d+1)
  state_at_truth : state theta = (pureParameter d truth).val
  physical : ∀ z ∈ domain, ∃ h : PureVector d, state z = (pureParameter d h).val
  jacobian : Matrix (TangentIndex d) (TangentIndex d) ℝ
  jacobian_invertible : IsUnit jacobian.det
  hasDerivative : HasFDerivAt state
    ((pureDerivative truth).comp (Matrix.toLin' jacobian).toContinuousLinearMap) theta

namespace PureChartData

variable {d : ℕ} (C : PureChartData d)

def quantumInformation : Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  C.jacobian.transpose * C.jacobian

/-- This matrix is the SLD metric of the actual chart differential. -/
theorem quantumInformation_entry (i j : TangentIndex d) :
    C.quantumInformation i j =
      PureSLDMetric.metricFromSLD C.truth
        (PureSLDMetric.normalizedLift C.truth
          (coordinates (TangentIndex d) (C.jacobian *ᵥ Pi.single i 1)))
        (PureSLDMetric.normalizedLift C.truth
          (coordinates (TangentIndex d) (C.jacobian *ᵥ Pi.single j 1))) := by
  rw [PureSLDMetric.normalized_metric]
  simp [quantumInformation, Matrix.mul_apply, Matrix.transpose_apply,
    coordinates, PiLp.inner_apply, mul_comm]

theorem differential_basis (i : TangentIndex d) :
    fderiv ℝ C.state C.theta (Pi.single i 1) =
      (PureSLDMetric.normalizedLift C.truth
        (coordinates (TangentIndex d) (C.jacobian *ᵥ Pi.single i 1))).val := by
  rw [C.hasDerivative.fderiv]
  rfl

/-- The QFI entries are the SLD pairing of the derivatives of the given
physical parametrization, rather than a freely chosen metric matrix. -/
theorem quantumInformation_from_derivative (i j : TangentIndex d) :
    C.quantumInformation i j = PureSLDMetric.metricFromSLD C.truth
      ⟨fderiv ℝ C.state C.theta (Pi.single i 1), by
        rw [C.differential_basis]
        exact (PureSLDMetric.normalizedLift C.truth _).property⟩
      ⟨fderiv ℝ C.state C.theta (Pi.single j 1), by
        rw [C.differential_basis]
        exact (PureSLDMetric.normalizedLift C.truth _).property⟩ := by
  simpa only [C.differential_basis] using C.quantumInformation_entry i j

theorem quantumInformation_posDef : C.quantumInformation.PosDef := by
  have hJ : IsUnit C.jacobian :=
    (Matrix.isUnit_iff_isUnit_det C.jacobian).mpr C.jacobian_invertible
  have h := (Matrix.PosDef.one :
    (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ).PosDef).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hJ)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one,
    quantumInformation] using h

/-- The actual one-copy Born model in these coordinates. -/
def model (P : FinitePOVM (Fin (d+1)) Y) : AtTruth C.theta Y := by
  let effects := GeneralPOVM.responseVector P (identityAction d)
  refine ⟨localBornModel C.theta C.domain C.domain_nhds C.state
    ((pureDerivative C.truth).comp (Matrix.toLin' C.jacobian).toContinuousLinearMap)
    C.hasDerivative effects ?_ ?_, rfl⟩
  · intro z hz y
    obtain ⟨h, hh⟩ := C.physical z hz
    rw [hh]
    exact GeneralPOVM.bornProbability_nonnegative P h (identityAction d) y
  · intro z hz
    obtain ⟨h, hh⟩ := C.physical z hz
    rw [hh]
    exact GeneralPOVM.bornProbability_sum P h (identityAction d)

theorem model_probability (P : FinitePOVM (Fin (d+1)) Y) (y : Y) :
    (C.model P).val.mass C.theta y = (pureModel C.truth P).val.mass 0 y := by
  have hmem := mem_of_mem_nhds C.domain_nhds
  simp only [model, localBornModel, RegularModel.ofNeighborhood, if_pos hmem,
    C.state_at_truth]
  rw [pureModel_mass C.truth P 0 (mem_of_mem_nhds (pureDomain_nhds d)),
    pureChart_zero]
  congr 1
  apply toMatrix_injective
  change (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) *
    toMatrix (GeneralPOVM.effectVector P y) * (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ).conjTranspose = _
  simp

theorem model_derivative (P : FinitePOVM (Fin (d+1)) Y)
    (y : Y) (j : TangentIndex d) :
    (C.model P).val.derivative y j =
      ∑ k, C.jacobian k j * (pureModel C.truth P).val.derivative y k := by
  change ⟪GeneralPOVM.responseVector P (identityAction d) y,
    pureDerivative C.truth ((Matrix.toLin' C.jacobian).toContinuousLinearMap
      (Pi.single j 1))⟫_ℝ = _
  rw [pureDerivative_inner]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply',
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    pureModel_derivative]

/-- Information pullback proved from Born probabilities and derivatives. -/
theorem model_information (P : FinitePOVM (Fin (d+1)) Y) :
    (C.model P).val.information = C.jacobian.transpose *
      (pureModel C.truth P).val.information * C.jacobian := by
  have htheta : (C.model P).val.theta = C.theta := (C.model P).property
  have hzero : (pureModel C.truth P).val.theta = 0 := (pureModel C.truth P).property
  have hscore (y : Y) : (C.model P).val.score y =
      C.jacobian.transpose *ᵥ (pureModel C.truth P).val.score y := by
    ext j
    simp only [RegularModel.score, htheta, hzero, model_probability, model_derivative,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_div, mul_div_assoc]
  unfold RegularModel.information
  simp only [htheta, hzero, model_probability, hscore, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ext i j
  simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- No Gill--Massar hypothesis is supplied for a general pure-state
chart: it follows from the physical POVM and coordinate invariance. -/
theorem model_gillMassar (P : FinitePOVM (Fin (d+1)) Y) :
    Matrix.trace (C.quantumInformation⁻¹ * (C.model P).val.information) ≤ (d : ℝ) := by
  rw [model_information]
  have h := InformationCoordinateInvariance.trace_information_invariant
    (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)
    (pureModel C.truth P).val.information C.jacobian C.jacobian_invertible
  simp only [Matrix.mul_one, inv_one, Matrix.one_mul] at h
  rw [show C.quantumInformation = C.jacobian.transpose * C.jacobian from rfl, h]
  exact pureModel_gillMassar C.truth P

def adaptiveModel (policy : List Y → FinitePOVM (Fin (d+1)) Y) (n : ℕ) :
    AtTruth C.theta (Record Y n) :=
  adaptiveExperiment C.theta (fun h => C.model (policy h)) n []

end PureChartData

/-- The paper's normalized amplitude chart supplies the chart data at
every pure truth; the general chart interface has an explicit witness. -/
def normalizedPureChart {d : ℕ} (truth : PureVector d) : PureChartData d where
  truth := truth
  theta := 0
  domain := pureDomain d
  domain_nhds := pureDomain_nhds d
  state := pureChart truth
  state_at_truth := pureChart_zero truth
  physical := by
    intro z hz
    exact ⟨trueChartPureVector truth (coordinates (TangentIndex d) z)
      (tangentRadiusSq_lt_four_of_ball _ hz).le, trueChart_is_pure _ _ _⟩
  jacobian := 1
  jacobian_invertible := by simp
  hasDerivative := by
    convert pureChart_derivative truth using 1
    ext u
    simp [Matrix.toLin'_apply']

/-- The pure-state alternative of revised Theorem 5.1 in an arbitrary
smooth local parametrization. The inputs are the physical chart, the
finite adaptive POVMs, a PSD loss, and local unbiasedness; no information
inequality is assumed. Here D=d+1, so the budget is d=D-1. -/
theorem theorem_5_1_pure {d : ℕ} (hd : 0 < d) (C : PureChartData d)
    (policy : List Y → FinitePOVM (Fin (d+1)) Y)
    (W : Matrix (TangentIndex d) (TangentIndex d) ℝ) (hW : W.PosSemidef)
    (n : ℕ) (_hn : 1 ≤ n) (T : Record Y n → TangentIndex d → ℝ)
    (hT : (C.adaptiveModel policy n).val.LocallyUnbiased T) :
    oracleConstant W C.quantumInformation (d : ℝ) ≤
      (n : ℝ) * (C.adaptiveModel policy n).val.quadraticRisk W T := by
  apply general_adaptive_oracle_qfi C.theta (fun h => C.model (policy h))
    W C.quantumInformation hW C.quantumInformation_posDef (d : ℝ) (by exact_mod_cast hd)
  · intro history
    exact C.model_gillMassar (policy history)
  · exact hT

/-- The two quantum models in Theorem 5.1. The constructor fields are
state/chart data; no constructor contains an information inequality. -/
inductive QuantumModel where
  | mixed (theta : Fin 3 → ℝ) (interior : blochNormSq theta < 1)
  | pure (d : ℕ) (positive_dimension : 0 < d) (chart : PureChartData d)

namespace QuantumModel

def Index : QuantumModel → Type
  | .mixed _ _ => Fin 3
  | .pure d _ _ => TangentIndex d

instance (M : QuantumModel) : Fintype M.Index := by
  cases M <;> dsimp [Index] <;> infer_instance

instance (M : QuantumModel) : DecidableEq M.Index := by
  cases M <;> dsimp [Index] <;> infer_instance

def systemDimension : QuantumModel → ℕ
  | .mixed _ _ => 2
  | .pure d _ _ => d+1

def quantumInformation (M : QuantumModel) : Matrix M.Index M.Index ℝ :=
  match M with
  | .mixed theta _ => qubitSLDFisherFromSLD theta
  | .pure _ _ C => C.quantumInformation

def experiment (M : QuantumModel)
    (policy : List Y → FinitePOVM (Fin M.systemDimension) Y) (n : ℕ) :
    RegularModel M.Index (Record Y n) :=
  match M with
  | .mixed theta interior => (mixedAdaptiveModel theta interior policy n).val
  | .pure _ _ C => (C.adaptiveModel policy n).val

end QuantumModel

/-- Revised Theorem 5.1, with its two quantum-model alternatives, full
adaptive Born records, arbitrary PSD W and local unbiasedness. The
Gill--Massar budget D-1 is a proved consequence of the single-copy POVMs.
Regularity is constructed from the smooth physical model/chart data. -/
theorem theorem_5_1 (M : QuantumModel)
    (policy : List Y → FinitePOVM (Fin M.systemDimension) Y)
    (W : Matrix M.Index M.Index ℝ) (hW : W.PosSemidef)
    (n : ℕ) (hn : 1 ≤ n) (T : Record Y n → M.Index → ℝ)
    (hT : (M.experiment policy n).LocallyUnbiased T) :
    oracleConstant W M.quantumInformation ((M.systemDimension : ℝ)-1) ≤
      (n : ℝ) * (M.experiment policy n).quadraticRisk W T := by
  cases M with
  | mixed theta interior =>
      simpa [QuantumModel.quantumInformation, QuantumModel.systemDimension,
        QuantumModel.experiment, show (2 : ℝ)-1 = 1 by norm_num] using
        theorem_5_1_mixed theta interior policy W hW n hn T hT
  | pure d hd C =>
      simpa [QuantumModel.quantumInformation, QuantumModel.systemDimension,
        QuantumModel.experiment, Nat.cast_add, Nat.cast_one] using
        theorem_5_1_pure hd C policy W hW n hn T hT

end
end QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle
