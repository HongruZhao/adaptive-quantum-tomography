import QubitOracle.AdaptiveDesign.FiniteAdaptiveOracle
import QubitOracle.AdaptiveDesign.FiniteRegularOracle
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureChartDifferential
import QubitOracle.AdaptiveDesign.PureChartDomain
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.QubitEffectRepresentation
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.QubitFoundations
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-! The classical regular model is constructed from the actual Born law.
A history fixes the selected POVM, including any classical randomization.
Its dependence on the data is never differentiated. Local charts are
extended outside their domain only to supply a globally defined mass. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBornRegularModel
open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open FiniteRegularOracle Filter
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y]

theorem coordinate_derivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) (theta : ι → ℝ) (D : (ι → ℝ) →L[ℝ] E)
    (hD : HasFDerivAt f D theta) (j : ι) :
    HasDerivAt (fun t => f (shift theta j t)) (D (Pi.single j 1)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => shift theta j t) (Pi.single j 1) 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single j 1)).const_add theta using 1 <;>
      simp only [shift,id_eq,one_smul]
  have hD' : HasFDerivAt f D (shift theta j 0) := by simpa only [shift,zero_smul,add_zero] using hD
  have h := hD'.comp_hasDerivAt 0 hline
  simpa only [Function.comp_def] using h

def localBornModel {n : ℕ} (theta : ι → ℝ) (U : Set (ι → ℝ)) (hU : U ∈ 𝓝 theta)
    (chart : (ι → ℝ) → HermitianSpace n) (D : (ι → ℝ) →L[ℝ] HermitianSpace n)
    (hD : HasFDerivAt chart D theta) (effects : Y → HermitianSpace n)
    (hn : ∀ z ∈ U, ∀ y, 0≤⟪effects y,chart z⟫_ℝ)
    (hs : ∀ z ∈ U, ∑ y, ⟪effects y,chart z⟫_ℝ=1) : RegularModel ι Y :=
  RegularModel.ofNeighborhood theta U hU (fun z y => ⟪effects y,chart z⟫_ℝ) hn hs
    (fun y j => ⟪effects y,D (Pi.single j 1)⟫_ℝ)
    (fun y j => coordinate_derivative _ theta ((innerSL ℝ (effects y)).comp D)
      ((innerSL ℝ (effects y)).hasFDerivAt.comp theta hD) j)

def coordinates (ι : Type) [Fintype ι] : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm

def identityAction (d : ℕ) : GlobalPFSICBorn.Action d := ⟨1,by simp⟩

def pureDomain (d : ℕ) : Set (TangentIndex d → ℝ) :=
  coordinates (TangentIndex d) ⁻¹' Metric.ball 0 2

theorem pureDomain_nhds (d : ℕ) : pureDomain d ∈ 𝓝 0 := by
  exact (coordinates (TangentIndex d)).continuous.continuousAt.preimage_mem_nhds
    (by simpa using (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (TangentIndex d))
      (by norm_num : (0:ℝ)<2)))

def pureChart {d : ℕ} (truth : PureVector d) :
    (TangentIndex d → ℝ) → HermitianSpace (d+1) :=
  trueChartMatrix truth ∘ coordinates (TangentIndex d)

def pureDerivative {d : ℕ} (truth : PureVector d) :
    (TangentIndex d → ℝ) →L[ℝ] HermitianSpace (d+1) :=
  ((1/2:ℝ) • trueLift truth).comp (coordinates (TangentIndex d)).toContinuousLinearMap

theorem pureChart_derivative {d : ℕ} (truth : PureVector d) :
    HasFDerivAt (pureChart truth) (pureDerivative truth) 0 := by
  exact (trueChart_hasFDerivAt_zero truth).comp 0 (coordinates (TangentIndex d)).hasFDerivAt

def pureModel {d : ℕ} (truth : PureVector d) (P : FinitePOVM (Fin (d+1)) Y) :
    AtTruth (0 : TangentIndex d → ℝ) Y := by
  let effects := GeneralPOVM.responseVector P (identityAction d)
  have hphys (z : TangentIndex d → ℝ) (hz : z∈pureDomain d) :
      ∃ h : PureVector d, pureChart truth z=(pureParameter d h).val := by
    exact ⟨trueChartPureVector truth (coordinates (TangentIndex d) z)
      (tangentRadiusSq_lt_four_of_ball _ hz).le,trueChart_is_pure _ _ _⟩
  refine ⟨localBornModel 0 (pureDomain d) (pureDomain_nhds d)
    (pureChart truth) (pureDerivative truth) (pureChart_derivative truth) effects ?_ ?_,rfl⟩
  · intro z hz y
    obtain ⟨h,hh⟩ := hphys z hz
    rw [hh]
    exact GeneralPOVM.bornProbability_nonnegative P h (identityAction d) y
  · intro z hz
    obtain ⟨h,hh⟩ := hphys z hz
    rw [hh]
    exact GeneralPOVM.bornProbability_sum P h (identityAction d)

theorem pureModel_mass {d : ℕ} (truth : PureVector d)
    (P : FinitePOVM (Fin (d+1)) Y) (z : TangentIndex d → ℝ) (hz : z∈pureDomain d) (y : Y) :
    (pureModel truth P).val.mass z y=
      ⟪GeneralPOVM.effectVector P y,pureChart truth z⟫_ℝ := by
  simp only [pureModel,localBornModel,RegularModel.ofNeighborhood,if_pos hz,
    GeneralPOVM.responseVector,identityAction]
  congr 1
  apply toMatrix_injective
  simp

/-- Any finite adaptive tree of quantum measurements gives an actual
regular experiment in pure-state coordinates. -/
def pureAdaptiveModel {d : ℕ} (truth : PureVector d)
    (policy : List Y → FinitePOVM (Fin (d+1)) Y) (n : ℕ) (history : List Y := []) :
    AtTruth (0 : TangentIndex d → ℝ) (Record Y n) :=
  adaptiveExperiment 0 (fun h => pureModel truth (policy h)) n history

/-- Literal product of the conditional Born probabilities; the policy is
arbitrary and may encode all previous estimate and batch updates. -/
def pureRecordMass {d : ℕ} (truth : PureVector d)
    (policy : List Y → FinitePOVM (Fin (d+1)) Y) (z : TangentIndex d → ℝ) :
    (n : ℕ) → List Y → Record Y n → ℝ
  | 0,_,_ => 1
  | n+1,h,w => ⟪GeneralPOVM.effectVector (policy h) w.1,pureChart truth z⟫_ℝ *
      pureRecordMass truth policy z n (w.1::h) w.2

theorem pureAdaptiveModel_exact_mass {d : ℕ} (truth : PureVector d)
    (policy : List Y → FinitePOVM (Fin (d+1)) Y) (z : TangentIndex d → ℝ)
    (hz : z∈pureDomain d) (n : ℕ) (history : List Y) (w : Record Y n) :
    (pureAdaptiveModel truth policy n history).val.mass z w=
      pureRecordMass truth policy z n history w := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
    change (pureModel truth (policy history)).val.mass z w.1 *
      (pureAdaptiveModel truth policy n (w.1::history)).val.mass z w.2=_
    rw [pureModel_mass _ _ _ hz,ih]
    rfl

def mixedDomain : Set (Fin 3 → ℝ) := {z | blochNormSq z<1}

theorem mixedDomain_nhds (theta : Fin 3 → ℝ) (htheta : blochNormSq theta<1) :
    mixedDomain ∈ 𝓝 theta := by
  have hc : Continuous blochNormSq := by unfold blochNormSq; fun_prop
  exact (isOpen_lt hc continuous_const).mem_nhds htheta

theorem mixed_probability_nonnegative (P : QubitBlochPOVM Y)
    (z : Fin 3 → ℝ) (hz : blochNormSq z<1) (y : Y) :
    0≤qubitProbability z P y := by
  have hc := bloch_cauchy_schwarz z (P.vector y)
  have hv := P.vector_normSq_le y
  have hw := P.weight_nonneg y
  have hnorm : 0≤blochNormSq (P.vector y) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hz.le hnorm
  dsimp [qubitProbability]
  nlinarith

theorem mixed_probability_total (P : QubitBlochPOVM Y) (z : Fin 3 → ℝ) :
    ∑ y, qubitProbability z P y=1 := by
  simp only [qubitProbability,Finset.sum_add_distrib,P.sum_weight,blochDot]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,P.sum_vector,mul_zero,Finset.sum_const_zero,add_zero]

theorem mixed_probability_derivative (P : QubitBlochPOVM Y)
    (theta : Fin 3 → ℝ) (y : Y) (j : Fin 3) :
    HasDerivAt (fun t => qubitProbability (shift theta j t) P y) (P.vector y j) 0 := by
  have he : (fun t => qubitProbability (shift theta j t) P y)=
      (fun t => qubitProbability theta P y+t*P.vector y j) := by
    funext t
    simp [qubitProbability,blochDot,shift,Pi.single_apply,add_mul,
      Finset.sum_add_distrib,Finset.mul_sum,mul_assoc,add_assoc]
  rw [he]
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (P.vector y j)).const_add
    (qubitProbability theta P y)

def mixedModel (theta : Fin 3 → ℝ) (htheta : blochNormSq theta<1)
    (P : FinitePOVM (Fin 2) Y) : AtTruth theta Y :=
  ⟨RegularModel.ofNeighborhood theta mixedDomain (mixedDomain_nhds theta htheta)
    (fun z y => qubitProbability z (QubitEffectRepresentation.ofPOVM P) y)
    (fun z hz y => mixed_probability_nonnegative _ z hz y)
    (fun z _ => mixed_probability_total _ z)
    (fun y j => (QubitEffectRepresentation.ofPOVM P).vector y j)
    (mixed_probability_derivative _ theta),rfl⟩

theorem mixedModel_mass (theta : Fin 3 → ℝ) (htheta : blochNormSq theta<1)
    (P : FinitePOVM (Fin 2) Y) (z : Fin 3 → ℝ) (hz : z∈mixedDomain) (y : Y) :
    (mixedModel theta htheta P).val.mass z y=
      (Matrix.trace (P.effect y*qubitDensityMatrix z)).re := by
  simp only [mixedModel,RegularModel.ofNeighborhood,if_pos hz]
  exact QubitEffectRepresentation.probability_is_born P z y

def mixedAdaptiveModel (theta : Fin 3 → ℝ) (htheta : blochNormSq theta<1)
    (policy : List Y → FinitePOVM (Fin 2) Y) (n : ℕ) (history : List Y := []) :
    AtTruth theta (Record Y n) :=
  adaptiveExperiment theta (fun h => mixedModel theta htheta (policy h)) n history

def mixedRecordMass (policy : List Y → FinitePOVM (Fin 2) Y) (z : Fin 3 → ℝ) :
    (n : ℕ) → List Y → Record Y n → ℝ
  | 0,_,_ => 1
  | n+1,h,w => (Matrix.trace ((policy h).effect w.1*qubitDensityMatrix z)).re *
      mixedRecordMass policy z n (w.1::h) w.2

theorem mixedAdaptiveModel_exact_mass (theta : Fin 3 → ℝ) (htheta : blochNormSq theta<1)
    (policy : List Y → FinitePOVM (Fin 2) Y) (z : Fin 3 → ℝ)
    (hz : z∈mixedDomain) (n : ℕ) (history : List Y) (w : Record Y n) :
    (mixedAdaptiveModel theta htheta policy n history).val.mass z w=
      mixedRecordMass policy z n history w := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
    change (mixedModel theta htheta (policy history)).val.mass z w.1 *
      (mixedAdaptiveModel theta htheta policy n (w.1::history)).val.mass z w.2=_
    rw [mixedModel_mass _ _ _ _ hz,ih]
    rfl

end
end QubitOracle.AdaptiveDesign.AdaptiveBornRegularModel
