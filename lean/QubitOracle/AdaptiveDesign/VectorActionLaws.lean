import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.Paper.FinitePOVMBounds

/-! The rewritten paper uses vectors as actions. This module connects
those vectors to the existing exact finite Born protocols. A frame and
allocation form a design; the selected mixed action is just one unit
axis. A pure action is a unit vector and its completion is deterministic.
-/
namespace QubitOracle.AdaptiveDesign.VectorActionLaws
open QubitOracle QubitOracle.Paper MeasureTheory ProbabilityTheory
  PureMatrixController GlobalPFSICHermitian
open scoped BigOperators ComplexOrder
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

abbrev MixedVectorAction := {a : Fin 3 → ℝ // blochNormSq a = 1}

def selectedAxis (design : P1Weighted.Action) (k : Fin 3) : MixedVectorAction :=
  ⟨P1Weighted.axis design k,design.frame.unit_axes k⟩

def mixedDesign (design : P1Weighted.Action) : Measure MixedVectorAction :=
  ∑ k, ENNReal.ofReal (design.weight k) • Measure.dirac (selectedAxis design k)

instance mixedDesign_probability (design : P1Weighted.Action) :
    IsProbabilityMeasure (mixedDesign design) where
  measure_univ := by
    simp only [mixedDesign,Measure.finset_sum_apply,Measure.smul_apply,
      measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => design.nonneg k),
      design.total,ENNReal.ofReal_one]

theorem mixedDesign_event (design : P1Weighted.Action) (C : Set MixedVectorAction)
    (hC : MeasurableSet C) :
    mixedDesign design C = ∑ k, ENNReal.ofReal (design.weight k) *
      (if selectedAxis design k ∈ C then 1 else 0) := by
  classical
  simp [mixedDesign,Measure.finset_sum_apply,Measure.smul_apply,
    Measure.dirac_apply' _ hC,smul_eq_mul,Set.indicator]

theorem mixed_joint_born_formula (θ : OneQubitPhysicalParameter)
    (design : P1Weighted.Action) (k : Fin 3) (y : BinaryOutcome) :
    P1Weighted.probability θ design (k,y) =
      design.weight k * (1+y.sign*blochDot (selectedAxis design k).val θ.val)/2 := by
  simp only [P1Weighted.probability,binaryBornProbability,generalAxisBornProjection,
    selectedAxis,P1Weighted.axis]
  ring

theorem mixed_axis_born_trace (θ : Fin 3 → ℝ) (a : MixedVectorAction) (y : BinaryOutcome) :
    qubitBornTrace θ a.val y.sign = (1+y.sign*blochDot a.val θ)/2 :=
  qubitBornTrace_eq θ a.val y.sign

theorem mixed_binary_mean (z : ℝ) :
    ∑ y : BinaryOutcome, binaryBornProbability z y * y.sign = z := by
  rw [sum_binaryOutcome]
  simp [binaryBornProbability,BinaryOutcome.sign]
  ring

theorem mixed_binary_variance (z : ℝ) :
    ∑ y : BinaryOutcome, binaryBornProbability z y * (y.sign-z)^2 = 1-z^2 := by
  rw [sum_binaryOutcome]
  simp [binaryBornProbability,BinaryOutcome.sign]
  ring

abbrev PureVectorAction (d : ℕ) := PureVector d

def completion {d : ℕ} (a : PureVectorAction d) : GlobalPFSICBorn.Action d :=
  ⟨ExactHouseholder.matrix a.val,ExactHouseholder.matrix_unitary a.val a.property⟩

theorem completion_firstColumn {d : ℕ} (a : PureVectorAction d) :
    (fun i => (completion a).matrix i 0) = a.val :=
  ExactHouseholder.matrix_firstColumn a.val

theorem completion_injective {d : ℕ} : Function.Injective (@completion d) := by
  intro a b hab
  apply Subtype.ext
  have hm := congrArg GlobalPFSICBorn.Action.matrix hab
  have hc := congrArg (fun M : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => fun i => M i 0) hm
  simpa only [completion_firstColumn] using hc

def pureDesign {d : ℕ} (a : PureVectorAction d) : Measure (PureVectorAction d) := Measure.dirac a

theorem pureDesign_event {d : ℕ} (a : PureVectorAction d) (C : Set (PureVectorAction d))
    (hC : MeasurableSet C) : pureDesign a C = if a ∈ C then 1 else 0 :=
  Measure.dirac_apply' a hC

def branchGate (d : ℕ) (b : Bool) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  if b then PhasePair.gate d else 1

def pureEffects {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (a : PureVectorAction d) (z : Bool × O) :=
  GeneralPOVM.effect (PhasePair.paired F) (completion a).matrix z

theorem pure_effect_formula {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (a : PureVectorAction d) (b : Bool) (y : O) :
    pureEffects F a (b,y) = (1/2 : ℝ) •
      ((completion a).matrix * (branchGate d b).conjTranspose * F.effect y *
        branchGate d b * (completion a).matrix.conjTranspose) := by
  cases b <;>
    simp [pureEffects,GeneralPOVM.effect,branchGate,PhasePair.paired_effect_false,
      PhasePair.paired_effect_true,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]

theorem pure_effects_positive_complete {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (a : PureVectorAction d) :
    (∀ z, (pureEffects F a z).PosSemidef) ∧ ∑ z, pureEffects F a z = 1 :=
  ⟨fun z => GeneralPOVM.effect_positive _ _ z,
    GeneralPOVM.effect_complete _ _ (completion a).unitary⟩

theorem pure_born_trace {d : ℕ} {O : Type} [Fintype O]
    (F : FinitePOVM (Fin (d+1)) O) (θ a : PureVectorAction d) (z : Bool × O) :
    (GeneralPOVM.bornProbability (PhasePair.paired F) θ (completion a) z : ℂ) =
      Matrix.trace (rankOneDensity θ.val * pureEffects F a z) :=
  GeneralPOVM.bornProbability_eq_trace _ _ _ _

theorem completion_aligned_projector {d : ℕ} (a : PureVectorAction d) :
    (completion a).matrix * rankOneDensity (GlobalPFSIC.coordinate 0) *
      (completion a).matrix.conjTranspose = rankOneDensity a.val := by
  have hc := completion_firstColumn a
  ext i j
  simp [Matrix.mul_apply,rankOneDensity,GlobalPFSIC.coordinate,Pi.single_apply,
    Matrix.conjTranspose_apply,← hc]

end
end QubitOracle.AdaptiveDesign.VectorActionLaws
