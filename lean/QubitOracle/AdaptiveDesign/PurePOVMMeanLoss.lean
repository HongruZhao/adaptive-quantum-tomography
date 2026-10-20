import QubitOracle.AdaptiveDesign.POVMEstimatorMoments
import QubitOracle.AdaptiveDesign.WeakMeanLossTransfer
import QubitOracle.AdaptiveDesign.GaussianQuadraticMoments
import QubitOracle.AdaptiveDesign.PureLossDistributions

/-! Expected physical losses for the actual corrected, identifying POVM
procedure. The required fourth moment is proved for this procedure, not
assumed in its expected-loss endpoint. -/
namespace QubitOracle.AdaptiveDesign.PurePOVMMeanLoss
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open TangentGLS Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open PureMultilevelDeterministicGeometry PureMultilevelLossConstants
open scoped Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def buresFactor {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) : ℝ :=
  (1+Real.sqrt ⟪(pureParameter d truth).val,A⟫_ℝ)⁻¹

theorem buresFactor_continuous {d : ℕ} (truth : PureVector d) : Continuous (buresFactor truth) := by
  apply Continuous.inv₀ (by fun_prop)
  intro A
  positivity

theorem buresFactor_bounds {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    0 ≤ buresFactor truth A ∧ buresFactor truth A ≤ 1 := by
  constructor
  · unfold buresFactor; positivity
  · exact (inv_le_one₀ (by positivity)).mpr (by linarith [Real.sqrt_nonneg ⟪(pureParameter d truth).val,A⟫_ℝ])

theorem buresFactor_self {d : ℕ} (truth : PureVector d) :
    buresFactor truth (pureParameter d truth).val = (1/2:ℝ) := by
  norm_num [buresFactor, real_inner_self_eq_norm_sq, pureParameter_norm]

theorem bures_identity {d : ℕ} (truth h : PureVector d) :
    pureMultilevelBuresSq truth.val h.val =
      ‖(pureParameter d h).val-(pureParameter d truth).val‖^2 *
        buresFactor truth (pureParameter d h).val := by
  rw [pureProjectorSquaredBures_eq_two_infidelity_div_one_add_rootFidelity,
    norm_sub_sq_real, pureParameter_norm, pureParameter_norm, real_inner_comm,
    PureLossDistributions.overlap_eq_fidelity]
  simp only [buresFactor, PureLossDistributions.overlap_eq_fidelity,
    pureMultilevelInfidelity, pureMultilevelRootFidelity, one_pow, div_eq_mul_inv]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem both_mean_losses {d : ℕ} (truth : PureVector d) (h : ℕ → Ω → PureVector d)
    (hm : ∀ n, StronglyMeasurable (fun ω => (pureParameter d (h n ω)).val))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => (pureParameter d (h n ω)).val) atTop (𝓝 (pureParameter d truth).val))
    (h4 : UniformMoment μ (fun n ω => Real.sqrt ((n+1:ℕ):ℝ) •
      ((pureParameter d (h (n+1) ω)).val-(pureParameter d truth).val)) 4)
    (hw : TendstoInDistribution
      (fun (n : ℕ) ω => (n:ℝ)*‖(pureParameter d (h n ω)).val-(pureParameter d truth).val‖^2)
      atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2) (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ (TangentIndex d)))) :
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ ω,
      ‖(pureParameter d (h n ω)).val-(pureParameter d truth).val‖^2 ∂μ)
      atTop (𝓝 (2*(d:ℝ))) ∧
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ ω, pureMultilevelBuresSq truth.val (h n ω).val ∂μ)
      atTop (𝓝 (d:ℝ)) := by
  let X := fun (n : ℕ) ω => (n:ℝ)*‖(pureParameter d (h n ω)).val-(pureParameter d truth).val‖^2
  let Z := fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2
  have hX : UniformMoment μ (fun n => X (n+1)) 2 := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)] using
      h4.norm_sq_of_four
  obtain ⟨M,hM,hXm⟩ := hX
  have hXs : TendstoInDistribution (fun n => X (n+1)) atTop Z (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) :=
    ⟨fun n => hw.forall_aemeasurable (n+1), hw.aemeasurable_limit,
      hw.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  have hZ : MemLp Z 2 (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) :=
    GaussianQuadraticMoments.norm_sq_memLp _
  have hmeanZ : ∫ z, Z z ∂stdGaussian (EuclideanSpace ℝ (TangentIndex d)) = 2*(d:ℝ) := by
    rw [GaussianQuadraticMoments.integral_norm_sq]
    simp [TangentIndex, Fintype.card_sum, Fintype.card_fin]
    ring
  have hf := WeakMeanLossTransfer.mean_tendsto_of_weak_and_secondMoment
    (fun n => X (n+1)) Z hXs (fun n => (hXm n).1) hZ
    (fun n => Eventually.of_forall (fun _ => by positivity))
    (Eventually.of_forall (fun _ => by positivity)) M hM
    (fun n => by simpa only [Real.norm_eq_abs, sq_abs] using (hXm n).2)
  rw [hmeanZ] at hf
  have hfactor : TendstoInMeasure μ
      (fun n ω => buresFactor truth (pureParameter d (h n ω)).val) atTop (fun _ => (1/2:ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n => ((buresFactor_continuous truth).comp_stronglyMeasurable (hm n)).aestronglyMeasurable)
    filter_upwards [hc] with ω hω
    simpa only [Function.comp_def, buresFactor_self] using (buresFactor_continuous truth).tendsto _ |>.comp hω
  let Y := fun (n : ℕ) ω => (n:ℝ)*pureMultilevelBuresSq truth.val (h n ω).val
  have he (n : ℕ) (ω : Ω) : Y n ω = X n ω*buresFactor truth (pureParameter d (h n ω)).val := by
    dsimp only [Y,X]
    rw [bures_identity]
    ring
  have hYw : TendstoInDistribution Y atTop (fun z => Z z*(1/2:ℝ)) (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) := by
    have ht := hw.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun x : ℝ × ℝ => x.1*x.2) (by fun_prop) hfactor
      (fun n => ((buresFactor_continuous truth).comp_stronglyMeasurable (hm n)).measurable.aemeasurable)
    convert ht using 1
    funext n ω
    exact he n ω
  have hYs : TendstoInDistribution (fun n => Y (n+1)) atTop (fun z => Z z*(1/2:ℝ)) (fun _ => μ)
      (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) :=
    ⟨fun n => hYw.forall_aemeasurable (n+1), hYw.aemeasurable_limit,
      hYw.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  have hYm : UniformMoment μ (fun n => Y (n+1)) 2 := by
    apply (show UniformMoment μ (fun n => X (n+1)) 2 from ⟨M,hM,hXm⟩).of_dominated _
      (fun n => (hYs.forall_aemeasurable n).aestronglyMeasurable) 1 (by norm_num)
    intro n ω
    simp only [he, norm_mul, Real.norm_eq_abs, abs_of_nonneg (buresFactor_bounds truth _).1, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (buresFactor_bounds truth _).2
  obtain ⟨K,hK,hYm⟩ := hYm
  have hb := WeakMeanLossTransfer.mean_tendsto_of_weak_and_secondMoment
    (fun n => Y (n+1)) (fun z => Z z*(1/2:ℝ)) hYs (fun n => (hYm n).1) (hZ.mul_const _)
    (fun n => Eventually.of_forall (fun ω => by rw [he]; exact mul_nonneg (by positivity) (buresFactor_bounds truth _).1))
    (Eventually.of_forall (fun _ => by positivity)) K hK
    (fun n => by simpa only [Real.norm_eq_abs, sq_abs] using (hYm n).2)
  have hmeanB : ∫ z, Z z*(1/2:ℝ) ∂stdGaussian (EuclideanSpace ℝ (TangentIndex d)) = (d:ℝ) := by
    rw [integral_mul_const, hmeanZ]
    ring
  rw [hmeanB] at hb
  constructor
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [X, integral_const_mul] using hf
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Y, integral_const_mul] using hb

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

/-- Corollary 5.6 for the identifying POVM route: both constants are
derived for the actual corrected estimator, with no extra moment input. -/
theorem povm
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    let μ := adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ path,
      ‖actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path‖^2 ∂μ)
      atTop (𝓝 (2*(d:ℝ))) ∧
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ path,
      pureMultilevelBuresSq truth.val (actualEstimate P hI hp regularization ridge hr hη batchSize path n).val ∂μ)
      atTop (𝓝 (d:ℝ)) := by
  apply both_mean_losses truth
    (fun n path => actualEstimate P hI hp regularization ridge hr hη batchSize path n)
  · intro n
    exact FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη)).val)
  · exact corrected_stronglyConsistent P hI hp truth regularization ridge hr hη batchSize
  · exact POVMEstimatorMoments.corrected_uniformMoment P hI hp truth regularization ridge hr hη batchSize 4
  · exact (PureLossDistributions.povm P hI hp hF truth regularization ridge hr hη batchSize hpositive).2

/-- The phase-pair construction discharges the Fisher-symmetry premise
for every regular identifying rank-one seed. -/
theorem phasePair
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    let Q := PhasePair.paired P
    let hQI := PhasePair.paired_identifying P hI
    let hQp := PhasePair.paired_regular P hp
    let μ := adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol Q hQI regularization hr batchSize) truth
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ path,
      ‖actualProjectorError Q hQI hQp truth regularization ridge hr hη batchSize n path‖^2 ∂μ)
      atTop (𝓝 (2*(d:ℝ))) ∧
    Tendsto (fun (n : ℕ) => (n:ℝ) * ∫ path,
      pureMultilevelBuresSq truth.val (actualEstimate Q hQI hQp regularization ridge hr hη batchSize path n).val ∂μ)
      atTop (𝓝 (d:ℝ)) :=
  povm (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive

end
end QubitOracle.AdaptiveDesign.PurePOVMMeanLoss
