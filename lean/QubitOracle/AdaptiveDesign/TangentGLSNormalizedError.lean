import QubitOracle.AdaptiveDesign.TangentGLSAsymptoticLinearization

/-! The normalized physical output has the same first-order error as the
intrinsic tangent correction. Its leading term is the true tangent score. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualProjectorError (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  (pureParameter d (actualEstimate P hI hp regularization ridge hr hη batchSize path n)).val -
    (pureParameter d truth).val

theorem actual_retraction_error_bound
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    ‖actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path -
      (actualPreliminaryError P hI regularization hr batchSize truth n path +
        actualDelta P hI hp regularization ridge hr hη batchSize n path)‖ ≤
      3*‖actualDelta P hI hp regularization ridge hr hη batchSize n path‖^2 := by
  let h := actualPreliminary P hI regularization hr batchSize path n
  let A := recordCorrection h (actualRecords P hI regularization hr batchSize path n)
    (referenceFloor P) ridge (referenceFloor_pos P hp) hη
  rw [← toMatrix_norm (actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path -
    (actualPreliminaryError P hI regularization hr batchSize truth n path +
      actualDelta P hI hp regularization ridge hr hη batchSize n path))]
  change ‖(updatedState h A - rankOneDensity truth.val) -
    ((rankOneDensity h.val-rankOneDensity truth.val)+toMatrix A.val)‖ ≤ 3*‖A‖^2
  have he : (updatedState h A - rankOneDensity truth.val) -
      ((rankOneDensity h.val-rankOneDensity truth.val)+toMatrix A.val) =
      updatedState h A - (rankOneDensity h.val+toMatrix A.val) := by abel
  rw [he]
  exact updatedState_remainder_bound_global h A

theorem actualDelta_square_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ‖actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path‖^2) atTop (fun _ => 0) := by
  have hh := square_norm_zero (actualDelta_quarterRate P hI hp hF truth regularization ridge hr hη batchSize hpositive)
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, BoundedResponseQuarterRate.quarterScale_sq] using hh

theorem actualProjectorError_linearization
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) • actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path -
        (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • tangentProjector truth
          (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path)) atTop (fun _ => 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth
  have hgeom : TendstoInMeasure μ (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) •
      (actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path -
        (actualPreliminaryError P hI regularization hr batchSize truth (n+1) path +
          actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path))) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated
      (actualDelta_square_rootRate P hI hp hF truth regularization ridge hr hη batchSize hpositive) 3 (by norm_num)
    intro n path
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left
      (actual_retraction_error_bound P hI hp truth regularization ridge hr hη batchSize (n+1) path)
      (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
    exact hb.trans_eq (by (try dsimp only [actualPreliminaryError]); ring)
  have hnormal : TendstoInMeasure μ (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) •
      (actualPreliminaryError P hI regularization hr batchSize truth (n+1) path -
        actualTangentError P hI truth regularization hr batchSize (n+1) path)) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated (actualPreliminaryError_square_rootRate P hI regularization hr batchSize truth) 3 (by norm_num)
    intro n path
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left (preliminaryError_normal_bound
      (actualPreliminary P hI regularization hr batchSize path (n+1)) truth) (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
    exact hb.trans_eq (by (try dsimp only [actualPreliminaryError]); ring)
  have hQ : TendstoInMeasure μ (fun n path =>
      tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1)) - tangentProjector truth)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
        (fun raw _ => tangentProjector (nearestVector d (toMatrix raw)) - tangentProjector truth)).aestronglyMeasurable
    · filter_upwards [actual_tangentProjector_tendsto P hI truth regularization hr batchSize] with path hpath
      simpa using (hpath.comp (tendsto_add_atTop_nat 1)).sub_const (tangentProjector truth)
  have hscore := clm_apply_zero hQ (actual_ambientScore_rootTight P hI truth (referenceFloor P)
    (referenceFloor_pos P hp) regularization hr batchSize)
  change TendstoInMeasure μ (fun n path =>
    (tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1)) - tangentProjector truth)
      ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path))
    atTop (fun _ => 0) at hscore
  have hh := ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add hgeom hnormal)
    (actualLinearError_rootRate P hI hp hF truth regularization ridge hr hη batchSize hpositive)) hscore
  have he (n : ℕ) (path : AdaptiveInfinitePath O) :
      Real.sqrt ((n+1 : ℕ) : ℝ) •
      (actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path -
        (actualPreliminaryError P hI regularization hr batchSize truth (n+1) path +
          actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path)) +
      Real.sqrt ((n+1 : ℕ) : ℝ) • (actualPreliminaryError P hI regularization hr batchSize truth (n+1) path -
        actualTangentError P hI truth regularization hr batchSize (n+1) path) +
      actualLinearError P hI hp truth regularization ridge hr hη batchSize (n+1) path +
      (tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1)) - tangentProjector truth)
        ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path) =
      Real.sqrt ((n+1 : ℕ) : ℝ) • actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path -
        (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • tangentProjector truth
          (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path) := by
    simp only [actualLinearError, ContinuousLinearMap.sub_apply, map_smul, smul_sub, smul_add]
    abel
  exact hh.congr (fun n => Filter.Eventually.of_forall (fun path => he n path)) Filter.EventuallyEq.rfl

end
end QubitOracle.AdaptiveDesign.TangentGLS
