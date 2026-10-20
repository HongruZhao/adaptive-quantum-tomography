import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.PhaseInvariantCorrection

/-! Reordering complete setting-outcome records preserves both least-squares
fits. This does not reorder outcomes while recomputing adaptive settings. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem gram_reindex {E R S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype R] [Fintype S] (e : S ≃ R) (f : R → E) (w : R → ℝ) :
    gram (f ∘ e) (w ∘ e) = gram f w := by
  ext x
  exact e.sum_comp (fun r => (w r * inner ℝ (f r) x) • f r)

theorem score_reindex {E R S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype R] [Fintype S] (e : S ≃ R) (f : R → E) (w r : R → ℝ) :
    score (f ∘ e) (w ∘ e) (r ∘ e) = score f w r :=
  e.sum_comp (fun i => (w i * r i) • f i)

theorem correction_reindex {E R S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype R] [Fintype S]
    (e : S ≃ R) (f : R → E) (w r : R → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ridge : ℝ) (hr : 0 < ridge) :
    correction (f ∘ e) (w ∘ e) (r ∘ e) (fun i => hw (e i)) ridge hr =
      correction f w r hw ridge hr := by
  apply correction_unique
  have h := correction_normalEquation (f ∘ e) (w ∘ e) (r ∘ e) (fun i => hw (e i)) ridge hr
  simpa only [normalMap,gram_reindex,score_reindex] using h

variable {d n : ℕ} {O : Type} [Fintype O]

theorem recordCorrection_permutation (h : PureVector d) (data : Fin n → Record d O)
    (e : Equiv.Perm (Fin n)) (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    recordCorrection h (data ∘ e) floor ridge hf hr =
      recordCorrection h data floor ridge hf hr := by
  exact correction_reindex (e.prodCongr (Equiv.refl O))
    (tangentFeature h data) (fun r => (denominator floor (fittedProbability h data r))⁻¹)
    (fittedResidual h data) (fun r => (inv_pos.mpr (denominator_pos hf _)).le) ridge hr

def recordRawFit (data : Fin n → Record d O) (ridge : ℝ) (hr : 0 < ridge) :
    HermitianSpace (d+1) :=
  correction (recordFeature data) (fun _ => 1) (observedIndicator data)
    (fun _ => zero_le_one) ridge hr

theorem recordRawFit_permutation (data : Fin n → Record d O)
    (e : Equiv.Perm (Fin n)) (ridge : ℝ) (hr : 0 < ridge) :
    recordRawFit (data ∘ e) ridge hr = recordRawFit data ridge hr :=
  correction_reindex (e.prodCongr (Equiv.refl O)) (recordFeature data)
    (fun _ => 1) (observedIndicator data) (fun _ => zero_le_one) ridge hr

theorem estimateFromRaw_permutation (raw : HermitianSpace (d+1))
    (data : Fin n → Record d O) (e : Equiv.Perm (Fin n))
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    estimateFromRaw raw (data ∘ e) floor ridge hf hr =
      estimateFromRaw raw data floor ridge hf hr := by
  simp only [estimateFromRaw,recordCorrection_permutation]

theorem fullRecordEstimate_permutation (data : Fin n → Record d O)
    (e : Equiv.Perm (Fin n)) (regularization floor ridge : ℝ)
    (hreg : 0 < regularization) (hf : 0 < floor) (hr : 0 < ridge) :
    estimateFromRaw (recordRawFit (data ∘ e) regularization hreg) (data ∘ e) floor ridge hf hr =
      estimateFromRaw (recordRawFit data regularization hreg) data floor ridge hf hr := by
  rw [recordRawFit_permutation,estimateFromRaw_permutation]

theorem recordRawFit_unique_minimizer (data : Fin n → Record d O)
    (ridge : ℝ) (hr : 0 < ridge) :
    (∀ x, objective (recordFeature data) (fun _ => 1) (observedIndicator data) ridge
      (recordRawFit data ridge hr) ≤
      objective (recordFeature data) (fun _ => 1) (observedIndicator data) ridge x) ∧
    (∀ x, objective (recordFeature data) (fun _ => 1) (observedIndicator data) ridge x =
      objective (recordFeature data) (fun _ => 1) (observedIndicator data) ridge
        (recordRawFit data ridge hr) → x = recordRawFit data ridge hr) := by
  constructor
  · exact correction_minimizes _ _ _ (fun _ => zero_le_one) ridge hr
  · intro x hx
    let c := recordRawFit data ridge hr
    have h := objective_expansion (recordFeature data) (fun _ => 1)
      (observedIndicator data) ridge c (x-c)
    have hn : normalMap (recordFeature data) (fun _ => 1) ridge c =
      score (recordFeature data) (fun _ => 1) (observedIndicator data) :=
      correction_normalEquation _ _ _ (fun _ => zero_le_one) ridge hr
    rw [add_sub_cancel,hn,sub_self,inner_zero_right,zero_add,hx,sub_self] at h
    have hc := normalMap_coercive (recordFeature data) (fun _ => 1)
      (fun _ => zero_le_one) ridge (x-c)
    have hz : ‖x-c‖^2 = 0 := by nlinarith [sq_nonneg ‖x-c‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actual_raw_eq_recordRawFit (P : FinitePOVM (Fin (d+1)) O)
    (hI : GeneralPOVM.Identifying P) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    GeneralPOVM.rawEstimator P hI ridge hr batchSize path n =
      recordRawFit (actualRecords P hI ridge hr batchSize path n) ridge hr := by
  apply correction_unique
  let st := GeneralPOVM.actualState P hI ridge hr batchSize path n
  have hg : normalMap (recordFeature (actualRecords P hI ridge hr batchSize path n))
      (fun _ => 1) ridge = st.gram := by
    ext x
    simp only [normalMap_apply,gram_apply,Fintype.sum_prod_type,one_mul,actual_recordFeature_eq]
    change _ = (SequentialRidgeController.pathState _ _ _ _ _ _ _ _ _ path n).gram x
    rw [SequentialRidgeController.pathState_gram,CoerciveLeastSquares.ridgeGram_apply,
      ← Fin.sum_univ_eq_sum_range]
    rfl
  have hs : score (recordFeature (actualRecords P hI ridge hr batchSize path n))
      (fun _ => 1) (observedIndicator (actualRecords P hI ridge hr batchSize path n)) =
      st.responseSum := by
    classical
    simp only [score,Fintype.sum_prod_type,one_mul,observedIndicator,actualRecords,
      actual_recordFeature_eq,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    change _ = (SequentialRidgeController.pathState _ _ _ _ _ _ _ _ _ path n).responseSum
    rw [SequentialRidgeController.pathState_responseSum,← Fin.sum_univ_eq_sum_range]
    rfl
  rw [hg,hs]
  exact SequentialRidgeController.State.estimate_normalEquation hr st

end
end QubitOracle.AdaptiveDesign.TangentGLS
