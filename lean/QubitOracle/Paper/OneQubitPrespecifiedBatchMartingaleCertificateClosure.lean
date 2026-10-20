import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeScoreCLT
import QubitOracle.Paper.OneQubitMixedCommonSpaceCondExpPullbackClosed
import QubitOracle.Paper.BoundedMartingaleAzumaStrongLaw

/-!
# Martingale certificate for the exact prespecified-batch qubit protocol

The final shots are flattened by their genuine cumulative batch offsets.  The
resulting filtration is independent of the terminal horizon: it reveals every
earlier complete batch, the current batch pilot, and the current final prefix.
The finite conditional-expectation calculations are imported from the closed
exact-cycle common-space development and specialized to the actual Born rows.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
open PureMultilevelSequentialBatchAdaptive

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

namespace PrespecifiedBatchMartingaleClosure

open MixedExactCycleScalarTriangularArrayData

/-- Number of final observations in batch `k`. -/
def finalShotBlockSize (k : Nat) : Nat :=
  3 * exactConcreteBatchFinalBlocks k

theorem finalShotBlockSize_pos (k : Nat) : 0 < finalShotBlockSize k := by
  unfold finalShotBlockSize
  exact Nat.mul_pos (by norm_num) (exactConcreteBatchFinalBlocks_pos k)

/-- Number of final observations in batches strictly before `K`. -/
def finalShotOffset (K : Nat) : Nat :=
  ∑ k ∈ Finset.range K, finalShotBlockSize k

@[simp]
theorem finalShotOffset_zero : finalShotOffset 0 = 0 := by
  simp [finalShotOffset]

theorem finalShotOffset_succ (K : Nat) :
    finalShotOffset (K + 1) =
      finalShotOffset K + finalShotBlockSize K := by
  rw [finalShotOffset, finalShotOffset, Finset.sum_range_succ]

theorem finalShotOffset_lt_succ (K : Nat) :
    finalShotOffset K < finalShotOffset (K + 1) := by
  rw [finalShotOffset_succ]
  exact Nat.lt_add_of_pos_right (finalShotBlockSize_pos K)

theorem finalShotOffset_strictMono : StrictMono finalShotOffset :=
  strictMono_nat_of_lt_succ finalShotOffset_lt_succ

theorem finalShotOffset_lower (K : Nat) : K <= finalShotOffset K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [finalShotOffset_succ]
      have hsize := finalShotBlockSize_pos K
      omega

/-- Exact-cycle data of the actual `k`th batch. -/
def exactBatchArrayData
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (k : Nat) : MixedExactCycleScalarTriangularArrayData where
  pilotLength := fun _ => exactConcreteBatchPilotBlocks k
  theta := theta
  direction := h
  selected := fun _ => exactConcreteBatchSelectedFrame k b
  targetVariance := 0
  targetVariance_nonnegative := le_rfl
  interior := hInterior

/-- The varying row size is exactly the prescribed number of final cycles. -/
def exactBatchRowSize (k : Nat) : Nat :=
  exactConcreteBatchFinalBlocks k

theorem exactBatchRowSize_pos (k : Nat) : 0 < exactBatchRowSize k :=
  exactConcreteBatchFinalBlocks_pos k

/-- The common-space row law is exactly the finite Born law used by the
implemented protocol. -/
theorem exactBatchCommonRowMeasure_eq
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (k : Nat) :
    commonRowMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize k =
      exactConcretePredeterminedBatchRowMeasure theta b k := by
  classical
  unfold commonRowMeasure exactConcretePredeterminedBatchRowMeasure
    MixedExactCycleScalarTriangularArrayData.mathlibRowMeasure
    mixedTwoStageFiniteBornMeasure
  congr 1
  funext row
  congr 1
  change
    (↑((exactBatchArrayData theta h b hInterior k).rowNNRealWeight
      (exactBatchRowSize k) row) : ENNReal) =
      ENNReal.ofReal
        ((exactBatchArrayData theta h b hInterior k).jointRowMass
          (exactBatchRowSize k) row)
  have hmass :=
    (exactBatchArrayData theta h b hInterior k).jointRowMass_nonnegative
      (exactBatchRowSize k) row
  rw [ENNReal.ofReal_eq_coe_nnreal hmass]
  congr 1

/-- Hence the exact infinite product Born law is the already-closed common
row product law, definitionally on the same path type. -/
theorem exactBatchCommonMeasure_eq
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    commonMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize =
      exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior) := by
  unfold commonMeasure exactConcretePredeterminedBatchPathMeasure
  congr 1
  funext k
  exact exactBatchCommonRowMeasure_eq theta h b hInterior k

/-! ## Horizon-independent cumulative offset decoder -/

theorem exists_batch_for_global_stage (n : Nat) :
    ∃ K : Nat, n < finalShotOffset (K + 1) := by
  refine ⟨n, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (finalShotOffset_lower (n + 1))

/-- Batch containing global final-shot number `n`. -/
def globalBatch (n : Nat) : Nat :=
  Nat.find (exists_batch_for_global_stage n)

theorem globalBatch_upper (n : Nat) :
    n < finalShotOffset (globalBatch n + 1) :=
  Nat.find_spec (exists_batch_for_global_stage n)

theorem globalBatch_lower (n : Nat) :
    finalShotOffset (globalBatch n) <= n := by
  by_cases hzero : globalBatch n = 0
  · simp [hzero]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hminimal := Nat.find_min (exists_batch_for_global_stage n)
      (show j < globalBatch n by omega)
    rw [hj]
    simpa only [Nat.succ_eq_add_one, not_lt] using hminimal

/-- Shot coordinate within its decoded batch. -/
def globalWithin (n : Nat) : Nat :=
  n - finalShotOffset (globalBatch n)

theorem globalWithin_lt_size (n : Nat) :
    globalWithin n < finalShotBlockSize (globalBatch n) := by
  have hu := globalBatch_upper n
  have hl := globalBatch_lower n
  rw [finalShotOffset_succ] at hu
  unfold globalWithin
  omega

/-- Infinite batch-major final-shot index. -/
abbrev InfiniteFinalShotIndex : Type :=
  Sigma fun k : Nat => Fin (finalShotBlockSize k)

/-- Decode a global natural shot number into its batch and within-batch shot. -/
def globalShot (n : Nat) : InfiniteFinalShotIndex :=
  ⟨globalBatch n, ⟨globalWithin n, globalWithin_lt_size n⟩⟩

/-- Encode a batch shot by cumulative offset. -/
def globalShotRank (shot : InfiniteFinalShotIndex) : Nat :=
  finalShotOffset shot.1 + shot.2.val

@[simp]
theorem globalShotRank_globalShot (n : Nat) :
    globalShotRank (globalShot n) = n := by
  unfold globalShotRank globalShot globalWithin
  exact Nat.add_sub_of_le (globalBatch_lower n)

theorem globalBatch_globalShotRank (shot : InfiniteFinalShotIndex) :
    globalBatch (globalShotRank shot) = shot.1 := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    unfold globalShotRank
    rw [finalShotOffset_succ]
    omega
  · by_contra hnot
    have hlt : globalBatch (globalShotRank shot) < shot.1 :=
      Nat.lt_of_not_ge hnot
    have hu := globalBatch_upper (globalShotRank shot)
    have hmono := finalShotOffset_strictMono.monotone
      (show globalBatch (globalShotRank shot) + 1 <= shot.1 by omega)
    unfold globalShotRank at hu hmono
    omega

/-! ## Exact finite-horizon embedding into the global shot order -/

/-- Forget the finite-horizon bound while retaining the batch and final-shot
coordinates. -/
def embedFiniteShot {K : Nat}
    (shot : PrespecifiedBatchCumulativeFinalShotIndex K) :
    InfiniteFinalShotIndex :=
  let raw := ofLex shot
  ⟨raw.1.val, raw.2⟩

/-- The explicit `Fin` enumeration is exactly cumulative-offset rank. -/
theorem enumeratedShot_globalRank
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    globalShotRank (embedFiniteShot
      (prespecifiedBatchCumulativeFinalShotOrderIso K t)) = t.val := by
  let hcard : prespecifiedBatchCumulativeFinalRowLength K =
      ∑ k : Fin K, 3 * exactConcreteBatchFinalBlocks k := by
    simp [prespecifiedBatchCumulativeFinalRowLength]
  let u : Fin (∑ k : Fin K, 3 * exactConcreteBatchFinalBlocks k) :=
    finCongr hcard t
  let raw : Sigma fun k : Fin K =>
      Fin (3 * exactConcreteBatchFinalBlocks k) :=
    finSigmaFinEquiv.symm u
  have happ : finSigmaFinEquiv raw = u := Equiv.apply_symm_apply _ u
  have hval := congrArg Fin.val happ
  rw [finSigmaFinEquiv_apply] at hval
  change finalShotOffset raw.1.val + raw.2.val = t.val
  rw [show finalShotOffset raw.1.val =
      ∑ i : Fin raw.1.val, finalShotBlockSize i by
        exact (Fin.sum_univ_eq_sum_range finalShotBlockSize raw.1.val).symm]
  simpa [u, hcard, embedFiniteShot,
    prespecifiedBatchCumulativeFinalShotOrderIso,
    finalShotBlockSize] using hval

/-- Decoding an enumerated horizon shot recovers its finite batch. -/
theorem globalBatch_enumeratedShot
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    globalBatch t.val =
      (embedFiniteShot
        (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1 := by
  rw [← enumeratedShot_globalRank K t]
  exact globalBatch_globalShotRank _

/-- Decoding an enumerated horizon shot recovers its within-batch coordinate. -/
theorem globalWithin_enumeratedShot
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    globalWithin t.val =
      (embedFiniteShot
        (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2.val := by
  rw [← enumeratedShot_globalRank K t]
  unfold globalWithin globalShotRank
  have hbatch :
      globalBatch
        (finalShotOffset
          (embedFiniteShot
            (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1 +
          (embedFiniteShot
            (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2.val) =
        (embedFiniteShot
          (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1 := by
    simpa [globalShotRank] using globalBatch_globalShotRank
      (embedFiniteShot (prespecifiedBatchCumulativeFinalShotOrderIso K t))
  rw [hbatch]
  exact Nat.add_sub_cancel_left _ _

/-! ## Horizon-independent batch-major filtration -/

theorem globalBatch_mono : Monotone globalBatch := by
  intro n m hnm
  apply Nat.find_min'
  exact lt_of_le_of_lt hnm (globalBatch_upper m)

/-- Existing common-space row filtrations are nested across any strict row
increase, not only adjacent rows. -/
theorem augmentedRowFiltrationSigma_le_of_lt
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    {i j : Nat} (hij : i < j) (k ell : Nat) :
    augmentedRowFiltrationSigma
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize i k <=
      augmentedRowFiltrationSigma
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize j ell := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hijEq : i = j
      · subst i
        exact augmentedRowFiltrationSigma_crossRow
          (exactBatchArrayData theta h b hInterior) exactBatchRowSize j k ell
      · have hij' : i < j := by omega
        exact (ih hij').trans
          (augmentedRowFiltrationSigma_crossRow
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize j ell ell)

/-- Sigma algebra before global final shot `n`: all previous rows, the current
pilot, and the current final prefix. -/
def globalFinalFiltrationSigma
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) : MeasurableSpace ExactConcretePredeterminedBatchPath :=
  augmentedRowFiltrationSigma
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    (globalBatch n) (globalWithin n)

theorem globalFinalFiltrationSigma_mono
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    Monotone (globalFinalFiltrationSigma theta h b hInterior) := by
  intro n m hnm
  by_cases hbatch : globalBatch n = globalBatch m
  · unfold globalFinalFiltrationSigma
    rw [hbatch]
    apply augmentedRowFiltrationSigma_mono
    unfold globalWithin
    rw [hbatch]
    omega
  · have hlt : globalBatch n < globalBatch m :=
      lt_of_le_of_ne (globalBatch_mono hnm) hbatch
    exact augmentedRowFiltrationSigma_le_of_lt theta h b hInterior hlt
      (globalWithin n) (globalWithin m)

/-- The single global filtration used for every terminal horizon. -/
def globalFinalFiltration
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    Filtration Nat
      (inferInstance : MeasurableSpace ExactConcretePredeterminedBatchPath) where
  seq := globalFinalFiltrationSigma theta h b hInterior
  mono' := globalFinalFiltrationSigma_mono theta h b hInterior
  le' := fun n => augmentedRowFiltrationSigma_le
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    (globalBatch n) (globalWithin n)

theorem globalFinalFiltrationSigma_enumerated
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    globalFinalFiltrationSigma theta h b hInterior t.val =
      augmentedRowFiltrationSigma
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        (embedFiniteShot
          (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1
        (embedFiniteShot
          (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2.val := by
  unfold globalFinalFiltrationSigma
  rw [globalBatch_enumeratedShot, globalWithin_enumeratedShot]

/-! ## Exact conditional score transport -/

theorem cumulativeIncrement_eq_scaled_liftedScore
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t =
      fun omega =>
        prespecifiedBatchCumulativeShotScale K
            (prespecifiedBatchCumulativeFinalShotOrderIso K t).1 *
          liftedScore (exactBatchArrayData theta h b hInterior)
            exactBatchRowSize
            (embedFiniteShot
              (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1
            (embedFiniteShot
              (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2 omega := by
  rfl

/-- Exact scaled conditional score centering for one enumerated final shot. -/
theorem cumulativeIncrement_condExp_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t |
        globalFinalFiltrationSigma theta h b hInterior t.val] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      (fun _ => (0 : Real)) := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  have hzero := liftedScore_condExp_zero_closed
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    embedded.1 embedded.2
  have hsmul := MeasureTheory.condExp_smul
    (μ := commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize) scale
    (liftedScore (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize embedded.1 embedded.2)
    (augmentedRowFiltrationSigma
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize
      embedded.1 embedded.2.val)
  have hscaled := hsmul.trans (hzero.const_smul scale)
  have hleft :
      scale • liftedScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize embedded.1 embedded.2 =
        fun omega => scale *
          liftedScore (exactBatchArrayData theta h b hInterior)
            exactBatchRowSize embedded.1 embedded.2 omega := by
    funext omega
    simp [smul_eq_mul]
  rw [hleft] at hscaled
  have hright :
      scale • (fun _ : CommonOmega
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize => (0 : Real))
        =ᵐ[commonMeasure (exactBatchArrayData theta h b hInterior)
          exactBatchRowSize]
      (fun _ => (0 : Real)) := by
    filter_upwards
    intro omega
    change scale • (0 : Real) = 0
    simp
  have hscaledZero := hscaled.trans hright
  rw [globalFinalFiltrationSigma_enumerated]
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  rw [cumulativeIncrement_eq_scaled_liftedScore theta h b hInterior K t]
  change
    (commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize)[
        (fun omega : CommonOmega
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize =>
          scale * liftedScore (exactBatchArrayData theta h b hInterior)
            exactBatchRowSize embedded.1 embedded.2 omega) |
        augmentedRowFiltrationSigma
          (exactBatchArrayData theta h b hInterior) exactBatchRowSize
          embedded.1 embedded.2.val] =ᵐ[
            commonMeasure (exactBatchArrayData theta h b hInterior)
              exactBatchRowSize]
      (fun _ => (0 : Real))
  exact hscaledZero

/-! ## Exact conditional squared-score transport -/

theorem exactBatch_liftedSquaredScore_eq_sq
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (k : Nat) (t : Fin (3 * exactConcreteBatchFinalBlocks k))
    (omega : CommonOmega (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize) :
    liftedSquaredScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize k t omega =
      liftedScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize k t omega ^ 2 := by
  rfl

theorem cumulativeIncrement_square_eq_scaled_liftedSquaredScore
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (fun omega =>
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2) =
      fun omega =>
        prespecifiedBatchCumulativeShotScale K
            (prespecifiedBatchCumulativeFinalShotOrderIso K t).1 ^ 2 *
          liftedSquaredScore (exactBatchArrayData theta h b hInterior)
            exactBatchRowSize
            (embedFiniteShot
              (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1
            (embedFiniteShot
              (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2 omega := by
  funext omega
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  rw [cumulativeIncrement_eq_scaled_liftedScore theta h b hInterior K t]
  change
    (scale * liftedScore (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize embedded.1 embedded.2 omega) ^ 2 =
      scale ^ 2 *
        liftedScore (exactBatchArrayData theta h b hInterior)
          exactBatchRowSize embedded.1 embedded.2 omega ^ 2
  ring

/-- Deterministic normalization: cumulative scale squared times the row-
normalized one-shot Fisher is exactly the displayed cumulative predictable
variance. -/
theorem scaled_liftedOneShotFisher_eq_conditionalVariance
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (fun omega =>
      prespecifiedBatchCumulativeShotScale K
          (prespecifiedBatchCumulativeFinalShotOrderIso K t).1 ^ 2 *
        liftedOneShotFisher (exactBatchArrayData theta h b hInterior)
          exactBatchRowSize
          (embedFiniteShot
            (prespecifiedBatchCumulativeFinalShotOrderIso K t)).1
          (embedFiniteShot
            (prespecifiedBatchCumulativeFinalShotOrderIso K t)).2 omega) =
      prespecifiedBatchCumulativeConditionalVariance theta h b K t := by
  funext omega
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let raw := ofLex shot
  let r := exactConcreteBatchFinalBlocks raw.1
  let axis := mixedTwoStageFinalAxis
    (exactConcreteBatchSelectedFrame raw.1 b) (omega raw.1).1 raw.2
  let info := QubitOracle.blochDot h axis ^ 2 /
    (1 - QubitOracle.blochDot theta axis ^ 2)
  have hr : 0 < r := exactConcreteBatchFinalBlocks_pos raw.1
  have ha : (0 : Real) < (3 * r : Nat) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) hr
  have hsqrt : Real.sqrt (3 * r : Nat) ^ 2 = (3 * r : Nat) := by
    exact Real.sq_sqrt (le_of_lt ha)
  change (Real.sqrt (3 * r : Nat) / prespecifiedBatchSampleScale K) ^ 2 *
      (info / ((3 * r : Nat) : Real)) =
    (prespecifiedBatchSampleScale K)⁻¹ ^ 2 * info
  rw [div_pow, hsqrt]
  field_simp [ne_of_gt ha]

/-- Exact conditional second moment equals the concrete cumulative Fisher
contribution for every final shot. -/
theorem cumulativeIncrement_square_condExp_eq_variance
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      (fun omega =>
        prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2) |
        globalFinalFiltrationSigma theta h b hInterior t.val] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      prespecifiedBatchCumulativeConditionalVariance theta h b K t := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scaleSq := prespecifiedBatchCumulativeShotScale K shot.1 ^ 2
  have hbase := liftedSquaredScore_condExp_eq_oneShotFisher_closed
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    embedded.1 (exactBatchRowSize_pos embedded.1) embedded.2
  have hsmul := MeasureTheory.condExp_smul
    (μ := commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize) scaleSq
    (liftedSquaredScore (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize embedded.1 embedded.2)
    (augmentedRowFiltrationSigma
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize
      embedded.1 embedded.2.val)
  have hscaled := hsmul.trans (hbase.const_smul scaleSq)
  have hleft :
      scaleSq • liftedSquaredScore
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 =
      fun omega => scaleSq * liftedSquaredScore
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 omega := by
    funext omega
    simp [smul_eq_mul]
  have hright :
      scaleSq • liftedOneShotFisher
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 =
      fun omega => scaleSq * liftedOneShotFisher
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 omega := by
    funext omega
    simp [smul_eq_mul]
  rw [hleft, hright] at hscaled
  have hnorm :
      (fun omega => scaleSq * liftedOneShotFisher
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 omega) =
      prespecifiedBatchCumulativeConditionalVariance theta h b K t := by
    simpa [shot, embedded, scaleSq] using
      scaled_liftedOneShotFisher_eq_conditionalVariance
        theta h b hInterior K t
  have hscaledVariance := hscaled.trans
    (Filter.Eventually.of_forall (fun omega => congrFun hnorm omega))
  rw [globalFinalFiltrationSigma_enumerated]
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  rw [cumulativeIncrement_square_eq_scaled_liftedSquaredScore
    theta h b hInterior K t]
  change
    (commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize)[
        (fun omega : CommonOmega
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize =>
          scaleSq * liftedSquaredScore
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize
            embedded.1 embedded.2 omega) |
        augmentedRowFiltrationSigma
          (exactBatchArrayData theta h b hInterior) exactBatchRowSize
          embedded.1 embedded.2.val] =ᵐ[
            commonMeasure (exactBatchArrayData theta h b hInterior)
              exactBatchRowSize]
      prespecifiedBatchCumulativeConditionalVariance theta h b K t
  exact hscaledVariance

/-! ## Strict Hall--Heyde Lindeberg transport -/

/-- Strict-threshold row observable matching the cumulative Hall--Heyde
statement exactly. -/
def strictLindebergObservable
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : Nat) (t : Fin (3 * r)) (epsilon : Real)
    (pilot : A.PilotSpace r) (outcome : Bool) : Real :=
  if epsilon < |A.normalizedFinalScoreIncrement r pilot t outcome| then
    A.normalizedFinalScoreIncrement r pilot t outcome ^ 2
  else 0

/-- Exact conditional Born kernel of the strict truncand. -/
def strictOneShotLindebergKernel
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : Nat) (t : Fin (3 * r)) (epsilon : Real)
    (row : A.RowSpace r) : Real :=
  ∑ outcome : Bool,
    mixedTwoStageFinalBornProbability
        A.theta (A.selected r) row.1 t outcome *
      strictLindebergObservable A r t epsilon row.1 outcome

theorem strictLindeberg_finiteConditionalExpectation_eq_kernel
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : Nat) (t : Fin (3 * r)) (epsilon : Real) :
    ExactFiniteStepConditionalExpectation A r t
      (strictLindebergObservable A r t epsilon)
      (strictOneShotLindebergKernel A r t epsilon) := by
  refine ⟨?_, ?_⟩
  · intro row1 row2 hhistory
    have hpilot : row1.1 = row2.1 :=
      congrArg (fun history : A.HistoryKey r => history.1) hhistory
    simp [strictOneShotLindebergKernel, hpilot]
  · intro row
    rfl

theorem strictLindeberg_literal_condExp_eq_kernel
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : Nat) (t : Fin (3 * r)) (epsilon : Real) :
    (A.mathlibRowMeasure r)[
      A.currentCoordinateObservable r t
        (strictLindebergObservable A r t epsilon) |
      A.rowFiltrationSigma r t.val] =ᵐ[A.mathlibRowMeasure r]
      strictOneShotLindebergKernel A r t epsilon := by
  exact (A.exactFiniteStepConditionalExpectation_ae_eq_condExp
    r t (strictLindebergObservable A r t epsilon)
      (strictOneShotLindebergKernel A r t epsilon)
      (strictLindeberg_finiteConditionalExpectation_eq_kernel
        A r t epsilon)).symm

noncomputable def liftedStrictLindebergObservable
    (A : Nat -> MixedExactCycleScalarTriangularArrayData)
    (rowSize : Nat -> Nat) (n : Nat)
    (t : Fin (3 * rowSize n)) (epsilon : Real) :
    CommonOmega A rowSize -> Real :=
  liftRowVariable A rowSize n
    ((A n).currentCoordinateObservable (rowSize n) t
      (strictLindebergObservable (A n) (rowSize n) t epsilon))

noncomputable def liftedStrictOneShotLindebergKernel
    (A : Nat -> MixedExactCycleScalarTriangularArrayData)
    (rowSize : Nat -> Nat) (n : Nat)
    (t : Fin (3 * rowSize n)) (epsilon : Real) :
    CommonOmega A rowSize -> Real :=
  liftRowVariable A rowSize n
    (strictOneShotLindebergKernel (A n) (rowSize n) t epsilon)

theorem liftedStrictLindeberg_condExp_eq_kernel
    (A : Nat -> MixedExactCycleScalarTriangularArrayData)
    (rowSize : Nat -> Nat) (n : Nat)
    (t : Fin (3 * rowSize n)) (epsilon : Real) :
    (commonMeasure A rowSize)[
      liftedStrictLindebergObservable A rowSize n t epsilon |
      augmentedRowFiltrationSigma A rowSize n t.val] =ᵐ[
        commonMeasure A rowSize]
      liftedStrictOneShotLindebergKernel A rowSize n t epsilon := by
  exact commonCondExp_lift A rowSize n t.val
    ((A n).currentCoordinateObservable (rowSize n) t
      (strictLindebergObservable (A n) (rowSize n) t epsilon))
    (strictOneShotLindebergKernel (A n) (rowSize n) t epsilon)
    (strictLindeberg_literal_condExp_eq_kernel
      (A n) (rowSize n) t epsilon)

theorem prespecifiedBatchSampleScale_pos_of_pos
    (K : Nat) (hK : 0 < K) :
    0 < prespecifiedBatchSampleScale K := by
  unfold prespecifiedBatchSampleScale
  apply Real.sqrt_pos.2
  have htotal : 0 < prespecifiedBatchTotalObservations K := by
    rw [show prespecifiedBatchTotalObservations K = (3 * K) ^ 6 by
      exact exactConcreteBatchSize_cumulative K]
    positivity
  exact_mod_cast htotal

theorem cumulativeShotScale_pos
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    0 < prespecifiedBatchCumulativeShotScale K
      (prespecifiedBatchCumulativeFinalShotOrderIso K t).1 := by
  have hK : 0 < K := by
    by_contra hnot
    have hzero : K = 0 := Nat.eq_zero_of_not_pos hnot
    subst K
    simpa [prespecifiedBatchCumulativeFinalRowLength] using t.isLt
  unfold prespecifiedBatchCumulativeShotScale
  apply div_pos
  · apply Real.sqrt_pos.2
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3)
      (exactConcreteBatchFinalBlocks_pos
        (prespecifiedBatchCumulativeFinalShotOrderIso K t).1)
  · exact prespecifiedBatchSampleScale_pos_of_pos K hK

/-- The cumulative strict truncand is exactly scale squared times the strict
row truncand at threshold `epsilon / scale`. -/
theorem cumulativeLindebergTruncand_eq_scaled_liftedStrict
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (K : Nat)
    (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (fun omega =>
      if epsilon <
          |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega|
      then prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2
      else 0) =
    fun omega =>
      let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
      let embedded := embedFiniteShot shot
      let scale := prespecifiedBatchCumulativeShotScale K shot.1
      scale ^ 2 * liftedStrictLindebergObservable
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 (epsilon / scale) omega := by
  funext omega
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  let score := liftedScore (exactBatchArrayData theta h b hInterior)
    exactBatchRowSize embedded.1 embedded.2 omega
  have hscale : 0 < scale := by
    exact cumulativeShotScale_pos K t
  have habs : |scale * score| = scale * |score| := by
    rw [abs_mul, abs_of_pos hscale]
  have hthreshold :
      epsilon < |scale * score| <-> epsilon / scale < |score| := by
    rw [habs]
    constructor
    · intro hlt
      exact (div_lt_iff₀ hscale).2 (by simpa [mul_comm] using hlt)
    · intro hlt
      have := (div_lt_iff₀ hscale).1 hlt
      simpa [mul_comm] using this
  rw [cumulativeIncrement_eq_scaled_liftedScore theta h b hInterior K t]
  change (if epsilon < |scale * score| then (scale * score) ^ 2 else 0) =
    scale ^ 2 * (if epsilon / scale < |score| then score ^ 2 else 0)
  by_cases htail : epsilon < |scale * score|
  · rw [if_pos htail, if_pos (hthreshold.mp htail)]
    ring
  · rw [if_neg htail, if_neg (fun h => htail (hthreshold.mpr h))]
    ring

/-- Concrete predictable strict Lindeberg contribution. -/
noncomputable def prespecifiedBatchCumulativeConditionalLindeberg
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (K : Nat)
    (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    ExactConcretePredeterminedBatchPath -> Real :=
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  fun omega => scale ^ 2 * liftedStrictOneShotLindebergKernel
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    embedded.1 embedded.2 (epsilon / scale) omega

theorem cumulativeLindeberg_condExp_eq_kernel
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (K : Nat)
    (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      (fun omega =>
        if epsilon <
            |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega|
        then prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2
        else 0) | globalFinalFiltrationSigma theta h b hInterior t.val] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      prespecifiedBatchCumulativeConditionalLindeberg
        theta h b hInterior epsilon K t := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  let threshold := epsilon / scale
  have hbase := liftedStrictLindeberg_condExp_eq_kernel
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    embedded.1 embedded.2 threshold
  have hsmul := MeasureTheory.condExp_smul
    (μ := commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize) (scale ^ 2)
    (liftedStrictLindebergObservable
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize
      embedded.1 embedded.2 threshold)
    (augmentedRowFiltrationSigma
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize
      embedded.1 embedded.2.val)
  have hscaled := hsmul.trans (hbase.const_smul (scale ^ 2))
  have hleft :
      scale ^ 2 • liftedStrictLindebergObservable
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 threshold =
      fun omega => scale ^ 2 * liftedStrictLindebergObservable
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 threshold omega := by
    funext omega
    simp [smul_eq_mul]
  have hright :
      scale ^ 2 • liftedStrictOneShotLindebergKernel
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 threshold =
      fun omega => scale ^ 2 * liftedStrictOneShotLindebergKernel
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 threshold omega := by
    funext omega
    simp [smul_eq_mul]
  rw [hleft, hright] at hscaled
  rw [globalFinalFiltrationSigma_enumerated]
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  rw [cumulativeLindebergTruncand_eq_scaled_liftedStrict
    theta h b hInterior epsilon K t]
  change
    (commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize)[
        (fun omega : CommonOmega
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize =>
          scale ^ 2 * liftedStrictLindebergObservable
            (exactBatchArrayData theta h b hInterior) exactBatchRowSize
            embedded.1 embedded.2 threshold omega) |
        augmentedRowFiltrationSigma
          (exactBatchArrayData theta h b hInterior) exactBatchRowSize
          embedded.1 embedded.2.val] =ᵐ[
            commonMeasure (exactBatchArrayData theta h b hInterior)
              exactBatchRowSize]
      (fun omega => scale ^ 2 * liftedStrictOneShotLindebergKernel
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        embedded.1 embedded.2 threshold omega)
  exact hscaled

/-! ## Adaptedness and finite integrability -/

/-- The sigma algebra after global shot `n` contains the current row prefix
through that shot. -/
theorem currentRowSuccSigma_le_globalSucc
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) :
    augmentedRowFiltrationSigma
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize
        (globalBatch n) (globalWithin n + 1) <=
      globalFinalFiltrationSigma theta h b hInterior (n + 1) := by
  have hmonoBatch : globalBatch n <= globalBatch (n + 1) :=
    globalBatch_mono (Nat.le_succ n)
  by_cases hbatch : globalBatch n = globalBatch (n + 1)
  · unfold globalFinalFiltrationSigma
    rw [← hbatch]
    apply augmentedRowFiltrationSigma_mono
    have hlower := globalBatch_lower n
    unfold globalWithin
    rw [← hbatch]
    omega
  · have hlt : globalBatch n < globalBatch (n + 1) :=
      lt_of_le_of_ne hmonoBatch hbatch
    exact augmentedRowFiltrationSigma_le_of_lt theta h b hInterior hlt
      (globalWithin n + 1) (globalWithin (n + 1))

theorem cumulativeIncrement_measurable_succ
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    Measurable[(globalFinalFiltration theta h b hInterior).seq (t.val + 1)]
      (prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t) := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  have hmeas := liftedScore_measurable_succ
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize
    embedded.1 embedded.2
  have hle := currentRowSuccSigma_le_globalSucc theta h b hInterior t.val
  rw [globalBatch_enumeratedShot, globalWithin_enumeratedShot] at hle
  rw [cumulativeIncrement_eq_scaled_liftedScore theta h b hInterior K t]
  exact (hmeas.const_mul scale).mono hle le_rfl

theorem cumulativeIncrement_integrable
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    Integrable (prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t)
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scale := prespecifiedBatchCumulativeShotScale K shot.1
  have hlift := liftRowVariable_integrable
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize embedded.1
    ((exactBatchArrayData theta h b hInterior embedded.1).currentCoordinateObservable
      (exactBatchRowSize embedded.1) embedded.2
      ((exactBatchArrayData theta h b hInterior embedded.1).scoreObservable
        (exactBatchRowSize embedded.1) embedded.2))
    ((exactBatchArrayData theta h b hInterior embedded.1).integrable_mathlibRowMeasure
      (exactBatchRowSize embedded.1) _)
  have hscore : Integrable
      (liftedScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize embedded.1 embedded.2)
      (commonMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize) := by
    simpa [liftedScore] using hlift
  have hscaled := hscore.const_mul scale
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  rw [cumulativeIncrement_eq_scaled_liftedScore theta h b hInterior K t]
  change Integrable
    (fun omega : CommonOmega
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize =>
      scale * liftedScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize embedded.1 embedded.2 omega)
    (commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize)
  exact hscaled

theorem cumulativeIncrement_square_integrable
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
    Integrable (fun omega =>
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2)
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) := by
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let embedded := embedFiniteShot shot
  let scaleSq := prespecifiedBatchCumulativeShotScale K shot.1 ^ 2
  have hlift := liftRowVariable_integrable
    (exactBatchArrayData theta h b hInterior) exactBatchRowSize embedded.1
    ((exactBatchArrayData theta h b hInterior embedded.1).currentCoordinateObservable
      (exactBatchRowSize embedded.1) embedded.2
      ((exactBatchArrayData theta h b hInterior embedded.1).squaredScoreObservable
        (exactBatchRowSize embedded.1) embedded.2))
    ((exactBatchArrayData theta h b hInterior embedded.1).integrable_mathlibRowMeasure
      (exactBatchRowSize embedded.1) _)
  have hsquare : Integrable
      (liftedSquaredScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize embedded.1 embedded.2)
      (commonMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize) := by
    simpa [liftedSquaredScore] using hlift
  have hscaled := hsquare.const_mul scaleSq
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  rw [cumulativeIncrement_square_eq_scaled_liftedSquaredScore
    theta h b hInterior K t]
  change Integrable
    (fun omega : CommonOmega
        (exactBatchArrayData theta h b hInterior) exactBatchRowSize =>
      scaleSq * liftedSquaredScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize embedded.1 embedded.2 omega)
    (commonMeasure (exactBatchArrayData theta h b hInterior)
      exactBatchRowSize)
  exact hscaled

/-! ## Complete finite martingale certificate -/

theorem cumulativeConditionalLindeberg_converges
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    forall epsilon : Real, 0 < epsilon ->
      HallHeydeScalarConvergesInProbability
        (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))
        (fun K omega =>
          ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeConditionalLindeberg
              theta h b hInterior epsilon K t omega)
        0 := by
  intro epsilon hepsilon delta hdelta
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  have hzero := prespecifiedBatchCumulativeLindebergTruncand_eventually_zero
    theta h b hInterior epsilon hepsilon
  have hprobabilityZero :
      (fun K => mu {omega |
        delta <= |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          prespecifiedBatchCumulativeConditionalLindeberg
            theta h b hInterior epsilon K t omega) - 0|}) =ᶠ[atTop]
        (fun _ : Nat => (0 : ENNReal)) := by
    filter_upwards [hzero] with K hK
    have hkernel (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)) :
        prespecifiedBatchCumulativeConditionalLindeberg
            theta h b hInterior epsilon K t =ᵐ[mu]
          (fun _ => (0 : Real)) := by
      have hce := cumulativeLindeberg_condExp_eq_kernel
        theta h b hInterior epsilon K t
      have hfun :
          (fun omega =>
            if epsilon <
                |prespecifiedBatchCumulativeEnumeratedIncrement
                  theta h b K t omega|
            then prespecifiedBatchCumulativeEnumeratedIncrement
              theta h b K t omega ^ 2
            else 0) = fun _ => (0 : Real) := by
        funext omega
        exact hK t omega
      rw [hfun] at hce
      change
        mu[(0 : ExactConcretePredeterminedBatchPath -> Real) |
          globalFinalFiltrationSigma theta h b hInterior t.val] =ᵐ[mu]
          prespecifiedBatchCumulativeConditionalLindeberg
            theta h b hInterior epsilon K t at hce
      rw [condExp_zero] at hce
      exact hce.symm
    have hall :
        ∀ᵐ omega ∂mu,
          ∀ t ∈ (Finset.univ :
            Finset (Fin (prespecifiedBatchCumulativeFinalRowLength K))),
            prespecifiedBatchCumulativeConditionalLindeberg
              theta h b hInterior epsilon K t omega = 0 :=
      (Finset.eventually_all Finset.univ).2
        (fun t _ht => hkernel t)
    have hsum :
        (fun omega =>
          ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeConditionalLindeberg
              theta h b hInterior epsilon K t omega) =ᵐ[mu]
          (fun _ => (0 : Real)) := by
      filter_upwards [hall] with omega homega
      exact Finset.sum_eq_zero (fun t ht => homega t ht)
    have hset :
        {omega : ExactConcretePredeterminedBatchPath |
          delta <= |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeConditionalLindeberg
              theta h b hInterior epsilon K t omega) - 0|} =ᵐ[mu]
          (∅ : Set ExactConcretePredeterminedBatchPath) := by
      filter_upwards [hsum] with omega homega
      change
        (delta <= |∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          prespecifiedBatchCumulativeConditionalLindeberg
            theta h b hInterior epsilon K t omega - 0|) = False
      rw [homega]
      simp [not_le_of_gt hdelta]
    calc
      mu {omega |
        delta <= |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          prespecifiedBatchCumulativeConditionalLindeberg
            theta h b hInterior epsilon K t omega) - 0|} =
          mu (∅ : Set ExactConcretePredeterminedBatchPath) := measure_congr hset
      _ = 0 := measure_empty
  simpa [mu] using tendsto_const_nhds.congr' hprobabilityZero.symm

/-- Fully constructed martingale certificate for the concrete prespecified-
batch protocol.  The same global filtration is used at every horizon. -/
noncomputable def prespecifiedBatchCumulativeMartingaleCertificate
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    PrespecifiedBatchCumulativeMartingaleCertificate
      theta h b (le_of_lt hInterior) where
  filtration := fun _ => globalFinalFiltration theta h b hInterior
  conditionalLindeberg := fun epsilon K t =>
    prespecifiedBatchCumulativeConditionalLindeberg
      theta h b hInterior epsilon K t
  condition321 := by
    intro n k hk hknext
    exact le_rfl
  increment_measurable := by
    intro K t
    exact cumulativeIncrement_measurable_succ theta h b hInterior K t
  increment_integrable := by
    intro K t
    exact cumulativeIncrement_integrable theta h b hInterior K t
  increment_square_integrable := by
    intro K t
    exact cumulativeIncrement_square_integrable theta h b hInterior K t
  martingaleDifference := by
    intro K t
    exact cumulativeIncrement_condExp_zero theta h b hInterior K t
  conditionalVarianceVersion := by
    intro K t
    exact cumulativeIncrement_square_condExp_eq_variance
      theta h b hInterior K t
  conditionalLindebergVersion := by
    intro epsilon hepsilon K t
    exact cumulativeLindeberg_condExp_eq_kernel
      theta h b hInterior epsilon K t
  conditionalLindeberg_converges := by
    intro epsilon hepsilon
    exact cumulativeConditionalLindeberg_converges
      theta h b hInterior epsilon hepsilon

/-- Hall--Heyde premises for the exact protocol, conditional only on the
separately named concrete cumulative Fisher convergence statement. -/
noncomputable def prespecifiedBatchCumulativeHallHeydePremises_closed
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (sigmaSq : Real) (hsigmaSq : 0 <= sigmaSq)
    (hFisher : PrespecifiedBatchCumulativeFisherConvergesInProbability
      theta h b (le_of_lt hInterior) sigmaSq) :
    HallHeyde1980Corollary31DeterministicVariancePremises
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))
      prespecifiedBatchCumulativeFinalRowLength
      (fun _ => globalFinalFiltration theta h b hInterior)
      (prespecifiedBatchCumulativeEnumeratedIncrement theta h b)
      (prespecifiedBatchCumulativeConditionalVariance theta h b)
      (fun epsilon K t =>
        prespecifiedBatchCumulativeConditionalLindeberg
          theta h b hInterior epsilon K t)
      sigmaSq :=
  prespecifiedBatchCumulativeHallHeydePremises
    theta h b (le_of_lt hInterior) sigmaSq hsigmaSq
    (prespecifiedBatchCumulativeMartingaleCertificate theta h b hInterior)
    hFisher

/-! ## Cumulative observed directional information -/

/-- Current within-row shot in the exact row-size type. -/
def globalRowShot (n : Nat) :
    Fin (3 * exactBatchRowSize (globalBatch n)) :=
  ⟨globalWithin n, by
    simpa [finalShotBlockSize, exactBatchRowSize] using
      globalWithin_lt_size n⟩

/-- Raw-scale centered observed directional information for global final shot
`n`.  Multiplication by `3 r_k` removes row normalization. -/
noncomputable def globalCenteredObservedInformation
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) : ExactConcretePredeterminedBatchPath -> Real :=
  fun omega =>
    ((3 * exactBatchRowSize (globalBatch n) : Nat) : Real) *
      (liftedSquaredScore (exactBatchArrayData theta h b hInterior)
          exactBatchRowSize (globalBatch n) (globalRowShot n) omega -
        liftedOneShotFisher (exactBatchArrayData theta h b hInterior)
          exactBatchRowSize (globalBatch n) (globalRowShot n) omega)

theorem liftedOneShotFisher_measurable_predictable
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) (t : Fin (3 * exactBatchRowSize n)) :
    Measurable[augmentedRowFiltrationSigma
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize n t.val]
      (liftedOneShotFisher (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize n t) := by
  let A := exactBatchArrayData theta h b hInterior n
  have hfinite := A.squaredScore_finiteConditionalExpectation_eq_oneShotFisher
    (exactBatchRowSize n) (exactBatchRowSize_pos n) t
  have hrow := A.measurable_of_history_invariant
    (exactBatchRowSize n) t.val
    (A.oneShotFisherKernel (exactBatchRowSize n) t)
    hfinite.prefixInvariant
  simpa [liftedOneShotFisher] using
    liftRowVariable_measurable
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize n t.val
      (A.oneShotFisherKernel (exactBatchRowSize n) t) hrow

theorem liftedOneShotFisher_integrable_exact
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) (t : Fin (3 * exactBatchRowSize n)) :
    Integrable
      (liftedOneShotFisher (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize n t)
      (commonMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize) := by
  simpa [liftedOneShotFisher] using
    liftRowVariable_integrable
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize n
      ((exactBatchArrayData theta h b hInterior n).oneShotFisherKernel
        (exactBatchRowSize n) t)
      ((exactBatchArrayData theta h b hInterior n).integrable_mathlibRowMeasure
        (exactBatchRowSize n) _)

theorem liftedSquaredScore_integrable_exact
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) (t : Fin (3 * exactBatchRowSize n)) :
    Integrable
      (liftedSquaredScore (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize n t)
      (commonMeasure (exactBatchArrayData theta h b hInterior)
        exactBatchRowSize) := by
  simpa [liftedSquaredScore] using
    liftRowVariable_integrable
      (exactBatchArrayData theta h b hInterior) exactBatchRowSize n
      ((exactBatchArrayData theta h b hInterior n).currentCoordinateObservable
        (exactBatchRowSize n) t
        ((exactBatchArrayData theta h b hInterior n).squaredScoreObservable
          (exactBatchRowSize n) t))
      ((exactBatchArrayData theta h b hInterior n).integrable_mathlibRowMeasure
        (exactBatchRowSize n) _)

theorem globalCenteredObservedInformation_condExp_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      globalCenteredObservedInformation theta h b hInterior n |
      globalFinalFiltrationSigma theta h b hInterior n] =ᵐ[
        exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      (fun _ => (0 : Real)) := by
  let A := exactBatchArrayData theta h b hInterior
  let t := globalRowShot n
  let a : Real := (3 * exactBatchRowSize (globalBatch n) : Nat)
  let mu := commonMeasure A exactBatchRowSize
  let sigma := augmentedRowFiltrationSigma A exactBatchRowSize
    (globalBatch n) t.val
  have hsquare := liftedSquaredScore_condExp_eq_oneShotFisher_closed
    A exactBatchRowSize (globalBatch n)
    (exactBatchRowSize_pos (globalBatch n)) t
  have hsquareInt := liftedSquaredScore_integrable_exact
    theta h b hInterior (globalBatch n) t
  have hfisherInt := liftedOneShotFisher_integrable_exact
    theta h b hInterior (globalBatch n) t
  have hfisherMeas := liftedOneShotFisher_measurable_predictable
    theta h b hInterior (globalBatch n) t
  have hfisherCond :
      mu[liftedOneShotFisher A exactBatchRowSize (globalBatch n) t | sigma] =
        liftedOneShotFisher A exactBatchRowSize (globalBatch n) t := by
    exact condExp_of_stronglyMeasurable
      (augmentedRowFiltrationSigma_le A exactBatchRowSize
        (globalBatch n) t.val)
      hfisherMeas.stronglyMeasurable hfisherInt
  have hsub := condExp_sub hsquareInt hfisherInt sigma
  have hcentered :
      mu[(fun omega =>
        liftedSquaredScore A exactBatchRowSize (globalBatch n) t omega -
          liftedOneShotFisher A exactBatchRowSize (globalBatch n) t omega) |
        sigma] =ᵐ[mu] (fun _ => (0 : Real)) := by
    filter_upwards [hsub, hsquare] with omega hsubOmega hsquareOmega
    change
      mu[(fun omega =>
        liftedSquaredScore A exactBatchRowSize (globalBatch n) t omega -
          liftedOneShotFisher A exactBatchRowSize (globalBatch n) t omega) |
        sigma] omega =
      (mu[liftedSquaredScore A exactBatchRowSize (globalBatch n) t | sigma] -
        mu[liftedOneShotFisher A exactBatchRowSize (globalBatch n) t | sigma])
          omega at hsubOmega
    rw [hsubOmega]
    change
      mu[liftedSquaredScore A exactBatchRowSize (globalBatch n) t | sigma] omega -
        mu[liftedOneShotFisher A exactBatchRowSize (globalBatch n) t | sigma] omega = 0
    rw [hsquareOmega, congrFun hfisherCond omega]
    simp
  have hsmul := MeasureTheory.condExp_smul (μ := mu) a
    (fun omega =>
      liftedSquaredScore A exactBatchRowSize (globalBatch n) t omega -
        liftedOneShotFisher A exactBatchRowSize (globalBatch n) t omega)
    sigma
  have hscaled := hsmul.trans (hcentered.const_smul a)
  have hleft :
      a • (fun omega =>
        liftedSquaredScore A exactBatchRowSize (globalBatch n) t omega -
          liftedOneShotFisher A exactBatchRowSize (globalBatch n) t omega) =
      globalCenteredObservedInformation theta h b hInterior n := by
    funext omega
    simp [globalCenteredObservedInformation, A, t, a, smul_eq_mul]
  rw [hleft] at hscaled
  have hzero :
      a • (fun _ : CommonOmega A exactBatchRowSize => (0 : Real)) =ᵐ[mu]
        (fun _ => (0 : Real)) := by
    filter_upwards
    intro omega
    change a • (0 : Real) = 0
    simp
  have hscaledZero := hscaled.trans hzero
  rw [globalFinalFiltrationSigma]
  rw [← exactBatchCommonMeasure_eq theta h b hInterior]
  change
    mu[globalCenteredObservedInformation theta h b hInterior n | sigma] =ᵐ[mu]
      (fun _ => (0 : Real))
  exact hscaledZero

theorem globalCenteredObservedInformation_measurable_succ
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) :
    Measurable[(globalFinalFiltration theta h b hInterior).seq (n + 1)]
      (globalCenteredObservedInformation theta h b hInterior n) := by
  let A := exactBatchArrayData theta h b hInterior
  let t := globalRowShot n
  have hscore := liftedScore_measurable_succ A exactBatchRowSize
    (globalBatch n) t
  have hsquare :
      Measurable[augmentedRowFiltrationSigma A exactBatchRowSize
        (globalBatch n) (t.val + 1)]
        (liftedSquaredScore A exactBatchRowSize (globalBatch n) t) := by
    have hsqeq :
        liftedSquaredScore A exactBatchRowSize (globalBatch n) t =
          fun omega => liftedScore A exactBatchRowSize (globalBatch n) t omega ^ 2 := by
      funext omega
      rfl
    rw [hsqeq]
    exact hscore.pow_const 2
  have hfisher0 := liftedOneShotFisher_measurable_predictable
    theta h b hInterior (globalBatch n) t
  have hfisher :
      Measurable[augmentedRowFiltrationSigma A exactBatchRowSize
        (globalBatch n) (t.val + 1)]
        (liftedOneShotFisher A exactBatchRowSize (globalBatch n) t) :=
    hfisher0.mono
      (augmentedRowFiltrationSigma_mono A exactBatchRowSize
        (globalBatch n) (Nat.le_succ t.val)) le_rfl
  have hrow := (hsquare.sub hfisher).const_mul
    ((3 * exactBatchRowSize (globalBatch n) : Nat) : Real)
  exact hrow.mono
    (currentRowSuccSigma_le_globalSucc theta h b hInterior n) le_rfl

theorem globalCenteredObservedInformation_abs_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (n : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    |globalCenteredObservedInformation theta h b hInterior n omega| <=
      2 * mixedProjectedScoreEnvelope theta h ^ 2 := by
  let k := globalBatch n
  let t := globalRowShot n
  let r := exactBatchRowSize k
  have hr : 0 < r := exactBatchRowSize_pos k
  have hcenter := mixedExactCycleCenteredObservedSquare_abs_le
    theta h (exactConcreteBatchSelectedFrame k b) (omega k).1 t (omega k).2
    hInterior hr
  have ha : (0 : Real) < (3 * r : Nat) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) hr
  have hsqrt : Real.sqrt (3 * r : Nat) ^ 2 = (3 * r : Nat) :=
    Real.sq_sqrt (le_of_lt ha)
  change |((3 * r : Nat) : Real) *
      mixedExactCycleCenteredObservedSquare theta h
        (exactConcreteBatchSelectedFrame k b) (omega k).1 t (omega k).2| <= _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : Real) <= (3 * r : Nat))]
  calc
    ((3 * r : Nat) : Real) *
        |mixedExactCycleCenteredObservedSquare theta h
          (exactConcreteBatchSelectedFrame k b) (omega k).1 t (omega k).2| <=
      ((3 * r : Nat) : Real) *
        (2 * (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : Nat)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcenter (by positivity)
    _ = 2 * mixedProjectedScoreEnvelope theta h ^ 2 := by
      rw [div_pow, hsqrt]
      field_simp [ne_of_gt ha]

/-- Shifted sequence expected by the source-free bounded martingale strong
law: index zero is zero and index `n+1` is global final-shot innovation `n`. -/
noncomputable def observedInformationInnovationSequence
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    Nat -> ExactConcretePredeterminedBatchPath -> Real
  | 0 => fun _ => 0
  | n + 1 => globalCenteredObservedInformation theta h b hInterior n

theorem observedInformationInnovationSequence_stronglyAdapted
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    StronglyAdapted (globalFinalFiltration theta h b hInterior)
      (observedInformationInnovationSequence theta h b hInterior) := by
  intro n
  cases n with
  | zero =>
      exact stronglyMeasurable_const
  | succ n =>
      exact (globalCenteredObservedInformation_measurable_succ
        theta h b hInterior n).stronglyMeasurable

theorem observedInformationInnovationSequence_sum_eq
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (M : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    (∑ i ∈ Finset.range (M + 1),
      observedInformationInnovationSequence theta h b hInterior i omega) =
      ∑ n ∈ Finset.range M,
        globalCenteredObservedInformation theta h b hInterior n omega := by
  induction M with
  | zero => simp [observedInformationInnovationSequence]
  | succ M ih =>
      rw [show Nat.succ M + 1 = (M + 1) + 1 by omega,
        Finset.sum_range_succ, ih, Finset.sum_range_succ]
      rfl

/-- Almost-sure strong law for the global centered observed information. -/
theorem globalCenteredObservedInformation_average_ae_tendsto_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᵐ omega ∂exactConcretePredeterminedBatchPathMeasure
        theta b (le_of_lt hInterior),
      Tendsto
        (fun M : Nat => (M : Real)⁻¹ *
          ∑ n ∈ Finset.range M,
            globalCenteredObservedInformation theta h b hInterior n omega)
        atTop (nhds 0) := by
  let mu := exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  have hslln := boundedMartingaleDifference_average_ae_tendsto_zero
    mu (globalFinalFiltration theta h b hInterior)
    (observedInformationInnovationSequence theta h b hInterior)
    (observedInformationInnovationSequence_stronglyAdapted
      theta h b hInterior)
    rfl
    (fun n => globalCenteredObservedInformation_condExp_zero
      theta h b hInterior n)
    (2 * mixedProjectedScoreEnvelope theta h ^ 2)
    (by positivity)
    (by
      intro n omega
      cases n with
      | zero =>
          rw [show observedInformationInnovationSequence
            theta h b hInterior 0 omega = 0 by rfl, norm_zero]
          positivity
      | succ n =>
          simpa [Real.norm_eq_abs, observedInformationInnovationSequence] using
            globalCenteredObservedInformation_abs_le
              theta h b hInterior n omega)
  filter_upwards [hslln] with omega homega
  simpa [observedInformationInnovationSequence_sum_eq] using homega

end PrespecifiedBatchMartingaleClosure

end

end QubitOracle.Paper
