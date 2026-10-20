import QubitOracle.Paper.OneQubitMixedTwoStageFiniteScore

/-!
# Exact information for complete three-axis cycles

For a final horizon `3 * r`, the deterministic allocation visits the three
pilot-selected frame columns in the order `0,1,2,0,1,2,...`.  This module
constructs the explicit finite equivalence

`Fin r × Fin 3 ≃ Fin (3 * r)`,  `(block, axis) ↦ 3 * block + axis`,

proves its compatibility with `mixedTwoStageCycleIndex`, and uses finite-sum
reindexing to obtain exact count and information identities.  No probability
law, limit, or asymptotic premise is used in the combinatorial results.
-/

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

/-! ## Mechanical cycle equivalence -/

/-- Explicit block-axis parametrization of the `3 * r` final times. -/
def mixedTwoStageExactCycleEquiv (r : ℕ) :
    Fin r × Fin 3 ≃ Fin (3 * r) where
  toFun p := ⟨3 * p.1.1 + p.2.1, by
    have hb := p.1.isLt
    have hk := p.2.isLt
    omega⟩
  invFun t :=
    (⟨t.1 / 3, by
      have ht := t.isLt
      omega⟩,
     ⟨t.1 % 3, Nat.mod_lt _ (by norm_num)⟩)
  left_inv p := by
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have hb := p.1.isLt
      have hk := p.2.isLt
      omega
    · apply Fin.ext
      dsimp
      have hb := p.1.isLt
      have hk := p.2.isLt
      omega
  right_inv t := by
    apply Fin.ext
    dsimp
    have ht := t.isLt
    have hdiv := Nat.mod_add_div t.1 3
    omega

/-- The explicit equivalence records the expected arithmetic index. -/
@[simp]
theorem mixedTwoStageExactCycleEquiv_apply_val
    (r : ℕ) (block : Fin r) (k : Fin 3) :
    (mixedTwoStageExactCycleEquiv r (block, k)).1 =
      3 * block.1 + k.1 :=
  rfl

/-- The deterministic cycle index of `(block, k)` is exactly `k`. -/
@[simp]
theorem mixedTwoStageCycleIndex_exactCycleEquiv
    (r : ℕ) (block : Fin r) (k : Fin 3) :
    mixedTwoStageCycleIndex
      (mixedTwoStageExactCycleEquiv r (block, k)) = k := by
  apply Fin.ext
  change (3 * block.1 + k.1) % 3 = k.1
  have hk := k.isLt
  omega

/-- Item 1, in indicator-count form: exactly `r` final times have cycle
index `k`. -/
theorem mixedTwoStageCycleIndex_count_exact
    (r : ℕ) (k : Fin 3) :
    (∑ t : Fin (3 * r),
      if mixedTwoStageCycleIndex t = k then 1 else 0) = r := by
  calc
    (∑ t : Fin (3 * r),
      if mixedTwoStageCycleIndex t = k then 1 else 0) =
      ∑ p : Fin r × Fin 3,
        if mixedTwoStageCycleIndex
            (mixedTwoStageExactCycleEquiv r p) = k
        then 1 else 0 := by
      exact (Fintype.sum_equiv (mixedTwoStageExactCycleEquiv r)
        (fun p : Fin r × Fin 3 =>
          if mixedTwoStageCycleIndex
              (mixedTwoStageExactCycleEquiv r p) = k
          then 1 else 0)
        (fun t : Fin (3 * r) =>
          if mixedTwoStageCycleIndex t = k then 1 else 0)
        (fun _ => rfl)).symm
    _ = ∑ p : Fin r × Fin 3, if p.2 = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rcases p with ⟨block, j⟩
      simp
    _ = r := by
      rw [Fintype.sum_prod_type]
      simp

/-! ## Exact directional information -/

/-- The one-shot directional Fisher term from
`mixedTwoStageConditionalFinalScoreSum_secondMoment`. -/
def mixedTwoStageFinalDirectionalFisherTerm
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) : ℝ :=
  QubitOracle.blochDot h
      (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
    (1 - QubitOracle.blochDot theta
      (mixedTwoStageFinalAxis selected pilot t) ^ 2)

/-- The same Fisher term indexed directly by one selected frame column. -/
def mixedTwoStageFrameColumnDirectionalFisherTerm
    {q : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (k : Fin 3) : ℝ :=
  QubitOracle.blochDot h
      (mixedTwoStageFrameAxis (selected.frame pilot) k) ^ 2 /
    (1 - QubitOracle.blochDot theta
      (mixedTwoStageFrameAxis (selected.frame pilot) k) ^ 2)

/-- Under the block-axis equivalence, a final-time Fisher term is exactly the
corresponding frame-column term. -/
@[simp]
theorem mixedTwoStageFinalDirectionalFisherTerm_exactCycleEquiv
    {q : ℕ} (r : ℕ) (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (block : Fin r) (k : Fin 3) :
    mixedTwoStageFinalDirectionalFisherTerm theta h selected pilot
        (mixedTwoStageExactCycleEquiv r (block, k)) =
      mixedTwoStageFrameColumnDirectionalFisherTerm
        theta h selected pilot k := by
  simp [mixedTwoStageFinalDirectionalFisherTerm,
    mixedTwoStageFrameColumnDirectionalFisherTerm,
    mixedTwoStageFinalAxis]

/-- Item 2: the information over `3 * r` final times is `r` times the
three-frame-column information. -/
theorem mixedTwoStageExactCycleInformation_sum
    {q : ℕ} (r : ℕ) (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ t : Fin (3 * r),
      mixedTwoStageFinalDirectionalFisherTerm
        theta h selected pilot t) =
      (r : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
  calc
    (∑ t : Fin (3 * r),
      mixedTwoStageFinalDirectionalFisherTerm
        theta h selected pilot t) =
      ∑ p : Fin r × Fin 3,
        mixedTwoStageFinalDirectionalFisherTerm theta h selected pilot
          (mixedTwoStageExactCycleEquiv r p) := by
      exact (Fintype.sum_equiv (mixedTwoStageExactCycleEquiv r)
        (fun p : Fin r × Fin 3 =>
          mixedTwoStageFinalDirectionalFisherTerm theta h selected pilot
            (mixedTwoStageExactCycleEquiv r p))
        (fun t : Fin (3 * r) =>
          mixedTwoStageFinalDirectionalFisherTerm
            theta h selected pilot t)
        (fun _ => rfl)).symm
    _ = ∑ p : Fin r × Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rcases p with ⟨block, k⟩
      exact mixedTwoStageFinalDirectionalFisherTerm_exactCycleEquiv
        r theta h selected pilot block k
    _ = ∑ _block : Fin r, ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
      rw [Fintype.sum_prod_type]
    _ = (r : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
      simp [nsmul_eq_mul]

/-- Item 3: after division by the positive horizon `3 * r`, exact-cycle
information is one third of the complete three-axis information. -/
theorem mixedTwoStageExactCycleInformation_normalized
    {q : ℕ} {r : ℕ} (hr : 0 < r)
    (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ t : Fin (3 * r),
      mixedTwoStageFinalDirectionalFisherTerm
        theta h selected pilot t) /
        ((3 * r : ℕ) : ℝ) =
      (1 / 3 : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
  rw [mixedTwoStageExactCycleInformation_sum]
  have hrReal : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hr)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hrReal]
  <;> ring

/-! ## Exact-cycle specialization of the finite score identity -/

/-- Item 4: the conditional second moment of the total final score over
`3 * r` shots is exactly `r` times the complete three-column Fisher sum. -/
theorem mixedTwoStageConditionalFinalScoreSum_secondMoment_exactCycle
    {q : ℕ} (r : ℕ) (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) =
      (r : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) =
      ∑ t : Fin (3 * r),
        mixedTwoStageFinalDirectionalFisherTerm
          theta h selected pilot t := by
      simpa [mixedTwoStageFinalDirectionalFisherTerm] using
        (mixedTwoStageConditionalFinalScoreSum_secondMoment
          (T := 3 * r) theta h selected hInterior pilot)
    _ = (r : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k :=
      mixedTwoStageExactCycleInformation_sum
        r theta h selected pilot

/-- Normalized form of the exact conditional score identity for `r > 0`. -/
theorem mixedTwoStageConditionalFinalScoreSum_secondMoment_exactCycle_normalized
    {q r : ℕ} (hr : 0 < r) (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) /
        ((3 * r : ℕ) : ℝ) =
      (1 / 3 : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) /
        ((3 * r : ℕ) : ℝ) =
      (∑ t : Fin (3 * r),
        mixedTwoStageFinalDirectionalFisherTerm
          theta h selected pilot t) /
        ((3 * r : ℕ) : ℝ) := by
      simpa [mixedTwoStageFinalDirectionalFisherTerm] using
        congrArg (fun x : ℝ => x / ((3 * r : ℕ) : ℝ))
          (mixedTwoStageConditionalFinalScoreSum_secondMoment
            (T := 3 * r) theta h selected hInterior pilot)
    _ = (1 / 3 : ℝ) * ∑ k : Fin 3,
        mixedTwoStageFrameColumnDirectionalFisherTerm
          theta h selected pilot k :=
      mixedTwoStageExactCycleInformation_normalized
        hr theta h selected pilot

end

end QubitOracle.Paper
