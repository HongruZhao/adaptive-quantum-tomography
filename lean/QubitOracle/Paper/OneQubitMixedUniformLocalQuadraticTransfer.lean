import QubitOracle.Paper.OneQubitMixedUniformLocalRemainderRates

namespace QubitOracle.Paper

noncomputable section

open Filter

/-- Every coordinate square is bounded by the three-dimensional Bloch norm. -/
theorem blochCoordinate_sq_le_normSq
    (x : RLSVector 3) (j : Fin 3) :
    x j ^ 2 ≤ blochNormSq x := by
  fin_cases j <;>
    simp [blochNormSq, Fin.sum_univ_succ] <;>
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

/-- Coordinatewise control from a Bloch-norm bound. -/
theorem blochCoordinate_abs_le_of_normSq_le
    (x : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hNorm : blochNormSq x ≤ H ^ 2)
    (j : Fin 3) :
    |x j| ≤ H := by
  have hSq : x j ^ 2 ≤ H ^ 2 :=
    le_trans (blochCoordinate_sq_le_normSq x j) hNorm
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x j - H), sq_nonneg (x j + H)]

/-- A local Bloch alternative is linear in every rotated frame coordinate. -/
theorem qubitFrameCoordinates_localAlternative_sub
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (theta h : RLSVector 3)
    (N : ℕ → ℕ) (n : ℕ) (k : Fin 3) :
    qubitFrameCoordinates R (mixedLocalAlternative theta N n h) k
        - qubitFrameCoordinates R theta k =
      mixedLocalScale N n * qubitFrameCoordinates R h k := by
  simp [qubitFrameCoordinates, mixedLocalAlternative, blochDot,
    qubitFrameAxis, Fin.sum_univ_succ]
  ring

/-- Uniform coordinate displacement of a bounded local alternative in any
orthonormal measurement frame. -/
theorem qubitFrameCoordinates_localAlternative_abs_sub_le
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (theta h : RLSVector 3)
    (N : ℕ → ℕ) (H : ℝ) (n : ℕ)
    (hH : 0 ≤ H)
    (hBall : MixedLocalDirectionBall H h)
    (k : Fin 3) :
    |qubitFrameCoordinates R (mixedLocalAlternative theta N n h) k
        - qubitFrameCoordinates R theta k| ≤
      mixedLocalScale N n * H := by
  rw [qubitFrameCoordinates_localAlternative_sub]
  have hCoordinate : |qubitFrameCoordinates R h k| ≤ H := by
    apply blochCoordinate_abs_le_of_normSq_le
      (qubitFrameCoordinates R h) H hH
    · rw [qubitFrameCoordinates_blochNormSq_of_orthonormal h R hR]
      exact hBall
  have hScale : 0 ≤ mixedLocalScale N n := by
    simp [mixedLocalScale]
  rw [abs_mul, abs_of_nonneg hScale]
  exact mul_le_mul_of_nonneg_left hCoordinate hScale

/-- The square map is `2`-Lipschitz on `[-1,1]`. -/
theorem abs_sq_sub_sq_le_two_mul
    (a b delta : ℝ)
    (ha : |a| ≤ 1)
    (hb : |b| ≤ 1)
    (hdelta : |a - b| ≤ delta)
    (hdeltaNonnegative : 0 ≤ delta) :
    |a ^ 2 - b ^ 2| ≤ 2 * delta := by
  have hsum : |a + b| ≤ 2 := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le a b
      _ ≤ 2 := by linarith
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
  calc
    |a - b| * |a + b| ≤ delta * 2 :=
      mul_le_mul hdelta hsum (abs_nonneg _) hdeltaNonnegative
    _ = 2 * delta := by ring

/-- The fourth-power map is `4`-Lipschitz on `[-1,1]`. -/
theorem abs_pow_four_sub_pow_four_le_four_mul
    (a b delta : ℝ)
    (ha : |a| ≤ 1)
    (hb : |b| ≤ 1)
    (hdelta : |a - b| ≤ delta)
    (hdeltaNonnegative : 0 ≤ delta) :
    |a ^ 4 - b ^ 4| ≤ 4 * delta := by
  have hSq := abs_sq_sub_sq_le_two_mul
    a b delta ha hb hdelta hdeltaNonnegative
  have haSq : a ^ 2 ≤ 1 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hbSq : b ^ 2 ≤ 1 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hsum : |a ^ 2 + b ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
    linarith
  rw [show a ^ 4 - b ^ 4 = (a ^ 2 - b ^ 2) * (a ^ 2 + b ^ 2) by ring,
    abs_mul]
  calc
    |a ^ 2 - b ^ 2| * |a ^ 2 + b ^ 2| ≤ (2 * delta) * 2 :=
      mul_le_mul hSq hsum (abs_nonneg _) (by positivity)
    _ = 4 * delta := by ring

/-- The Bernoulli variance polynomial `x²(1-x²)` is `6`-Lipschitz on
`[-1,1]`. -/
theorem abs_sq_mul_one_sub_sq_sub_le_six_mul
    (a b delta : ℝ)
    (ha : |a| ≤ 1)
    (hb : |b| ≤ 1)
    (hdelta : |a - b| ≤ delta)
    (hdeltaNonnegative : 0 ≤ delta) :
    |a ^ 2 * (1 - a ^ 2) - b ^ 2 * (1 - b ^ 2)| ≤ 6 * delta := by
  have hSq := abs_sq_sub_sq_le_two_mul
    a b delta ha hb hdelta hdeltaNonnegative
  have hFourth := abs_pow_four_sub_pow_four_le_four_mul
    a b delta ha hb hdelta hdeltaNonnegative
  have hIdentity :
      a ^ 2 * (1 - a ^ 2) - b ^ 2 * (1 - b ^ 2) =
        (a ^ 2 - b ^ 2) - (a ^ 4 - b ^ 4) := by ring
  rw [hIdentity]
  calc
    |(a ^ 2 - b ^ 2) - (a ^ 4 - b ^ 4)| ≤
        |a ^ 2 - b ^ 2| + |a ^ 4 - b ^ 4| := abs_sub _ _
    _ ≤ 2 * delta + 4 * delta := add_le_add hSq hFourth
    _ = 6 * delta := by ring

/-- Interior Bloch vectors have every orthonormal-frame coordinate in
`[-1,1]`. -/
theorem qubitFrameCoordinates_abs_le_one_of_interior
    (theta : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hInterior : blochNormSq theta < 1)
    (j : Fin 3) :
    |qubitFrameCoordinates R theta j| ≤ 1 := by
  apply blochCoordinate_abs_le_of_normSq_le
    (qubitFrameCoordinates R theta) 1 (by norm_num)
  rw [qubitFrameCoordinates_blochNormSq_of_orthonormal theta R hR]
  simpa only [one_pow] using le_of_lt hInterior

/-- Summed square terms in the three-coordinate risk formula vary by at most
`6 * delta`. -/
theorem abs_sum_one_sub_sq_sub_le_six_mul
    (u v : RLSVector 3)
    (delta : ℝ)
    (hu : ∀ j, |u j| ≤ 1)
    (hv : ∀ j, |v j| ≤ 1)
    (hdiff : ∀ j, |u j - v j| ≤ delta)
    (hdelta : 0 ≤ delta) :
    |(∑ j, (1 - u j ^ 2)) - ∑ j, (1 - v j ^ 2)| ≤
      6 * delta := by
  calc
    |(∑ j, (1 - u j ^ 2)) - ∑ j, (1 - v j ^ 2)| =
        |∑ j, ((1 - u j ^ 2) - (1 - v j ^ 2))| := by
      congr 1
      exact (Finset.sum_sub_distrib
        (fun j : Fin 3 => 1 - u j ^ 2)
        (fun j : Fin 3 => 1 - v j ^ 2)).symm
    _ ≤
        ∑ j, |(1 - u j ^ 2) - (1 - v j ^ 2)| := by
      exact Finset.abs_sum_le_sum_abs
        (fun j : Fin 3 => (1 - u j ^ 2) - (1 - v j ^ 2)) Finset.univ
    _ ≤ ∑ _j : Fin 3, 2 * delta := by
      apply Finset.sum_le_sum
      intro j _hj
      have hSq := abs_sq_sub_sq_le_two_mul
        (u j) (v j) delta (hu j) (hv j) (hdiff j) hdelta
      simpa [show (1 - u j ^ 2) - (1 - v j ^ 2) =
          v j ^ 2 - u j ^ 2 by ring, abs_sub_comm] using hSq
    _ = 6 * delta := by
      simp [Fin.sum_univ_succ]
      ring

/-- Summed Bernoulli-variance terms in the three-coordinate risk formula vary
by at most `18 * delta`. -/
theorem abs_sum_sq_mul_one_sub_sq_sub_le_eighteen_mul
    (u v : RLSVector 3)
    (delta : ℝ)
    (hu : ∀ j, |u j| ≤ 1)
    (hv : ∀ j, |v j| ≤ 1)
    (hdiff : ∀ j, |u j - v j| ≤ delta)
    (hdelta : 0 ≤ delta) :
    |(∑ j, u j ^ 2 * (1 - u j ^ 2)) -
        ∑ j, v j ^ 2 * (1 - v j ^ 2)| ≤
      18 * delta := by
  calc
    |(∑ j, u j ^ 2 * (1 - u j ^ 2)) -
        ∑ j, v j ^ 2 * (1 - v j ^ 2)| =
        |∑ j, (u j ^ 2 * (1 - u j ^ 2) -
          v j ^ 2 * (1 - v j ^ 2))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤
        ∑ j, |u j ^ 2 * (1 - u j ^ 2) -
          v j ^ 2 * (1 - v j ^ 2)| := by
      exact Finset.abs_sum_le_sum_abs
        (fun j : Fin 3 => u j ^ 2 * (1 - u j ^ 2) -
          v j ^ 2 * (1 - v j ^ 2)) Finset.univ
    _ ≤ ∑ _j : Fin 3, 6 * delta := by
      apply Finset.sum_le_sum
      intro j _hj
      exact abs_sq_mul_one_sub_sq_sub_le_six_mul
        (u j) (v j) delta (hu j) (hv j) (hdiff j) hdelta
    _ = 18 * delta := by
      simp [Fin.sum_univ_succ]
      ring

/-- A positive-denominator perturbation bound for a quotient.  This is the
only rational-algebra input needed for the local qubit risk transfer. -/
theorem abs_div_sub_div_le_of_pos
    (a b x y A B C : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hab : |a - b| ≤ A) (hb : |b| ≤ B)
    (hxy : |y - x| ≤ C) :
    |a / x - b / y| ≤ A / x + B * C / (x * y) := by
  have hxyPos : 0 < x * y := mul_pos hx hy
  have hIdentity :
      a / x - b / y =
        (a - b) / x + b * (y - x) / (x * y) := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    ring
  rw [hIdentity]
  calc
    |(a - b) / x + b * (y - x) / (x * y)| ≤
        |(a - b) / x| + |b * (y - x) / (x * y)| := abs_add_le _ _
    _ = |a - b| / x + |b| * |y - x| / (x * y) := by
      simp only [abs_div, abs_mul, abs_of_pos hx, abs_of_pos hxyPos]
    _ ≤ A / x + B * C / (x * y) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hab hx.le
      · apply div_le_div_of_nonneg_right
        exact mul_le_mul hb hxy (abs_nonneg _) hB
        exact hxyPos.le

/-- Replacing a denominator bounded below by half of `y` costs at most a
factor of two. -/
theorem div_le_two_mul_div_of_half_le
    (A x y : ℝ) (hA : 0 ≤ A) (hy : 0 < y)
    (hhalf : y / 2 ≤ x) :
    A / x ≤ (2 * A) / y := by
  have hx : 0 < x := by nlinarith
  apply (div_le_div_iff₀ hx hy).2
  have hmul := mul_le_mul_of_nonneg_left hhalf hA
  nlinarith

/-- The corresponding two-denominator estimate. -/
theorem div_mul_le_two_mul_div_sq_of_half_le
    (A x y : ℝ) (hA : 0 ≤ A) (hy : 0 < y)
    (hhalf : y / 2 ≤ x) :
    A / (x * y) ≤ (2 * A) / y ^ 2 := by
  have hx : 0 < x := by nlinarith
  have hxy : 0 < x * y := mul_pos hx hy
  have hysq : 0 < y ^ 2 := sq_pos_of_pos hy
  apply (div_le_div_iff₀ hxy hysq).2
  have hAy : 0 ≤ A * y := mul_nonneg hA hy.le
  have hmul := mul_le_mul_of_nonneg_left hhalf hAy
  nlinarith

/-- For coordinates in `[-1,1]`, the three Bernoulli-variance terms have
absolute sum at most three. -/
theorem abs_sum_sq_mul_one_sub_sq_le_three
    (v : RLSVector 3) (hv : ∀ j, |v j| ≤ 1) :
    |∑ j, v j ^ 2 * (1 - v j ^ 2)| ≤ 3 := by
  have hTermNonnegative :
      ∀ j : Fin 3, 0 ≤ v j ^ 2 * (1 - v j ^ 2) := by
    intro j
    have hProduct : 0 ≤ (1 - |v j|) * (1 + |v j|) :=
      mul_nonneg (sub_nonneg.mpr (hv j)) (by positivity)
    have hSq : v j ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hSq)
  rw [abs_of_nonneg]
  · calc
      ∑ j, v j ^ 2 * (1 - v j ^ 2) ≤ ∑ _j : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _hj
        have hProduct : 0 ≤ (1 - |v j|) * (1 + |v j|) :=
          mul_nonneg (sub_nonneg.mpr (hv j)) (by positivity)
        have hSq : v j ^ 2 ≤ 1 := by
          rw [← sq_abs]
          nlinarith
        calc
          v j ^ 2 * (1 - v j ^ 2) ≤ v j ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
          _ ≤ 1 := by simpa using hSq
      _ = 3 := by norm_num
  · apply Finset.sum_nonneg
    intro j _hj
    exact hTermNonnegative j

/-- Explicit deterministic envelope for changing the truth argument of the
closed-frame quadratic risk along a local alternative. -/
noncomputable def mixedLocalQuadraticRiskTransferEnvelope
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ) (n : ℕ) : ℝ :=
  let delta := mixedLocalScale N n * H
  let gap := 1 - QubitOracle.blochNormSq theta
  (3 / 4 : ℝ) *
    (6 * delta + 36 * delta / gap + 36 * delta / gap ^ 2)

/-- On the uniform interior-margin event, every orthonormal frame obeys the
explicit local-to-center closed-risk transfer bound. -/
theorem mixedFrameScaledQuadraticRiskClosedForm_localAlternative_abs_sub_le
    (theta h : RLSVector 3) (N : ℕ → ℕ) (H : ℝ) (n : ℕ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : 0 ≤ H) (hInterior : QubitOracle.blochNormSq theta < 1)
    (hBall : MixedLocalDirectionBall H h)
    (hR : MixedFrameOrthonormal R)
    (hMargin :
      (1 - QubitOracle.blochNormSq theta) / 2 ≤
        1 - QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) ∧
      0 < 1 - QubitOracle.blochNormSq
        (mixedLocalAlternative theta N n h)) :
    |mixedFrameScaledQuadraticRiskClosedForm
        (mixedLocalAlternative theta N n h) R -
      mixedFrameScaledQuadraticRiskClosedForm theta R| ≤
      mixedLocalQuadraticRiskTransferEnvelope theta N H n := by
  let localTheta := mixedLocalAlternative theta N n h
  let u := qubitFrameCoordinates R localTheta
  let v := qubitFrameCoordinates R theta
  let delta := mixedLocalScale N n * H
  let localGap := 1 - QubitOracle.blochNormSq localTheta
  let gap := 1 - QubitOracle.blochNormSq theta
  have hGapPos : 0 < gap := by dsimp [gap]; linarith
  have hLocalGapPos : 0 < localGap := by
    simpa [localGap, localTheta] using hMargin.2
  have hHalf : gap / 2 ≤ localGap := by
    simpa [gap, localGap, localTheta] using hMargin.1
  have hLocalInterior : QubitOracle.blochNormSq localTheta < 1 := by
    dsimp [localGap] at hLocalGapPos
    linarith
  have hDelta : 0 ≤ delta := by
    dsimp [delta, mixedLocalScale]
    positivity
  have hu : ∀ j, |u j| ≤ 1 := by
    intro j
    exact qubitFrameCoordinates_abs_le_one_of_interior
      localTheta R hR hLocalInterior j
  have hv : ∀ j, |v j| ≤ 1 := by
    intro j
    exact qubitFrameCoordinates_abs_le_one_of_interior
      theta R hR hInterior j
  have hdiff : ∀ j, |u j - v j| ≤ delta := by
    intro j
    simpa [u, v, localTheta, delta] using
      qubitFrameCoordinates_localAlternative_abs_sub_le
        R hR theta h N H n hH hBall j
  have hFirst :
      |(∑ j, (1 - u j ^ 2)) - ∑ j, (1 - v j ^ 2)| ≤
        6 * delta :=
    abs_sum_one_sub_sq_sub_le_six_mul u v delta hu hv hdiff hDelta
  have hSecond :
      |(∑ j, u j ^ 2 * (1 - u j ^ 2)) -
        ∑ j, v j ^ 2 * (1 - v j ^ 2)| ≤ 18 * delta :=
    abs_sum_sq_mul_one_sub_sq_sub_le_eighteen_mul
      u v delta hu hv hdiff hDelta
  have hCenterSecond :
      |∑ j, v j ^ 2 * (1 - v j ^ 2)| ≤ 3 :=
    abs_sum_sq_mul_one_sub_sq_le_three v hv
  have hGapDifference : |gap - localGap| ≤ 6 * delta := by
    have hFirst' := hFirst
    dsimp [gap, localGap]
    rw [← qubitFrameCoordinates_blochNormSq_of_orthonormal localTheta R hR,
      ← qubitFrameCoordinates_blochNormSq_of_orthonormal theta R hR]
    simpa [u, v, QubitOracle.blochNormSq, abs_sub_comm,
      Fin.sum_univ_succ] using hFirst'
  have hQuotient := abs_div_sub_div_le_of_pos
    (∑ j, u j ^ 2 * (1 - u j ^ 2))
    (∑ j, v j ^ 2 * (1 - v j ^ 2))
    localGap gap (18 * delta) 3 (6 * delta)
    hLocalGapPos hGapPos (by positivity) (by norm_num) (by positivity)
    hSecond hCenterSecond hGapDifference
  have hFirstDenominator :
      (18 * delta) / localGap ≤ (36 * delta) / gap := by
    have h := div_le_two_mul_div_of_half_le
      (18 * delta) localGap gap (by positivity) hGapPos hHalf
    convert h using 1 <;> ring
  have hSecondDenominator :
      (3 * (6 * delta)) / (localGap * gap) ≤
        (36 * delta) / gap ^ 2 := by
    have h := div_mul_le_two_mul_div_sq_of_half_le
      (18 * delta) localGap gap (by positivity) hGapPos hHalf
    convert h using 1 <;> ring
  have hQuotientBound :
      |(∑ j, u j ^ 2 * (1 - u j ^ 2)) / localGap -
        (∑ j, v j ^ 2 * (1 - v j ^ 2)) / gap| ≤
        36 * delta / gap + 36 * delta / gap ^ 2 := by
    exact hQuotient.trans
      (add_le_add hFirstDenominator hSecondDenominator)
  have hThreeFour : (0 : ℝ) ≤ 3 / 4 := by norm_num
  unfold mixedFrameScaledQuadraticRiskClosedForm
    mixedLocalQuadraticRiskTransferEnvelope
  dsimp only
  change
    |(3 / 4 : ℝ) *
        ((∑ j, (1 - u j ^ 2)) +
          (∑ j, u j ^ 2 * (1 - u j ^ 2)) / localGap) -
      (3 / 4 : ℝ) *
        ((∑ j, (1 - v j ^ 2)) +
          (∑ j, v j ^ 2 * (1 - v j ^ 2)) / gap)| ≤
      (3 / 4 : ℝ) *
        (6 * delta + 36 * delta / gap + 36 * delta / gap ^ 2)
  calc
    |(3 / 4 : ℝ) *
        ((∑ j, (1 - u j ^ 2)) +
          (∑ j, u j ^ 2 * (1 - u j ^ 2)) / localGap) -
      (3 / 4 : ℝ) *
        ((∑ j, (1 - v j ^ 2)) +
          (∑ j, v j ^ 2 * (1 - v j ^ 2)) / gap)| =
      (3 / 4 : ℝ) *
        |((∑ j, (1 - u j ^ 2)) - ∑ j, (1 - v j ^ 2)) +
          ((∑ j, u j ^ 2 * (1 - u j ^ 2)) / localGap -
            (∑ j, v j ^ 2 * (1 - v j ^ 2)) / gap)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hThreeFour]
      congr 2
      ring
    _ ≤ (3 / 4 : ℝ) *
        (|(∑ j, (1 - u j ^ 2)) - ∑ j, (1 - v j ^ 2)| +
          |(∑ j, u j ^ 2 * (1 - u j ^ 2)) / localGap -
            (∑ j, v j ^ 2 * (1 - v j ^ 2)) / gap|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hThreeFour
    _ ≤ (3 / 4 : ℝ) *
        (6 * delta + 36 * delta / gap + 36 * delta / gap ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [hFirst, hQuotientBound]) hThreeFour

/-- The deterministic transfer envelope vanishes with the exact-cycle local
scale. -/
theorem mixedExactCycleLocalQuadraticRiskTransferEnvelope_tendsto_zero
    (theta : RLSVector 3) (H : ℝ) :
    Tendsto
      (mixedLocalQuadraticRiskTransferEnvelope theta
        mixedUniformLocalExactCycleN H)
      atTop (nhds 0) := by
  have hDelta : Tendsto
      (fun n => mixedLocalScale mixedUniformLocalExactCycleN n * H)
      atTop (nhds 0) := by
    simpa using mixedUniformLocalExactCycleScale_tendsto_zero.mul_const H
  have hContinuous : Continuous
      (fun delta : ℝ =>
        (3 / 4 : ℝ) *
          (6 * delta +
            36 * delta / (1 - QubitOracle.blochNormSq theta) +
            36 * delta / (1 - QubitOracle.blochNormSq theta) ^ 2)) := by
    fun_prop
  change Tendsto
    (fun n => (3 / 4 : ℝ) *
      (6 * (mixedLocalScale mixedUniformLocalExactCycleN n * H) +
        36 * (mixedLocalScale mixedUniformLocalExactCycleN n * H) /
          (1 - QubitOracle.blochNormSq theta) +
        36 * (mixedLocalScale mixedUniformLocalExactCycleN n * H) /
          (1 - QubitOracle.blochNormSq theta) ^ 2))
    atTop (nhds 0)
  have hComposed : Tendsto
      ((fun delta : ℝ =>
        (3 / 4 : ℝ) *
          (6 * delta +
            36 * delta / (1 - QubitOracle.blochNormSq theta) +
            36 * delta / (1 - QubitOracle.blochNormSq theta) ^ 2)) ∘
        (fun n => mixedLocalScale mixedUniformLocalExactCycleN n * H))
      atTop (nhds 0) := by
    simpa using hContinuous.continuousAt.tendsto.comp hDelta
  refine hComposed.congr' ?_
  exact Eventually.of_forall (fun _n => rfl)

/-- Uniform local-to-center transfer for the exact-cycle conditional
quadratic risk, simultaneously over all bounded directions and all
orthonormal frames. -/
theorem mixedExactCycleLocal_uniform_quadraticRisk_transfer
    (theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H) (hInterior : QubitOracle.blochNormSq theta < 1)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
      ∀ R : Matrix (Fin 3) (Fin 3) ℝ, MixedFrameOrthonormal R →
        |mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n)
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) R -
          mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n) theta R| < epsilon := by
  have hEnvelope : ∀ᶠ n in atTop,
      mixedLocalQuadraticRiskTransferEnvelope theta
        mixedUniformLocalExactCycleN H n < epsilon :=
    (tendsto_order.1
      (mixedExactCycleLocalQuadraticRiskTransferEnvelope_tendsto_zero
        theta H)).2 epsilon hepsilon
  filter_upwards
    [mixedExactCycleLocal_uniform_remainder_margin theta H hInterior,
      hEnvelope] with n hMargin hEnvelopeN
  intro h hBall R hR
  have hLocalInterior :
      QubitOracle.blochNormSq
        (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) < 1 := by
    have := (hMargin h hBall).2
    linarith
  rw [mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
        (mixedUniformLocalExactCycleQFinal_pos n)
        (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
        hLocalInterior R hR,
      mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
        (mixedUniformLocalExactCycleQFinal_pos n) theta hInterior R hR]
  exact lt_of_le_of_lt
    (mixedFrameScaledQuadraticRiskClosedForm_localAlternative_abs_sub_le
      theta h mixedUniformLocalExactCycleN H n R hH hInterior hBall hR
      (hMargin h hBall))
    hEnvelopeN

/-- The actual local-truth conditional quadratic risk is uniformly oracle
optimal on every good pilot outcome.  This closes the previously missing
center-to-local step in the exact-cycle argument. -/
theorem mixedExactCycleLocalPolynomialGood_uniform_localQuadraticRisk
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
          mixedFrameConditionalScaledQuadraticRisk
              (q := mixedUniformLocalExactCycleQFinal n)
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) <
            9 / 4 + epsilon := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hFrozen :=
    mixedExactCycleLocalPolynomialGood_uniform_frozenFrameRisk
      b theta H hH hPositive hInterior hSeed (epsilon / 2) hHalf
  have hTransfer :=
    mixedExactCycleLocal_uniform_quadraticRisk_transfer
      theta H (epsilon / 2) hH hInterior hHalf
  filter_upwards [hFrozen, hTransfer] with n hFrozenN hTransferN
  intro h hBall omega hGood
  let R := mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega)
  have hR : MixedFrameOrthonormal R :=
    mixedPilotSelectedLocalFrame_orthonormal _ _
  have hCenter := hFrozenN h hBall omega hGood
  have hLocal := hTransferN h hBall R hR
  rw [abs_lt] at hCenter hLocal
  dsimp [R] at hCenter hLocal ⊢
  linarith

end

end QubitOracle.Paper
