import QubitOracle.Paper.MixedBuresLocal
import QubitOracle.Paper.PureBuresLocal
import QubitOracle.Paper.OneQubitPureCoordinateCore

/-!
# Deterministic one-qubit Bures-risk remainders

This file deliberately keeps the two pure-state coordinates separate.

* `u` is the north-pole stereographic coordinate.  Its north-pole fidelity is
  `1 / (1 + ‖u‖₂²)`, so its quadratic infidelity has weight `I`.
* `k` is the rank-one Bloch chart coordinate.  Its north-pole fidelity is
  `1 - ‖k‖₂² / 4`, so its quadratic infidelity has weight `(1 / 4) I`.

The exact nonlinear conversion used below is

`k(u) = 2 u / sqrt (1 + ‖u‖₂²)`.

Thus `k = 2u` is only its linearization.  No theorem below feeds a
stereographic `u` directly to `pureQubitBuresWeight`.

For a general nonzero interior mixed-state truth, the raw Bloch-coordinate
Taylor remainder has a cubic term of changing sign.  Consequently the
one-sided premise

`quadratic ≤ physical loss`

used by `mixedQubitPhysicalRisk_tendsto` is not valid in those coordinates.
This file records the correct mixed quadratic form and its positivity, but
intentionally does not assert that false one-sided mixed remainder.
-/

namespace QubitOracle

open scoped BigOperators ENNReal Topology

noncomputable section

/-! ## Interior mixed-state quadratic form -/

/-- A Bloch vector separated from the boundary by an explicit radial margin. -/
def MixedQubitInteriorWithMargin (margin : ℝ) (theta : Fin 3 → ℝ) : Prop :=
  0 < margin ∧ margin ≤ 1 ∧
    blochNormSq theta ≤ (1 - margin) ^ 2

/-- The Bures quadratic form in raw Bloch coordinates at an interior truth. -/
def mixedQubitBuresQuadraticAt
    (theta h : Fin 3 → ℝ) : ℝ :=
  (blochNormSq h +
      (blochDot theta h) ^ 2 / (1 - blochNormSq theta)) / 4

/-- Matrix form of the interior one-qubit Bures weight. -/
def mixedQubitBuresWeightAt
    (theta : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    (1 / 4 : ℝ) *
      ((if i = j then 1 else 0) +
        theta i * theta j / (1 - blochNormSq theta))

/-- A radial margin makes the denominator in the mixed Bures metric positive. -/
theorem mixedQubitInterior_denominator_pos
    {margin : ℝ} {theta : Fin 3 → ℝ}
    (h : MixedQubitInteriorWithMargin margin theta) :
    0 < 1 - blochNormSq theta := by
  rcases h with ⟨hmargin, hmargin_one, htheta⟩
  have hprod : 0 < margin * (2 - margin) :=
    mul_pos hmargin (by linarith)
  have hsquare : (1 - margin) ^ 2 < 1 := by
    nlinarith
  exact sub_pos.mpr (lt_of_le_of_lt htheta hsquare)

/-- The mixed Bures quadratic form is nonnegative at every interior truth. -/
theorem mixedQubitBuresQuadraticAt_nonneg
    {theta h : Fin 3 → ℝ}
    (htheta : blochNormSq theta < 1) :
    0 ≤ mixedQubitBuresQuadraticAt theta h := by
  have hden : 0 ≤ 1 - blochNormSq theta :=
    (sub_pos.mpr htheta).le
  have hnorm : 0 ≤ blochNormSq h := by
    unfold blochNormSq
    positivity
  have hradial :
      0 ≤ (blochDot theta h) ^ 2 / (1 - blochNormSq theta) :=
    div_nonneg (sq_nonneg _) hden
  unfold mixedQubitBuresQuadraticAt
  positivity

/-- The Euclidean part is a lower bound for the mixed quadratic form itself. -/
theorem mixedQubitBuresQuadraticAt_euclidean_lower
    {theta h : Fin 3 → ℝ}
    (htheta : blochNormSq theta < 1) :
    blochNormSq h / 4 ≤ mixedQubitBuresQuadraticAt theta h := by
  have hden : 0 ≤ 1 - blochNormSq theta :=
    (sub_pos.mpr htheta).le
  have hradial :
      0 ≤ (blochDot theta h) ^ 2 / (1 - blochNormSq theta) :=
    div_nonneg (sq_nonneg _) hden
  unfold mixedQubitBuresQuadraticAt
  linarith

/-! ## The exact `u` to `k` pure-coordinate bridge -/

/-- North-pole fidelity of a Bloch vector, in the convention used here. -/
def northPoleBlochFidelity (r : Fin 3 → ℝ) : ℝ :=
  (1 + r 2) / 2

/-- Exact nonlinear conversion from stereographic `u` to rank-one-chart `k`. -/
def stereographicToRankOne (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => 2 * u i / Real.sqrt (1 + directionalQubitNormSq u)

/-- The nonlinear correction to the linear relation `k = 2u`. -/
def stereographicToRankOneRemainder
    (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i =>
    2 * u i *
      ((Real.sqrt (1 + directionalQubitNormSq u))⁻¹ - 1)

private theorem directionalQubitNormSq_nonneg
    (u : Fin 2 → ℝ) :
    0 ≤ directionalQubitNormSq u := by
  unfold directionalQubitNormSq
  positivity

private theorem one_add_directionalQubitNormSq_pos
    (u : Fin 2 → ℝ) :
    0 < 1 + directionalQubitNormSq u := by
  have hu := directionalQubitNormSq_nonneg u
  linarith

/-- The exact conversion is its linear part plus an explicit nonlinear term. -/
theorem stereographicToRankOne_eq_linear_add_remainder
    (u : Fin 2 → ℝ) (i : Fin 2) :
    stereographicToRankOne u i =
      2 * u i + stereographicToRankOneRemainder u i := by
  simp [stereographicToRankOne, stereographicToRankOneRemainder,
    div_eq_mul_inv]
  ring

/-- Squared-radius identity for the exact nonlinear coordinate conversion. -/
theorem finTwoQubitRadiusSq_stereographicToRankOne
    (u : Fin 2 → ℝ) :
    finTwoQubitRadiusSq (stereographicToRankOne u) =
      4 * directionalQubitNormSq u /
        (1 + directionalQubitNormSq u) := by
  have hpos := one_add_directionalQubitNormSq_pos u
  have hsqrt_ne :
      Real.sqrt (1 + directionalQubitNormSq u) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsqrt_sq :
      (Real.sqrt (1 + directionalQubitNormSq u)) ^ 2 =
        1 + directionalQubitNormSq u :=
    Real.sq_sqrt hpos.le
  simp [directionalQubitNormSq] at hsqrt_sq
  simp [finTwoQubitRadiusSq, directionalQubitNormSq,
    stereographicToRankOne, Fin.sum_univ_succ]
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]
  ring

/-- The rank-one chart has exact north-pole fidelity `1 - ‖k‖²/4`. -/
theorem northPoleBlochFidelity_pureQubitRankOneBlochChart
    (k : Fin 2 → ℝ) :
    northPoleBlochFidelity (pureQubitRankOneBlochChart k) =
      1 - finTwoQubitRadiusSq k / 4 := by
  simp [northPoleBlochFidelity, pureQubitRankOneBlochChart,
    finTwoQubitRadiusSq, Fin.sum_univ_succ]
  ring

/-- The stereographic chart has exact north-pole fidelity `1/(1+‖u‖²)`. -/
theorem northPoleBlochFidelity_directionalNorthPoleStereographicChart
    (u : Fin 2 → ℝ) :
    northPoleBlochFidelity (directionalNorthPoleStereographicChart u) =
      1 / (1 + directionalQubitNormSq u) := by
  have hne : 1 + directionalQubitNormSq u ≠ 0 :=
    ne_of_gt (one_add_directionalQubitNormSq_pos u)
  simp [northPoleBlochFidelity,
    directionalNorthPoleStereographicChart,
    directionalStereographicDenominator]
  field_simp [hne]
  ring

/-- At the level of fidelity, the nonlinear `u` to `k` conversion is exact. -/
theorem northPoleFidelity_rankOne_after_stereographicToRankOne
    (u : Fin 2 → ℝ) :
    northPoleBlochFidelity
        (pureQubitRankOneBlochChart (stereographicToRankOne u)) =
      1 / (1 + directionalQubitNormSq u) := by
  rw [northPoleBlochFidelity_pureQubitRankOneBlochChart,
    finTwoQubitRadiusSq_stereographicToRankOne]
  have hne : 1 + directionalQubitNormSq u ≠ 0 :=
    ne_of_gt (one_add_directionalQubitNormSq_pos u)
  field_simp [hne]
  ring

/-- Infidelity in the stereographic coordinate; its quadratic weight is `I`. -/
def pureStereographicInfidelity (u : Fin 2 → ℝ) : ℝ :=
  1 - northPoleBlochFidelity
    (directionalNorthPoleStereographicChart u)

/-- Exact stereographic infidelity formula. -/
theorem pureStereographicInfidelity_eq
    (u : Fin 2 → ℝ) :
    pureStereographicInfidelity u =
      directionalQubitNormSq u /
        (1 + directionalQubitNormSq u) := by
  rw [pureStereographicInfidelity,
    northPoleBlochFidelity_directionalNorthPoleStereographicChart]
  have hne : 1 + directionalQubitNormSq u ≠ 0 :=
    ne_of_gt (one_add_directionalQubitNormSq_pos u)
  field_simp [hne]
  ring

/-- The stereographic quadratic discrepancy is nonnegative and fourth order. -/
theorem pureStereographicInfidelity_quadratic_discrepancy
    (u : Fin 2 → ℝ) :
    0 ≤ directionalQubitNormSq u - pureStereographicInfidelity u ∧
    directionalQubitNormSq u - pureStereographicInfidelity u =
      (directionalQubitNormSq u) ^ 2 /
        (1 + directionalQubitNormSq u) := by
  rw [pureStereographicInfidelity_eq]
  have hnorm := directionalQubitNormSq_nonneg u
  have hden := one_add_directionalQubitNormSq_pos u
  have heq :
      directionalQubitNormSq u -
          directionalQubitNormSq u / (1 + directionalQubitNormSq u) =
        directionalQubitNormSq u ^ 2 /
          (1 + directionalQubitNormSq u) := by
    field_simp [ne_of_gt hden]
    ring
  constructor
  · rw [heq]
    exact div_nonneg (sq_nonneg _) hden.le
  · exact heq

/-- Infidelity in the rank-one chart; its quadratic weight is `(1/4) I`. -/
def pureRankOneInfidelity (k : Fin 2 → ℝ) : ℝ :=
  1 - northPoleBlochFidelity (pureQubitRankOneBlochChart k)

/-- Rank-one-chart infidelity is exactly `‖k‖²/4`. -/
theorem pureRankOneInfidelity_eq
    (k : Fin 2 → ℝ) :
    pureRankOneInfidelity k = finTwoQubitRadiusSq k / 4 := by
  rw [pureRankOneInfidelity,
    northPoleBlochFidelity_pureQubitRankOneBlochChart]
  ring

/-! ## Rank-one `k`-chart Bures remainder at root-`N` scale -/

/-- The quadratic pure-state loss in the rank-one `k` chart. -/
def pureRankOneQuadraticLossReal (k : Fin 2 → ℝ) : ℝ :=
  finTwoQubitRadiusSq k / 4

/-- Root-`N` rescaled Bures loss in the rank-one chart. -/
def pureRankOneRootNBuresLossReal
    (N : ℝ) (k : Fin 2 → ℝ) : ℝ :=
  N * buresChartLoss
    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k)

/-- Root-`N` rescaled infidelity in the rank-one chart. -/
def pureRankOneRootNInfidelityLossReal
    (N : ℝ) (k : Fin 2 → ℝ) : ℝ :=
  N * traceChartLoss
    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k)

private theorem rootScale_sq
    {N : ℝ} (hN : 0 < N) :
    ((Real.sqrt N)⁻¹) ^ 2 = N⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hN.le]

private theorem rootScale_rankOne_domain
    {N : ℝ} {k : Fin 2 → ℝ}
    (hN : 0 < N)
    (hradius : finTwoQubitRadiusSq k ≤ 4 * N) :
    ((Real.sqrt N)⁻¹) ^ 2 *
        tangentRadiusSq (finTwoAsQubitTangent k) ≤ 4 := by
  rw [rootScale_sq hN, tangentRadiusSq_finTwoAsQubitTangent]
  have hdiv : finTwoQubitRadiusSq k / N ≤ 4 :=
    (div_le_iff₀ hN).2 hradius
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- Root-`N` rank-one infidelity equals its `(1/4)I` quadratic form exactly. -/
theorem pureRankOneRootNInfidelityLossReal_eq
    {N : ℝ} (hN : 0 < N) (k : Fin 2 → ℝ)
    (hradius : finTwoQubitRadiusSq k ≤ 4 * N) :
    pureRankOneRootNInfidelityLossReal N k =
      pureRankOneQuadraticLossReal k := by
  have hdomain := rootScale_rankOne_domain hN hradius
  have hscaled :
      tangentRadiusSq
          ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) ≤ 4 := by
    rw [Paper.tangentRadiusSq_smul]
    exact hdomain
  have hNne : N ≠ 0 := ne_of_gt hN
  unfold pureRankOneRootNInfidelityLossReal pureRankOneQuadraticLossReal
  rw [traceChartLoss_eq _ hscaled, Paper.tangentRadiusSq_smul,
    tangentRadiusSq_finTwoAsQubitTangent, rootScale_sq hN]
  field_simp [hNne]

/-- Exact-sign and exact-constant Bures remainder in the rank-one `k` chart.

The upper constant is `1/16`, and the vanishing rate is `1/N` times the
fourth envelope `(‖k‖²)²`.
-/
theorem pureRankOneRootNBuresLossReal_remainder_bounds
    {N : ℝ} {k : Fin 2 → ℝ}
    (hN : 0 < N)
    (hradius : finTwoQubitRadiusSq k ≤ 4 * N) :
    0 ≤ pureRankOneRootNBuresLossReal N k -
        pureRankOneQuadraticLossReal k ∧
    pureRankOneRootNBuresLossReal N k -
        pureRankOneQuadraticLossReal k ≤
      (finTwoQubitRadiusSq k) ^ 2 / (16 * N) := by
  have hdomain := rootScale_rankOne_domain hN hradius
  have hb := Paper.buresChartLoss_smul_remainder_bounds
    (Real.sqrt N)⁻¹ (finTwoAsQubitTangent k) hdomain
  rw [tangentRadiusSq_finTwoAsQubitTangent] at hb
  have hNne : N ≠ 0 := ne_of_gt hN
  have hNa2 : N * ((Real.sqrt N)⁻¹) ^ 2 = 1 := by
    rw [rootScale_sq hN]
    field_simp [hNne]
  have hNa4 : N * ((Real.sqrt N)⁻¹) ^ 4 = N⁻¹ := by
    rw [show ((Real.sqrt N)⁻¹) ^ 4 =
      (((Real.sqrt N)⁻¹) ^ 2) ^ 2 by ring, rootScale_sq hN]
    field_simp [hNne]
  constructor
  · calc
      pureRankOneRootNBuresLossReal N k -
          pureRankOneQuadraticLossReal k =
        N * (buresChartLoss
          ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
          ((Real.sqrt N)⁻¹) ^ 2 *
            finTwoQubitRadiusSq k / 4) := by
              unfold pureRankOneRootNBuresLossReal
                pureRankOneQuadraticLossReal
              calc
                N * buresChartLoss
                    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    finTwoQubitRadiusSq k / 4 =
                  N * buresChartLoss
                      ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    (N * ((Real.sqrt N)⁻¹) ^ 2) *
                      finTwoQubitRadiusSq k / 4 := by
                        rw [hNa2]
                        ring
                _ = N * (buresChartLoss
                    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    ((Real.sqrt N)⁻¹) ^ 2 *
                      finTwoQubitRadiusSq k / 4) := by ring
      _ ≥ 0 := mul_nonneg hN.le hb.1
  · calc
      pureRankOneRootNBuresLossReal N k -
          pureRankOneQuadraticLossReal k =
        N * (buresChartLoss
          ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
          ((Real.sqrt N)⁻¹) ^ 2 *
            finTwoQubitRadiusSq k / 4) := by
              unfold pureRankOneRootNBuresLossReal
                pureRankOneQuadraticLossReal
              calc
                N * buresChartLoss
                    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    finTwoQubitRadiusSq k / 4 =
                  N * buresChartLoss
                      ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    (N * ((Real.sqrt N)⁻¹) ^ 2) *
                      finTwoQubitRadiusSq k / 4 := by
                        rw [hNa2]
                        ring
                _ = N * (buresChartLoss
                    ((Real.sqrt N)⁻¹ • finTwoAsQubitTangent k) -
                    ((Real.sqrt N)⁻¹) ^ 2 *
                      finTwoQubitRadiusSq k / 4) := by ring
      _ ≤ N * (((Real.sqrt N)⁻¹) ^ 4 *
          (finTwoQubitRadiusSq k) ^ 2 / 16) :=
        mul_le_mul_of_nonneg_left hb.2 hN.le
      _ = (finTwoQubitRadiusSq k) ^ 2 / (16 * N) := by
        rw [show N * (((Real.sqrt N)⁻¹) ^ 4 *
          (finTwoQubitRadiusSq k) ^ 2 / 16) =
          (N * ((Real.sqrt N)⁻¹) ^ 4) *
            (finTwoQubitRadiusSq k) ^ 2 / 16 by ring, hNa4]
        field_simp [hNne]

/-- The deterministic lower/upper premises needed by the pure risk transfer. -/
theorem pureRankOneRootNBuresLossReal_quadratic_bounds
    {N : ℝ} {k : Fin 2 → ℝ}
    (hN : 0 < N)
    (hradius : finTwoQubitRadiusSq k ≤ 4 * N) :
    pureRankOneQuadraticLossReal k ≤
        pureRankOneRootNBuresLossReal N k ∧
    pureRankOneRootNBuresLossReal N k ≤
      pureRankOneQuadraticLossReal k +
        (finTwoQubitRadiusSq k) ^ 2 / (16 * N) := by
  rcases pureRankOneRootNBuresLossReal_remainder_bounds hN hradius with
    ⟨hlower, hupper⟩
  constructor <;> linarith

/-- A convenient ENNReal rate; it tends to zero and is looser than the sharp
`1/(16n)` coefficient proved above. -/
def pureRankOneBuresRemainderRate (n : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞)⁻¹

/-- The risk-transfer rate vanishes. -/
theorem pureRankOneBuresRemainderRate_tendsto_zero :
    Filter.Tendsto pureRankOneBuresRemainderRate Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹)
    Filter.atTop (𝓝 0)
  exact ENNReal.tendsto_inv_nat_nhds_zero

/-!
The pure deterministic endpoint above is closed in the rank-one `k` chart.
Combining it with `pureQubitPhysicalRisk_tendsto` leaves only distributional
convergence and a uniform fourth-moment input, provided that those stochastic
inputs are stated for `k` itself.

A stereographic LAN stated for `u` cannot be substituted directly: it first
needs a delta-method result for `stereographicToRankOne`, whose exact nonlinear
remainder is isolated above.  Likewise, a general raw-Bloch mixed endpoint
needs a two-sided absolute Taylor-remainder transfer theorem rather than the
one-sided transfer currently exposed by `mixedQubitPhysicalRisk_tendsto`.
No closure theorem is asserted across either missing bridge.
-/

end

end QubitOracle
