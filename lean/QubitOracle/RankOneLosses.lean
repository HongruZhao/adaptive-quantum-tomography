import QubitOracle.TwoBasis

/-!
# Rank-one local loss geometry

This file defines the full normalized local chart around the reference ray and
derives the exact fidelity formula.  It then identifies the local quadratic
weights for squared Frobenius loss, squared trace distance, and Bures loss.
The Bures statement includes an exact nonnegative remainder and a uniform
fourth-order bound on the chart domain.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

/-- Squared Euclidean radius in the `2n` real tangent coordinates. -/
def tangentRadiusSq {n : ℕ} (h : TangentIndex n → ℝ) : ℝ :=
  ∑ x, h x ^ 2

/-- Quadratic form associated with a real tangent-space matrix. -/
def tangentQuadratic {n : ℕ}
    (G : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (h : TangentIndex n → ℝ) : ℝ :=
  dotProduct h (G.mulVec h)

/-- A scalar identity matrix represents the corresponding multiple of the
squared tangent radius. -/
theorem tangentQuadratic_smul_identity {n : ℕ} (g : ℝ)
    (h : TangentIndex n → ℝ) :
    tangentQuadratic (g • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h =
      g * tangentRadiusSq h := by
  change (∑ i, h i * ((g • (1 : Matrix (TangentIndex n)
    (TangentIndex n) ℝ)).mulVec h) i) = g * ∑ i, h i ^ 2
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply]
  ring

/-- Full normalized local chart in adapted coordinates. -/
def chartState {n : ℕ} (h : TangentIndex n → ℝ) : Fin (n + 1) → ℂ :=
  Fin.cases (Real.sqrt (1 - tangentRadiusSq h / 4) : ℂ) fun a =>
    ⟨h (Sum.inl a) / 2, h (Sum.inr a) / 2⟩

theorem tangentRadiusSq_nonneg {n : ℕ} (h : TangentIndex n → ℝ) :
    0 ≤ tangentRadiusSq h := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The full chart is normalized whenever its squared tangent radius is at
most four. -/
theorem chartState_normalized {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    (∑ i, Complex.normSq (chartState h i)) = 1 := by
  have hnonneg : 0 ≤ 1 - tangentRadiusSq h / 4 := by linarith
  have hradial : (Real.sqrt (1 - tangentRadiusSq h / 4)) ^ 2 =
      1 - tangentRadiusSq h / 4 := Real.sq_sqrt hnonneg
  have htail :
      (∑ i : Fin n, (
        (h (Sum.inl i : TangentIndex n) / 2) *
          (h (Sum.inl i : TangentIndex n) / 2) +
        (h (Sum.inr i : TangentIndex n) / 2) *
          (h (Sum.inr i : TangentIndex n) / 2))) =
        tangentRadiusSq h / 4 := by
    rw [Finset.sum_add_distrib]
    calc
      (∑ i : Fin n, h (Sum.inl i : TangentIndex n) / 2 *
          (h (Sum.inl i : TangentIndex n) / 2)) +
          ∑ i : Fin n, h (Sum.inr i : TangentIndex n) / 2 *
            (h (Sum.inr i : TangentIndex n) / 2) =
          (∑ i : Fin n, h (Sum.inl i : TangentIndex n) ^ 2 / 4) +
            ∑ i : Fin n, h (Sum.inr i : TangentIndex n) ^ 2 / 4 := by
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
      _ = (∑ i : Fin n, h (Sum.inl i : TangentIndex n) ^ 2) / 4 +
          (∑ i : Fin n, h (Sum.inr i : TangentIndex n) ^ 2) / 4 := by
        rw [Finset.sum_div, Finset.sum_div]
      _ = tangentRadiusSq h / 4 := by
        simp [tangentRadiusSq, Fintype.sum_sum_type]
        ring
  rw [Fin.sum_univ_succ]
  simp only [chartState, Fin.cases_zero, Fin.cases_succ, Complex.normSq_ofReal,
    Complex.normSq_mk]
  rw [← pow_two, hradial]
  rw [htail]
  ring

/-- Fidelity with the reference ray in the adapted chart. -/
def chartFidelity {n : ℕ} (h : TangentIndex n → ℝ) : ℝ :=
  Complex.normSq (chartState h 0)

/-- Exact chart fidelity. -/
theorem chartFidelity_eq {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    chartFidelity h = 1 - tangentRadiusSq h / 4 := by
  have hnonneg : 0 ≤ 1 - tangentRadiusSq h / 4 := by
    linarith [tangentRadiusSq_nonneg h]
  simp only [chartFidelity, chartState, Fin.cases_zero, Complex.normSq_ofReal]
  rw [← pow_two, Real.sq_sqrt hnonneg]

/-- Squared Frobenius loss between rank-one density matrices, expressed via
fidelity. -/
def frobeniusChartLoss {n : ℕ} (h : TangentIndex n → ℝ) : ℝ :=
  2 * (1 - chartFidelity h)

/-- Squared trace distance between rank-one density matrices. -/
def traceChartLoss {n : ℕ} (h : TangentIndex n → ℝ) : ℝ :=
  1 - chartFidelity h

/-- Squared Bures distance in the convention `2 (1 - sqrt F)`. -/
def buresChartLoss {n : ℕ} (h : TangentIndex n → ℝ) : ℝ :=
  2 * (1 - Real.sqrt (chartFidelity h))

theorem frobeniusChartLoss_eq {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    frobeniusChartLoss h = tangentRadiusSq h / 2 := by
  rw [frobeniusChartLoss, chartFidelity_eq h hchart]
  ring

theorem traceChartLoss_eq {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    traceChartLoss h = tangentRadiusSq h / 4 := by
  rw [traceChartLoss, chartFidelity_eq h hchart]
  ring

/-- The exact Frobenius local weight is `(1/2) I`. -/
theorem frobeniusChartLoss_eq_quadratic {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    frobeniusChartLoss h = tangentQuadratic
      ((1 / 2 : ℝ) • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h := by
  rw [frobeniusChartLoss_eq h hchart, tangentQuadratic_smul_identity]
  ring

/-- The exact squared-trace-distance local weight is `(1/4) I`. -/
theorem traceChartLoss_eq_quadratic {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    traceChartLoss h = tangentQuadratic
      ((1 / 4 : ℝ) • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h := by
  rw [traceChartLoss_eq h hchart, tangentQuadratic_smul_identity]
  ring

theorem buresChartLoss_eq {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    buresChartLoss h =
      2 * (1 - Real.sqrt (1 - tangentRadiusSq h / 4)) := by
  rw [buresChartLoss, chartFidelity_eq h hchart]

/-- Exact decomposition of Bures loss into its quadratic term and a
nonnegative remainder. -/
theorem buresChartLoss_exact_remainder {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    buresChartLoss h = tangentRadiusSq h / 4 +
      (tangentRadiusSq h) ^ 2 /
        (16 * (1 + Real.sqrt (1 - tangentRadiusSq h / 4)) ^ 2) := by
  rw [buresChartLoss_eq h hchart]
  let s : ℝ := tangentRadiusSq h
  let r : ℝ := Real.sqrt (1 - s / 4)
  change 2 * (1 - r) = s / 4 + s ^ 2 / (16 * (1 + r) ^ 2)
  have hnonneg : 0 ≤ 1 - s / 4 := by
    linarith [tangentRadiusSq_nonneg h]
  have hsqrt_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hsqrt_sq : r ^ 2 = 1 - s / 4 := Real.sq_sqrt hnonneg
  have hden : 1 + r ≠ 0 := by
    positivity
  field_simp [hden]
  nlinarith [hsqrt_sq]

/-- The Bures remainder lies between zero and `||h||^4 / 16`. -/
theorem buresChartLoss_remainder_bounds {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    0 ≤ buresChartLoss h - tangentRadiusSq h / 4 ∧
      buresChartLoss h - tangentRadiusSq h / 4 ≤
        (tangentRadiusSq h) ^ 2 / 16 := by
  have hremainder :
      buresChartLoss h - tangentRadiusSq h / 4 =
        (tangentRadiusSq h) ^ 2 /
          (16 * (1 + Real.sqrt (1 - tangentRadiusSq h / 4)) ^ 2) := by
    rw [buresChartLoss_exact_remainder h hchart]
    ring
  rw [hremainder]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - tangentRadiusSq h / 4) :=
    Real.sqrt_nonneg _
  have hden_pos :
      0 < 16 * (1 + Real.sqrt (1 - tangentRadiusSq h / 4)) ^ 2 := by
    positivity
  constructor
  · exact div_nonneg (sq_nonneg _) hden_pos.le
  · have hden : 1 ≤ (1 + Real.sqrt (1 - tangentRadiusSq h / 4)) ^ 2 := by
      nlinarith
    have hsq : 0 ≤ (tangentRadiusSq h) ^ 2 := sq_nonneg _
    apply div_le_div_of_nonneg_left hsq (by norm_num)
    nlinarith

/-- Bures loss has quadratic weight `(1/4) I`, with a nonnegative remainder
bounded by `||h||^4 / 16`. -/
theorem buresChartLoss_quadratic_remainder_bounds {n : ℕ}
    (h : TangentIndex n → ℝ) (hchart : tangentRadiusSq h ≤ 4) :
    0 ≤ buresChartLoss h - tangentQuadratic
      ((1 / 4 : ℝ) • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h ∧
    buresChartLoss h - tangentQuadratic
      ((1 / 4 : ℝ) • (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h ≤
        (tangentRadiusSq h) ^ 2 / 16 := by
  rw [tangentQuadratic_smul_identity]
  simpa [div_eq_mul_inv, mul_comm] using
    buresChartLoss_remainder_bounds h hchart

end


end QubitOracle
