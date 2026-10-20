import QubitOracle.Paper.PureMultilevelDeterministicGeometryClosed
import QubitOracle.RankOneLosses

namespace QubitOracle.Paper
namespace PureMultilevelProjectorGeometry

open scoped BigOperators

noncomputable section

open PureMultilevelDeterministicGeometry

/-- Phase-invariant real tangent coordinates extracted from the first column
of the estimated rank-one density matrix. -/
def pureProjectorTangentCoordinate {d : ℕ}
    (psi : Fin (d + 1) → ℂ) : QubitOracle.TangentIndex d → ℝ
  | Sum.inl k => 2 * (rankOneDensity psi k.succ 0).re
  | Sum.inr k => 2 * (rankOneDensity psi k.succ 0).im

/-- Entrywise squared Frobenius distance between two rank-one density
matrices. -/
def pureRankOneDensityFrobeniusSq {d : ℕ}
    (psi phi : Fin (d + 1) → ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq
    (rankOneDensity psi i j - rankOneDensity phi i j)

theorem rankOneDensity_normSq_sum
    {d : ℕ} (psi : Fin (d + 1) → ℂ) :
    (∑ i, ∑ j, Complex.normSq (rankOneDensity psi i j)) =
      pureStateNormSq psi ^ 2 := by
  simp only [rankOneDensity, Complex.normSq_mul]
  rw [← Finset.sum_mul_sum]
  have hConj :
      (∑ j, Complex.normSq (star (psi j))) =
        ∑ j, Complex.normSq (psi j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Complex.normSq_conj _
  rw [hConj]
  unfold pureStateNormSq
  ring

theorem rankOneDensity_cross_re_sum_eq_fidelity
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    (∑ i, ∑ j,
      (rankOneDensity psi i j *
        (starRingEnd ℂ) (rankOneDensity phi i j)).re) =
      pureMultilevelFidelity psi phi := by
  have hComplex :
      (∑ i, ∑ j,
        rankOneDensity psi i j *
          (starRingEnd ℂ) (rankOneDensity phi i j)) =
        ((pureMultilevelFidelity psi phi : ℝ) : ℂ) := by
    calc
      (∑ i, ∑ j,
          rankOneDensity psi i j * star (rankOneDensity phi i j)) =
        (∑ i, psi i * star (phi i)) *
          (∑ j, star (psi j) * phi j) := by
            rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            simp only [rankOneDensity]
            rw [star_mul, star_star]
            ring
      _ = star (basisBornAmplitude psi phi) *
          basisBornAmplitude psi phi := by
            simp [basisBornAmplitude, mul_comm]
      _ = ((pureMultilevelFidelity psi phi : ℝ) : ℂ) := by
            unfold pureMultilevelFidelity basisBornProbability
            exact (Complex.normSq_eq_conj_mul_self).symm
  have hReal := congrArg Complex.re hComplex
  simpa using hReal

/-- For normalized pure vectors, entrywise density-matrix Frobenius loss is
exactly twice ordinary infidelity. -/
theorem pureRankOneDensityFrobeniusSq_eq_two_infidelity
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    pureRankOneDensityFrobeniusSq psi phi =
      2 * pureMultilevelInfidelity psi phi := by
  unfold pureRankOneDensityFrobeniusSq
  calc
    (∑ i, ∑ j, Complex.normSq
        (rankOneDensity psi i j - rankOneDensity phi i j)) =
      (∑ i, ∑ j, Complex.normSq (rankOneDensity psi i j)) +
      (∑ i, ∑ j, Complex.normSq (rankOneDensity phi i j)) -
      2 * (∑ i, ∑ j, (rankOneDensity psi i j *
        (starRingEnd ℂ) (rankOneDensity phi i j)).re) := by
          simp_rw [Complex.normSq_sub]
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
    _ = 2 * pureMultilevelInfidelity psi phi := by
      rw [rankOneDensity_normSq_sum,
        rankOneDensity_normSq_sum,
        rankOneDensity_cross_re_sum_eq_fidelity,
        hPsi, hPhi]
      unfold pureMultilevelInfidelity
      ring

theorem pureRankOneDensityFrobeniusSq_nonnegative
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    0 ≤ pureRankOneDensityFrobeniusSq psi phi := by
  unfold pureRankOneDensityFrobeniusSq
  exact Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _

theorem normalized_pureMultilevelFidelity_le_one
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    pureMultilevelFidelity psi phi ≤ 1 := by
  have hFrob := pureRankOneDensityFrobeniusSq_nonnegative psi phi
  rw [pureRankOneDensityFrobeniusSq_eq_two_infidelity
    psi phi hPsi hPhi] at hFrob
  unfold pureMultilevelInfidelity at hFrob
  linarith

/-- For normalized pure states, squared Bures distance is at least one half
of squared density-matrix Frobenius distance. -/
theorem normalized_frobenius_le_two_bures
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    pureRankOneDensityFrobeniusSq psi phi ≤
      2 * pureMultilevelBuresSq psi phi := by
  have hFidelityNonnegative :
      0 ≤ pureMultilevelFidelity psi phi := by
    unfold pureMultilevelFidelity basisBornProbability
    exact Complex.normSq_nonneg _
  have hFidelityLe :=
    normalized_pureMultilevelFidelity_le_one psi phi hPsi hPhi
  have hRootNonnegative :
      0 ≤ pureMultilevelRootFidelity psi phi := by
    unfold pureMultilevelRootFidelity
    exact Real.sqrt_nonneg _
  have hRootSquare :
      pureMultilevelRootFidelity psi phi ^ 2 =
        pureMultilevelFidelity psi phi := by
    unfold pureMultilevelRootFidelity
    exact Real.sq_sqrt hFidelityNonnegative
  have hRootLe : pureMultilevelRootFidelity psi phi ≤ 1 := by
    nlinarith
  rw [pureRankOneDensityFrobeniusSq_eq_two_infidelity
    psi phi hPsi hPhi]
  unfold pureMultilevelInfidelity pureMultilevelBuresSq
  nlinarith

theorem pureProjectorTangentCoordinate_sub_radius
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    QubitOracle.tangentRadiusSq (fun a =>
      pureProjectorTangentCoordinate psi a -
        pureProjectorTangentCoordinate phi a) =
      4 * ∑ k : Fin d, Complex.normSq
        (rankOneDensity psi k.succ 0 - rankOneDensity phi k.succ 0) := by
  unfold QubitOracle.tangentRadiusSq
  rw [Fintype.sum_sum_type]
  simp only [pureProjectorTangentCoordinate]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem rankOneDensity_sub_normSq_transpose
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (i j : Fin (d + 1)) :
    Complex.normSq
        (rankOneDensity psi i j - rankOneDensity phi i j) =
      Complex.normSq
        (rankOneDensity psi j i - rankOneDensity phi j i) := by
  rw [rankOneDensity_hermitian_symmetry psi i j,
    rankOneDensity_hermitian_symmetry phi i j]
  calc
    Complex.normSq
        (star (rankOneDensity psi j i) - star (rankOneDensity phi j i)) =
      Complex.normSq
        (star (rankOneDensity psi j i - rankOneDensity phi j i)) := by
          congr 1
          simp
    _ = Complex.normSq
        (rankOneDensity psi j i - rankOneDensity phi j i) :=
      Complex.normSq_conj _

/-- The full density-matrix Frobenius loss controls the phase-invariant
projector-coordinate error in every finite dimension. -/
theorem half_projectorCoordinateError_le_frobenius
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    (1 / 2 : ℝ) * QubitOracle.tangentRadiusSq (fun a =>
      pureProjectorTangentCoordinate psi a -
        pureProjectorTangentCoordinate phi a) ≤
      pureRankOneDensityFrobeniusSq psi phi := by
  let off : ℝ := ∑ k : Fin d, Complex.normSq
    (rankOneDensity psi k.succ 0 - rankOneDensity phi k.succ 0)
  have hRow :
      off ≤ ∑ j : Fin (d + 1), Complex.normSq
        (rankOneDensity psi 0 j - rankOneDensity phi 0 j) := by
    rw [Fin.sum_univ_succ]
    have hEq :
        (∑ k : Fin d, Complex.normSq
          (rankOneDensity psi 0 k.succ - rankOneDensity phi 0 k.succ)) =
          off := by
      unfold off
      apply Finset.sum_congr rfl
      intro k hk
      exact rankOneDensity_sub_normSq_transpose psi phi 0 k.succ
    rw [hEq]
    exact le_add_of_nonneg_left (Complex.normSq_nonneg _)
  have hTail :
      off ≤ ∑ i : Fin d, ∑ j : Fin (d + 1), Complex.normSq
        (rankOneDensity psi i.succ j - rankOneDensity phi i.succ j) := by
    unfold off
    apply Finset.sum_le_sum
    intro i hi
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun j hj => Complex.normSq_nonneg _)
  rw [pureProjectorTangentCoordinate_sub_radius]
  unfold pureRankOneDensityFrobeniusSq
  rw [Fin.sum_univ_succ]
  nlinarith

/-- Global normalized-state comparison needed for squared-Bures minimax:
one quarter of phase-invariant projector-coordinate error is bounded by the
physical squared Bures distance. -/
theorem quarter_projectorCoordinateError_le_bures
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    (1 / 4 : ℝ) * QubitOracle.tangentRadiusSq (fun a =>
      pureProjectorTangentCoordinate psi a -
        pureProjectorTangentCoordinate phi a) ≤
      pureMultilevelBuresSq psi phi := by
  have hCoordinate :=
    half_projectorCoordinateError_le_frobenius psi phi
  have hBures := normalized_frobenius_le_two_bures
    psi phi hPsi hPhi
  nlinarith

end

end PureMultilevelProjectorGeometry
end QubitOracle.Paper
