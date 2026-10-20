import Mathlib

/-!
# Population-gap Davis--Kahan variant

This file records a source-faithful interface to Theorem 2 of

Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan
theorem for statisticians*, Biometrika 102 (2015), 315--323.

Source: https://personal.lse.ac.uk/wangt60/publication/DKvariant.pdf

The only eigengap below is computed from the ordered population eigenvalues.
The selected columns form a nonempty proper block of consecutive eigenvectors;
the full-space case omitted by this representation is trivial because both
subspaces are the whole ambient space.
-/

namespace QubitOracle.Paper.SourceFaithfulDavisKahan

open scoped BigOperators

noncomputable section

/-- Algebraically largest eigenvalue of a nonempty real self-adjoint matrix. -/
def largestEigenvalue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if hA : A.IsHermitian then
    if hd : 0 < d then hA.eigenvalues ⟨0, hd⟩ else 0
  else 0

/-- Spectral/operator norm of a real matrix. -/
def matrixOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (largestEigenvalue (A.transpose * A))

/-- Frobenius norm written entrywise. -/
def matrixFrobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

/-- Zero-based index of the `j`th member of the consecutive block beginning
at `r`. -/
def blockIndex {p q : ℕ} (r : ℕ) (hfit : r + q ≤ p) (j : Fin q) : Fin p :=
  ⟨r + j, by omega⟩

/-- Left population boundary gap, absent when the block starts at zero. -/
def leftBoundaryGap {p q : ℕ}
    (lambda : Fin p → ℝ) (r : ℕ) (hq : 0 < q) (hfit : r + q ≤ p) : Option ℝ :=
  if hr : 0 < r then
    some (lambda ⟨r - 1, by omega⟩ - lambda ⟨r, by omega⟩)
  else none

/-- Right population boundary gap, absent when the block ends at `p`. -/
def rightBoundaryGap {p q : ℕ}
    (lambda : Fin p → ℝ) (r : ℕ) (hq : 0 < q) (hfit : r + q ≤ p) : Option ℝ :=
  if hright : r + q < p then
    some (lambda ⟨r + q - 1, by omega⟩ - lambda ⟨r + q, hright⟩)
  else none

/-- Minimum of the finite population boundary gaps.  A value of zero is used
only if both boundaries are absent; the source theorem structure below rules
that full-space case out. -/
def finiteBoundaryMinimum : Option ℝ → Option ℝ → ℝ
  | some a, some b => min a b
  | some a, none => a
  | none, some b => b
  | none, none => 0

/-- Concrete data in Yu--Wang--Samworth Theorem 2.  `r` is zero-based and the
block has `q` consecutive eigenvectors. -/
structure PopulationEigenspaceBlock (p q : ℕ) where
  r : ℕ
  blockNonempty : 0 < q
  blockFits : r + q ≤ p
  blockProper : 0 < r ∨ r + q < p
  population : Matrix (Fin p) (Fin p) ℝ
  sample : Matrix (Fin p) (Fin p) ℝ
  populationEigenvalues : Fin p → ℝ
  sampleEigenvalues : Fin p → ℝ
  populationVectors : Matrix (Fin p) (Fin q) ℝ
  sampleVectors : Matrix (Fin p) (Fin q) ℝ
  populationSymmetric : population.IsHermitian
  sampleSymmetric : sample.IsHermitian
  populationOrdered : Antitone populationEigenvalues
  sampleOrdered : Antitone sampleEigenvalues
  populationOrthonormal : populationVectors.transpose * populationVectors = 1
  sampleOrthonormal : sampleVectors.transpose * sampleVectors = 1
  populationEigenvector : ∀ j : Fin q,
    Matrix.mulVec population (fun i => populationVectors i j) =
      populationEigenvalues (blockIndex r blockFits j) •
        (fun i => populationVectors i j)
  sampleEigenvector : ∀ j : Fin q,
    Matrix.mulVec sample (fun i => sampleVectors i j) =
      sampleEigenvalues (blockIndex r blockFits j) •
        (fun i => sampleVectors i j)

/-- The exact population-only gap from Theorem 2, with the source's infinite
boundary convention implemented by omitting a missing boundary before taking
the minimum. -/
def PopulationEigenspaceBlock.populationGap {p q : ℕ}
    (data : PopulationEigenspaceBlock p q) : ℝ :=
  finiteBoundaryMinimum
    (leftBoundaryGap data.populationEigenvalues data.r
      data.blockNonempty data.blockFits)
    (rightBoundaryGap data.populationEigenvalues data.r
      data.blockNonempty data.blockFits)

/-- `min(sqrt(q) * ||Ahat-A||_op, ||Ahat-A||_F)`. -/
def PopulationEigenspaceBlock.perturbationSize {p q : ℕ}
    (data : PopulationEigenspaceBlock p q) : ℝ :=
  min
    (Real.sqrt (q : ℝ) * matrixOperatorNorm (data.sample - data.population))
    (matrixFrobeniusNorm (data.sample - data.population))

/-- Frobenius norm of `sin Theta(Vhat,V)`, represented by the component of
`Vhat` orthogonal to the columns of `V`. -/
def sinThetaFrobenius {p q : ℕ}
    (Vhat V : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  matrixFrobeniusNorm ((1 - V * V.transpose) * Vhat)

/-- Orthogonality of a real square matrix. -/
def IsOrthogonalMatrix {q : ℕ} (O : Matrix (Fin q) (Fin q) ℝ) : Prop :=
  O.transpose * O = 1 ∧ O * O.transpose = 1

/-- Frobenius distance after aligning the two eigenvector bases. -/
def alignedBasisDistance {p q : ℕ}
    (Vhat V : Matrix (Fin p) (Fin q) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  matrixFrobeniusNorm (Vhat * O - V)

/-- **Scientific axiom: Yu--Wang--Samworth (2015), Theorem 2.**

The first conjunct is equation (2), and the existential second conjunct is
equation (3).  Both denominators use only the population eigengap.
-/
axiom yuWangSamworth2015_theorem2
    {p q : ℕ} (data : PopulationEigenspaceBlock p q)
    (hgap : 0 < data.populationGap) :
    sinThetaFrobenius data.sampleVectors data.populationVectors ≤
        2 * data.perturbationSize / data.populationGap ∧
      ∃ O : Matrix (Fin q) (Fin q) ℝ,
        IsOrthogonalMatrix O ∧
          alignedBasisDistance data.sampleVectors data.populationVectors O ≤
            (2 * Real.sqrt 2) * data.perturbationSize / data.populationGap

end

end QubitOracle.Paper.SourceFaithfulDavisKahan
