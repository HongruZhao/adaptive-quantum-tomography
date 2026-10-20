import Mathlib

/-!
# Generic finite-dimensional pure-state foundations

This file supplies the finite-dimensional complex linear algebra underlying
the pure-state parts of `eq:r1_param`, `eq:r1_basis_born`, `eq:SI_states`, and
`eq:SI_r1_born`.  Everything is proved directly from finite sums.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

variable {d : Type*} [Fintype d]

/-- The coefficient squared norm of a finite-dimensional complex vector. -/
def pureStateNormSq (psi : d -> ℂ) : ℝ :=
  ∑ i, Complex.normSq (psi i)

/-- The rank-one matrix `|psi><psi|` (`eq:r1_param` and the pure component of
`eq:SI_states`). -/
def rankOneDensity (psi : d -> ℂ) : Matrix d d ℂ :=
  fun i j => psi i * star (psi j)

/-- The trace of `|psi><psi|` is the squared norm of `psi`. -/
theorem rankOneDensity_trace_eq_normSq (psi : d -> ℂ) :
    (rankOneDensity psi).trace = (pureStateNormSq psi : ℂ) := by
  rw [show (pureStateNormSq psi : ℂ) =
      ∑ i, (Complex.normSq (psi i) : ℂ) by simp [pureStateNormSq]]
  apply Finset.sum_congr rfl
  intro i _
  simpa [rankOneDensity, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- A normalized state vector produces a trace-one rank-one density matrix. -/
theorem rankOneDensity_trace_eq_one (psi : d -> ℂ)
    (hpsi : pureStateNormSq psi = 1) :
    (rankOneDensity psi).trace = 1 := by
  rw [rankOneDensity_trace_eq_normSq, hpsi]
  norm_num

/-- Entrywise Hermitian symmetry of a rank-one density matrix. -/
theorem rankOneDensity_hermitian_symmetry (psi : d -> ℂ) (i j : d) :
    rankOneDensity psi i j = star (rankOneDensity psi j i) := by
  simp [rankOneDensity, mul_comm]

/-- A basis-vector Born amplitude, `\langle basis | psi \rangle`. -/
def basisBornAmplitude (basis psi : d -> ℂ) : ℂ :=
  ∑ i, star (basis i) * psi i

/-- The basis Born probability, defined as the squared amplitude
(`eq:r1_basis_born` and `eq:SI_r1_born`). -/
def basisBornProbability (basis psi : d -> ℂ) : ℝ :=
  Complex.normSq (basisBornAmplitude basis psi)

/-- The rank-one projector associated with a basis vector. -/
def rankOneBasisProjector (basis : d -> ℂ) : Matrix d d ℂ :=
  rankOneDensity basis

/-- The trace of two rank-one operators factors into a Born amplitude and its
complex conjugate. -/
theorem trace_rankOneDensity_mul_rankOneBasisProjector
    (basis psi : d -> ℂ) :
    (rankOneDensity psi * rankOneBasisProjector basis).trace =
      basisBornAmplitude basis psi * star (basisBornAmplitude basis psi) := by
  classical
  calc
    (rankOneDensity psi * rankOneBasisProjector basis).trace =
        ∑ i, ∑ j,
          (psi i * star (psi j)) * (basis j * star (basis i)) := by
            rfl
    _ = ∑ i, ∑ j,
          (star (basis i) * psi i) * (star (psi j) * basis j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ i, star (basis i) * psi i) *
          (∑ j, star (psi j) * basis j) := by
            rw [Finset.sum_mul_sum]
    _ = basisBornAmplitude basis psi *
          star (basisBornAmplitude basis psi) := by
            simp [basisBornAmplitude, mul_comm]

/-- The squared-amplitude Born probability equals
`Tr(|psi><psi| |basis><basis|)`. -/
theorem basisBornProbability_eq_trace_rankOneDensity_mul_projector
    (basis psi : d -> ℂ) :
    (basisBornProbability basis psi : ℂ) =
      (rankOneDensity psi * rankOneBasisProjector basis).trace := by
  rw [trace_rankOneDensity_mul_rankOneBasisProjector]
  simpa [basisBornProbability, mul_comm] using
    (Complex.normSq_eq_conj_mul_self
      (z := basisBornAmplitude basis psi))

end

end QubitOracle.Paper
