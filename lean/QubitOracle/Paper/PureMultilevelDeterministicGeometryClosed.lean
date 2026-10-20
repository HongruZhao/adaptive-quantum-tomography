import QubitOracle.Paper.PureStateFoundations

/-!
# Finite-dimensional pure-state deterministic geometry

This sidecar isolates the multilevel pure-state algebra that does not require
probability limits or a literature theorem.  Its principal result is the
concrete finite-dimensional rank-one specialization of the paper's
`eq:SI_root_fidelity`: fidelity is the rank-one Born trace, root fidelity is
its nonnegative square root, and squared Bures distance is
`2 - 2 * root fidelity`.

This module does not prove the corresponding statement for general mixed
density matrices, where matrix square roots and the full Uhlmann fidelity are
needed.  It also makes no claim about adaptive protocols, LAN, or risk limits.
-/

namespace QubitOracle.Paper
namespace PureMultilevelDeterministicGeometry

noncomputable section

variable {d : Type*} [Fintype d]

/-- Squared-overlap fidelity for two finite-dimensional pure vectors. -/
def pureMultilevelFidelity (psi phi : d -> ℂ) : ℝ :=
  basisBornProbability psi phi

/-- The root fidelity used in the Bures formula. -/
def pureMultilevelRootFidelity (psi phi : d -> ℂ) : ℝ :=
  Real.sqrt (pureMultilevelFidelity psi phi)

/-- Pure-state infidelity. -/
def pureMultilevelInfidelity (psi phi : d -> ℂ) : ℝ :=
  1 - pureMultilevelFidelity psi phi

/-- Squared Bures distance for finite-dimensional pure states. -/
def pureMultilevelBuresSq (psi phi : d -> ℂ) : ℝ :=
  2 * (1 - pureMultilevelRootFidelity psi phi)

/-- The pure-state fidelity is exactly the Born trace of the two rank-one
density matrices.  This is the finite-dimensional rank-one trace identity
behind `eq:r1_basis_born` and `eq:SI_r1_born`. -/
theorem pureMultilevelFidelity_eq_rankOneTrace (psi phi : d -> ℂ) :
    (pureMultilevelFidelity psi phi : ℂ) =
      (rankOneDensity phi * rankOneDensity psi).trace := by
  simpa [pureMultilevelFidelity, rankOneBasisProjector] using
    (basisBornProbability_eq_trace_rankOneDensity_mul_projector
      (basis := psi) (psi := phi))

/-- Concrete finite-dimensional pure-state specialization of
`eq:SI_root_fidelity`.  The general mixed-state operator-square-root identity
is deliberately not claimed here. -/
theorem eq_SI_root_fidelity_pure_multilevel_specialization
    (psi phi : d -> ℂ) :
    pureMultilevelRootFidelity psi phi ^ 2 =
        pureMultilevelFidelity psi phi ∧
    (pureMultilevelFidelity psi phi : ℂ) =
        (rankOneDensity phi * rankOneDensity psi).trace ∧
    pureMultilevelInfidelity psi phi =
        1 - pureMultilevelFidelity psi phi ∧
    pureMultilevelBuresSq psi phi =
        2 - 2 * pureMultilevelRootFidelity psi phi := by
  refine ⟨?_, pureMultilevelFidelity_eq_rankOneTrace psi phi, rfl, ?_⟩
  · unfold pureMultilevelRootFidelity pureMultilevelFidelity
    exact Real.sq_sqrt (Complex.normSq_nonneg _)
  · unfold pureMultilevelBuresSq
    ring

/-- Normalized vectors give trace-one rank-one density matrices, while their
fidelity and Bures quantities obey the exact finite-dimensional identities
above. -/
theorem normalizedPureMultilevel_exactGeometry
    (psi phi : d -> ℂ)
    (hpsi : pureStateNormSq psi = 1)
    (hphi : pureStateNormSq phi = 1) :
    (rankOneDensity psi).trace = 1 ∧
    (rankOneDensity phi).trace = 1 ∧
    (pureMultilevelFidelity psi phi : ℂ) =
        (rankOneDensity phi * rankOneDensity psi).trace ∧
    pureMultilevelRootFidelity psi phi ^ 2 =
        pureMultilevelFidelity psi phi ∧
    pureMultilevelBuresSq psi phi =
        2 - 2 * pureMultilevelRootFidelity psi phi := by
  refine ⟨rankOneDensity_trace_eq_one psi hpsi,
    rankOneDensity_trace_eq_one phi hphi,
    pureMultilevelFidelity_eq_rankOneTrace psi phi, ?_, ?_⟩
  · exact (eq_SI_root_fidelity_pure_multilevel_specialization psi phi).1
  · exact (eq_SI_root_fidelity_pure_multilevel_specialization psi phi).2.2.2

end

end PureMultilevelDeterministicGeometry
end QubitOracle.Paper
