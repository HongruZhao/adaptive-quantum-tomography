import QubitOracle.Paper.HallHeydeCor31LiteratureStatement

/-!
# Source-faithful Hall--Heyde Corollary 3.1 interface

This module contains exactly one imported literature atom. All finite-space
identities, conditional-expectation calculations, score bounds, Fisher
information calculations, and convergence reductions remain Lean theorems.

Source: P. Hall and C. C. Heyde, Martingale Limit Theory and Its
Application, Academic Press, 1980, Corollary 3.1, pp. 58--59,
DOI: 10.1016/C2013-0-10818-5.

The proposition named below is defined, without axioms, in
HallHeydeCor31LiteratureStatement.lean. Consequently the declaration is an
inspectable transfer of the cited scalar martingale-array CLT rather than a
paper-specific tomography assumption.
-/

namespace QubitOracle.Paper

/-- External theorem atom: Hall--Heyde (1980), Corollary 3.1, in the
deterministic limiting-variance form encoded by
HallHeyde1980Corollary31DeterministicVarianceStatement. -/
axiom hallHeyde1980_corollary3_1_deterministicVariance_external :
    HallHeyde1980Corollary31DeterministicVarianceStatement

end QubitOracle.Paper
