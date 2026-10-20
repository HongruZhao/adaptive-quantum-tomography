-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.P1PositiveBatches
import QubitOracle.Paper.P1BuresOptimality
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.GlobalPFSICOptimality
import QubitOracle.AdaptiveDesign.GlobalPFSICBorn
import QubitOracle.AdaptiveDesign.P2BornFisherIdentification
import QubitOracle.AdaptiveDesign.PVMBornFisherIdentification
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GeneralPOVMExample
import QubitOracle.AdaptiveDesign.PhasePairAdaptive

/-!
# The first two adaptive tomography theorems

P1: interior mixed qubit, literal all-observation ridge estimator, arbitrary
positive predetermined batches, predictable and realized Bures information.

P2: every finite complex dimension `d+1` with `d>0`, literal one-hot ridge
estimator and nearest pure projection for ANY finite identifying POVM,
any positive ridge constant, and arbitrary positive batches. Reference
regularity and rank-one seed effects yield literal Born Fisher convergence
after phase pairing. Its half-QFI identity is proved, not assumed.
The earlier explicit POVM is retained as an optional verified example.

P2 also has an ordinary PVM algorithm with explicit vanishing exploration,
a design-averaged all-observation estimator, and the same limiting information.

The imported optimality theorems compare the attained targets against actual
finite-outcome POVMs. Their transitive audits use only Lean's foundations.
No LAN, central limit, or estimator risk-attainment assertion is imported as
part of either first-theorem conclusion.
-/

-/
