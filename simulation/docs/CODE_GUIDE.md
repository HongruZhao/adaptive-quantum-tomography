# Reading the simulation code

The numerical implementation is unchanged from code version 1.2.0. Start with the CLI, then follow one trajectory rather than reading plotting code first.

| File | Role |
|---|---|
| [__main__.py](../src/adaptive_tomography/__main__.py) | `run`, `plot` and `design` commands; caller-selected paths |
| [simulation.py](../src/adaptive_tomography/simulation.py) | Independent random streams, three main studies, saved arrays and receipts |
| [schedules.py](../src/adaptive_tomography/schedules.py) | Predetermined batches and nearest completed-batch reports |
| [mixed.py](../src/adaptive_tomography/mixed.py) | Algorithms 1-2: allocations, safeguarded fits and binary Born sampling |
| [pure.py](../src/adaptive_tomography/pure.py) | Algorithm 3: reference bases, all-record preliminary fit, tangent correction and information |
| [estimators.py](../src/adaptive_tomography/estimators.py) | Phase pairing, fixed Householder frame, eigenvector convention and weighted tangent solve |
| [design.py](../src/adaptive_tomography/design.py) | Mean pure-state information diagnostics and output-checked stream replay |
| [plotting.py](../src/adaptive_tomography/plotting.py) | Read saved data, verify summaries and render figures; no sampling |
| [optional.py](../src/adaptive_tomography/optional.py) | Finite covariance-example measurement and the historical optional simulation |
| [tests](../tests) | Independent small-record objectives, apparatus, batch and ensemble checks |

For each new batch, the preliminary estimate uses all previous records to select the next measurement. Each batch is sampled from the complete setting/outcome Born law. Every acquired copy enters the fit. At a reporting horizon, the pure correction evaluates all past effects at one final preliminary estimate, solves the weighted tangent equations and applies the normalization retraction.

Truth is an input to sampling and diagnostic calculation, not to adaptive measurement selection or estimation. Mixed loss weights differ; the pure dimension-4 design targets squared Bures loss. `C_n^cur` concerns the next batch and `C_n^avg` concerns information actually collected. The pure mean design panel averages per-record inverse-information criteria rather than inverting a pooled information matrix.

The code stores complete batch count summaries, then retains losses, tangent-error diagnostics, apparatus and stream rules in the public data bundle. It does not archive every intermediate record. A fixed seed does not guarantee identical adaptive paths under different numerical libraries or eigensolver conventions.

The current default [paper configuration](../configs/paper.json) omits the historical optional covariance runs. The unchanged [historical configuration](../configs/historical_full_run_20261017.json) reproduces the scope of the saved five-study bundle.
