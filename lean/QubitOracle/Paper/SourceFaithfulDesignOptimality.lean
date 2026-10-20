import QubitOracle.Paper.SourceFaithfulGillMassar
import QubitOracle.Paper.MixedOracleUniqueness
import QubitOracle.Paper.PureBuresLocal
import QubitOracle.Paper.MixedBuresLocal

/-!
# Source-faithful Bures and fidelity design optimality

This module connects the source-faithful one-copy Gill--Massar theorem to the
paper's kernel-checked design optimization.  Every endpoint is a statement
about Fisher-information design risk.  No estimator, MLE efficiency, LAN
transfer, or expected-loss convergence is assumed.

For pure states, infidelity and squared Bures distance have the common local
quadratic weight `(1/4) I`; the exact infidelity identity and the controlled
Bures remainder are recalled below.  For an interior mixed qubit, the common
normalized quadratic cost is `(1/4) I_3`.  The latter identification with a
physical cost `G` and information `M` remains an explicit equality hypothesis
in the physical-coordinate endpoint.
-/

namespace QubitOracle.Paper.SourceFaithfulDesignOptimality

open QubitOracle
open QubitOracle.Paper
open QubitOracle.Paper.SourceFaithfulGillMassar

noncomputable section

/-! ## Pure states in arbitrary finite dimension -/

/-- The exact pure-state infidelity identity and Bures remainder certify the
common local quadratic weight `(1/4) I`.  This is deterministic loss geometry
and uses no literature axiom. -/
theorem pureBuresInfidelity_common_quadratic_weight
    {n : ℕ} (h : TangentIndex n → ℝ)
    (hchart : tangentRadiusSq h ≤ 4) :
    traceChartLoss h =
        tangentQuadratic ((1 / 4 : ℝ) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h ∧
      0 ≤ buresChartLoss h -
        tangentQuadratic ((1 / 4 : ℝ) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h ∧
      buresChartLoss h -
          tangentQuadratic ((1 / 4 : ℝ) •
            (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ)) h ≤
        tangentRadiusSq h ^ 2 / 16 := by
  have hb := buresChartLoss_quadratic_remainder_bounds h hchart
  exact ⟨traceChartLoss_eq_quadratic h hchart, hb.1, hb.2⟩

/-- Source-faithful lower bound for the common pure-state Bures/infidelity
quadratic design risk. -/
theorem pureBuresInfidelity_quadraticDesign_lower_bound_from_source
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (TangentIndex n))
    (P : FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (hM : M.PosDef)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    n ≤ isotropicRisk (1 / 4 : ℝ) M :=
  paperRankOne_buresRisk_lower_bound model P M hM hHpos hH hI

/-- The equal two-basis information is Bures- and infidelity-optimal against
every regular finite-POVM competitor connected to the source model. -/
theorem pureTwoBasis_buresInfidelity_optimal_from_source
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (TangentIndex n))
    (P : FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (F : OracleFrame n) (hM : M.PosDef)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    isotropicRisk (1 / 4 : ℝ) (equalMixtureFisher F) ≤
      isotropicRisk (1 / 4 : ℝ) M := by
  rw [equalMixture_buresQuadraticRisk]
  exact pureBuresInfidelity_quadraticDesign_lower_bound_from_source
    model P M hM hHpos hH hI

/-- Sharp tie characterization for both pure-state local losses. -/
theorem pureBuresInfidelity_tie_iff_halfIdentity_from_source
    {n : ℕ} {O : Type} [Fintype O]
    (model : OneCopySLDModel (n + 1) (TangentIndex n))
    (P : FinitePOVM (Fin (n + 1)) O)
    [GillMassar2000OneCopyAssumption model P]
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ)
    (F : OracleFrame n) (hM : M.PosDef)
    (hHpos : (sldQuantumFisher model).PosDef)
    (hH : sldQuantumFisher model = 1)
    (hI : oneCopyClassicalFisher model P = M) :
    isotropicRisk (1 / 4 : ℝ) M =
        isotropicRisk (1 / 4 : ℝ) (equalMixtureFisher F) ↔
      M = (1 / 2 : ℝ) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) ℝ) := by
  rw [equalMixture_buresQuadraticRisk]
  have hbudget := paperRankOne_satisfiesGillMassarTraceBudget
    model P M hHpos hH hI
  simpa using gillMassarBudget_risk_eq_iff
    (1 / 4 : ℝ) M (by norm_num) hM hbudget

/-! ## Interior mixed qubits -/

/-- Common normalized local quadratic cost for squared Bures distance and
infidelity in the interior mixed-qubit model. -/
def mixedBuresInfidelityNormalizedCost : OracleMatrix :=
  (1 / 4 : ℝ) • (1 : OracleMatrix)

/-- Positive square root of the normalized Bures/infidelity cost. -/
def mixedBuresInfidelityNormalizedSqrt : OracleMatrix :=
  (1 / 2 : ℝ) • (1 : OracleMatrix)

/-- Its explicit inverse. -/
def mixedBuresInfidelityNormalizedSqrtInv : OracleMatrix :=
  (2 : ℝ) • (1 : OracleMatrix)

/-- Unique normalized information optimizer. -/
def mixedBuresInfidelityNormalizedOptimizer : OracleMatrix :=
  (1 / 3 : ℝ) • (1 : OracleMatrix)

theorem mixedBuresInfidelityNormalizedSqrt_transpose :
    mixedBuresInfidelityNormalizedSqrt.transpose =
      mixedBuresInfidelityNormalizedSqrt := by
  simp [mixedBuresInfidelityNormalizedSqrt]

theorem mixedBuresInfidelityNormalizedSqrt_sq :
    mixedBuresInfidelityNormalizedSqrt *
        mixedBuresInfidelityNormalizedSqrt =
      mixedBuresInfidelityNormalizedCost := by
  norm_num [mixedBuresInfidelityNormalizedSqrt,
    mixedBuresInfidelityNormalizedCost, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

theorem mixedBuresInfidelityNormalizedSqrt_mul_inv :
    mixedBuresInfidelityNormalizedSqrt *
        mixedBuresInfidelityNormalizedSqrtInv = 1 := by
  norm_num [mixedBuresInfidelityNormalizedSqrt,
    mixedBuresInfidelityNormalizedSqrtInv, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

theorem mixedBuresInfidelityNormalizedSqrt_trace :
    Matrix.trace mixedBuresInfidelityNormalizedSqrt = 3 / 2 := by
  norm_num [mixedBuresInfidelityNormalizedSqrt,
    Matrix.trace_smul, Matrix.trace_one]

theorem mixedBuresInfidelity_oracleOptimizer_eq :
    oracleMatrixOptimizer mixedBuresInfidelityNormalizedSqrt (3 / 2) =
      mixedBuresInfidelityNormalizedOptimizer := by
  norm_num [oracleMatrixOptimizer, mixedBuresInfidelityNormalizedSqrt,
    mixedBuresInfidelityNormalizedOptimizer, smul_smul]

/-- The normalized optimizer is an actual finite convex mixture of unit
Bloch rank-one projectors, not merely a point in a relaxed matrix region. -/
theorem mixedBuresInfidelityNormalizedOptimizer_isProjective :
    IsNormalizedProjectiveInformation
      mixedBuresInfidelityNormalizedOptimizer := by
  apply (normalized_projective_information_iff _).2
  constructor
  · exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 3)).posSemidef
  · norm_num [mixedBuresInfidelityNormalizedOptimizer,
      Matrix.trace_smul, Matrix.trace_one]

/-- Kernel-checked attained normalized value `9/4`. -/
theorem mixedBuresInfidelityNormalizedOptimizer_value :
    mixedDesignCriterion mixedBuresInfidelityNormalizedCost
        mixedBuresInfidelityNormalizedOptimizer = 9 / 4 := by
  have h := oracleMatrixOptimizer_value
    mixedBuresInfidelityNormalizedCost
    mixedBuresInfidelityNormalizedSqrt
    mixedBuresInfidelityNormalizedSqrtInv (3 / 2 : ℝ)
    (by norm_num)
    mixedBuresInfidelityNormalizedSqrt_mul_inv
    mixedBuresInfidelityNormalizedSqrt_sq
    mixedBuresInfidelityNormalizedSqrt_trace
  rw [mixedBuresInfidelity_oracleOptimizer_eq] at h
  norm_num [mixedDesignCriterion] at h ⊢
  exact h

/-- A supplied square-root pair identifies `Ainv` with the actual inverse of
`A`; this is pure matrix algebra. -/
theorem oracleSuppliedInverse_eq_matrixInverse
    (A Ainv H K : OracleMatrix)
    (hHK : H * K = 1)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv) :
    A⁻¹ = Ainv := by
  apply Matrix.inv_eq_right_inv
  calc
    A * Ainv = (H * H) * (K * K) := by rw [hHsq, hKsq]
    _ = H * (H * K) * K := by noncomm_ring
    _ = 1 := by rw [hHK]; simp [hHK]

/-- The source trace becomes the normalized Gill--Massar budget.  The only
remaining model-to-design bridge is the displayed scalar equality identifying
the source invariant trace with `trace A`. -/
theorem mixedQubit_normalizedTraceBudget_from_source
    {O : Type} [Fintype O]
    (model : OneCopySLDModel 2 (Fin 3))
    (P : FinitePOVM (Fin 2) O)
    [GillMassar2000OneCopyAssumption model P]
    (A : OracleMatrix)
    (hHpos : (sldQuantumFisher model).PosDef)
    (htraceIdentification : informationTrace model P = Matrix.trace A) :
    Matrix.trace A ≤ 1 := by
  have hsource := gillMassar2000_theorems_I_II_oneCopy
    model P (by norm_num) hHpos
  norm_num at hsource
  rwa [htraceIdentification] at hsource

/-- Sharp normalized Bures/infidelity design theorem for an arbitrary
one-copy mixed-qubit competitor.  `H,K` are explicit square-root witnesses;
the source theorem supplies only the trace budget. -/
theorem mixedQubit_buresInfidelity_normalized_optimality_from_source
    {O : Type} [Fintype O]
    (model : OneCopySLDModel 2 (Fin 3))
    (P : FinitePOVM (Fin 2) O)
    [GillMassar2000OneCopyAssumption model P]
    (A Ainv H K : OracleMatrix)
    (hSourceHpos : (sldQuantumFisher model).PosDef)
    (htraceIdentification : informationTrace model P = Matrix.trace A)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hrisk0 : 0 ≤ Matrix.trace
      (mixedBuresInfidelityNormalizedCost * Ainv)) :
    9 / 4 ≤ mixedDesignCriterion
        mixedBuresInfidelityNormalizedCost A ∧
      mixedDesignCriterion mixedBuresInfidelityNormalizedCost
          mixedBuresInfidelityNormalizedOptimizer = 9 / 4 ∧
      (mixedDesignCriterion mixedBuresInfidelityNormalizedCost A = 9 / 4 →
        A = mixedBuresInfidelityNormalizedOptimizer) := by
  have hbudget := mixedQubit_normalizedTraceBudget_from_source
    model P A hSourceHpos htraceIdentification
  have htraceR0 :
      0 ≤ Matrix.trace mixedBuresInfidelityNormalizedSqrt := by
    rw [mixedBuresInfidelityNormalizedSqrt_trace]
    norm_num
  have hgeneral := QubitOracle.Paper.Label.prop_SI_mixed_oracle
    A Ainv mixedBuresInfidelityNormalizedCost H K
    mixedBuresInfidelityNormalizedSqrt
    mixedBuresInfidelityNormalizedSqrtInv (3 / 2 : ℝ)
    hHK hHsym hKsym
    mixedBuresInfidelityNormalizedSqrt_transpose
    hHsq hKsq mixedBuresInfidelityNormalizedSqrt_sq
    htraceA0 hbudget hrisk0 htraceR0
    mixedBuresInfidelityNormalizedSqrt_trace (by norm_num)
    mixedBuresInfidelityNormalizedSqrt_mul_inv
  have hinv := oracleSuppliedInverse_eq_matrixInverse
    A Ainv H K hHK hHsq hKsq
  refine ⟨?_, mixedBuresInfidelityNormalizedOptimizer_value, ?_⟩
  · have hlower := hgeneral.1
    norm_num at hlower
    simpa [mixedDesignCriterion, hinv] using hlower
  · intro heq
    have heq' :
        Matrix.trace (mixedBuresInfidelityNormalizedCost * Ainv) =
          (3 / 2 : ℝ) ^ 2 := by
      rw [← hinv]
      norm_num [mixedDesignCriterion] at heq ⊢
      exact heq
    have huniq := hgeneral.2.2 heq'
    rwa [mixedBuresInfidelity_oracleOptimizer_eq] at huniq

/-- Physical-coordinate lower bound.  The equality hypothesis is exactly the
remaining `C = J^{-1/2} G J^{-1/2}` and
`A = J^{-1/2} M J^{-1/2}` risk-identification bridge. -/
theorem mixedQubit_buresInfidelity_physical_lower_bound_from_source
    {O : Type} [Fintype O]
    (model : OneCopySLDModel 2 (Fin 3))
    (P : FinitePOVM (Fin 2) O)
    [GillMassar2000OneCopyAssumption model P]
    (G M A Ainv H K : OracleMatrix)
    (hSourceHpos : (sldQuantumFisher model).PosDef)
    (htraceIdentification : informationTrace model P = Matrix.trace A)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hrisk0 : 0 ≤ Matrix.trace
      (mixedBuresInfidelityNormalizedCost * Ainv))
    (hphysicalRisk : mixedDesignCriterion G M =
      mixedDesignCriterion mixedBuresInfidelityNormalizedCost A) :
    9 / 4 ≤ mixedDesignCriterion G M := by
  rw [hphysicalRisk]
  exact (mixedQubit_buresInfidelity_normalized_optimality_from_source
    model P A Ainv H K hSourceHpos htraceIdentification hHK hHsym hKsym
      hHsq hKsq htraceA0 hrisk0).1

/-- Physical design optimality against one arbitrary competitor.  The two
coordinate equalities are explicit, and no assertion about an estimator is
made. -/
theorem mixedQubit_buresInfidelity_physical_design_optimal_from_source
    {O : Type} [Fintype O]
    (model : OneCopySLDModel 2 (Fin 3))
    (P : FinitePOVM (Fin 2) O)
    [GillMassar2000OneCopyAssumption model P]
    (G M Mstar A Ainv H K : OracleMatrix)
    (hSourceHpos : (sldQuantumFisher model).PosDef)
    (htraceIdentification : informationTrace model P = Matrix.trace A)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hrisk0 : 0 ≤ Matrix.trace
      (mixedBuresInfidelityNormalizedCost * Ainv))
    (hcompetitorRisk : mixedDesignCriterion G M =
      mixedDesignCriterion mixedBuresInfidelityNormalizedCost A)
    (hoptimalRisk : mixedDesignCriterion G Mstar =
      mixedDesignCriterion mixedBuresInfidelityNormalizedCost
        mixedBuresInfidelityNormalizedOptimizer) :
    mixedDesignCriterion G Mstar ≤ mixedDesignCriterion G M := by
  rw [hoptimalRisk, hcompetitorRisk,
    mixedBuresInfidelityNormalizedOptimizer_value]
  exact (mixedQubit_buresInfidelity_normalized_optimality_from_source
    model P A Ainv H K hSourceHpos htraceIdentification hHK hHsym hKsym
      hHsq hKsq htraceA0 hrisk0).1

/-- Existing deterministic control for the exact mixed-qubit Bures loss.
It is deliberately separate from the Fisher-design theorem above. -/
theorem mixedQubit_exactBuresLoss_local_upper
    (theta delta : Fin 3 → ℝ)
    (hinterior : blochNormSq theta < 1)
    (hlocal :
      2 * |blochDot theta delta| + blochNormSq delta ≤
        1 - blochNormSq theta) :
    mixedBlochBuresSq theta delta ≤
      2 * blochNormSq delta / (1 - blochNormSq theta) :=
  mixedBlochBuresSq_local_upper theta delta hinterior hlocal

end

end QubitOracle.Paper.SourceFaithfulDesignOptimality
