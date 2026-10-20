import Mathlib.Analysis.CStarAlgebra.Matrix
import QubitOracle.Paper.CompactLimitTransfer
import QubitOracle.TwoBasis
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle
namespace Paper

open Filter Set
open scoped BigOperators ComplexConjugate Matrix.Norms.Elementwise Topology

noncomputable section

/-- Controller-adapted chi basis expressed in a fixed true frame. -/
def controllerChiBasis {n : Nat} (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Complex :=
  U * chiBasis F

/-- Controller-adapted tau basis expressed in a fixed true frame. -/
def controllerTauBasis {n : Nat} (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) Complex :=
  U * tauBasis F

/-- True-state outcome probability of a basis represented in the fixed true
frame, whose first vector is the true ray. -/
def fixedChartBasisProbability {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (k : Fin (n + 1)) : Real :=
  Complex.normSq (B 0 k)

/-- True-chart probability gradient of an arbitrary measurement basis. -/
def fixedChartBasisGradient {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (k : Fin (n + 1)) : TangentIndex n -> Real
  | Sum.inl a => (star (B 0 k) * B a.succ k).re
  | Sum.inr a => (star (B 0 k) * B a.succ k).im

/-- Classical Fisher information of an arbitrary basis at the true chart
origin. -/
def fixedChartBasisFisher {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    Matrix (TangentIndex n) (TangentIndex n) Real :=
  classicalFisher (fixedChartBasisProbability B)
    (fixedChartBasisGradient B)

/-- Equal chi/tau exploitation information evaluated at the truth. -/
def rankOneStageInformation {n : Nat} (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    Matrix (TangentIndex n) (TangentIndex n) Real :=
  (1 / 2 : Real) • fixedChartBasisFisher (controllerChiBasis F U) +
    (1 / 2 : Real) • fixedChartBasisFisher (controllerTauBasis F U)

/-- Squared overlap between the controller ray and the true ray. -/
def controllerTrueOverlapSq {n : Nat}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) : Real :=
  Complex.normSq (U 0 0)

/-- Unitary matrices are compact in finite dimension. -/
theorem isCompact_unitaryMatrices {d : Type*} [Fintype d] [DecidableEq d] :
    IsCompact {U : Matrix d d Complex |
      U ∈ Matrix.unitaryGroup d Complex} := by
  have hclosed : IsClosed {U : Matrix d d Complex |
      U ∈ Matrix.unitaryGroup d Complex} := by
    have heq : {U : Matrix d d Complex |
        U ∈ Matrix.unitaryGroup d Complex} =
        {U | U * star U = 1} := by
      ext U
      exact Matrix.mem_unitaryGroup_iff
    rw [heq]
    exact isClosed_eq (by fun_prop) continuous_const
  apply (ProperSpace.isCompact_closedBall
    (0 : Matrix d d Complex) 1).of_isClosed_subset hclosed
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entrywise_sup_norm_bound_of_unitary hU

/-- Column normalization of a unitary matrix, in squared complex norms. -/
theorem unitary_column_normSq_sum {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix d d Complex) (hU : U ∈ Matrix.unitaryGroup d Complex)
    (j : d) :
    (∑ i, Complex.normSq (U i j)) = 1 := by
  have h := congrFun (congrFun
    (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  have hre := congrArg Complex.re h
  change (∑ i, ((U i j).re * (U i j).re +
    (U i j).im * (U i j).im)) = 1
  simpa [Matrix.mul_apply, Matrix.one_apply] using hre

/-- Row normalization of a unitary matrix, in squared complex norms. -/
theorem unitary_row_normSq_sum {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix d d Complex) (hU : U ∈ Matrix.unitaryGroup d Complex)
    (i : d) :
    (∑ j, Complex.normSq (U i j)) = 1 := by
  have h := congrFun (congrFun
    (Matrix.mem_unitaryGroup_iff.mp hU) i) i
  have hre := congrArg Complex.re h
  change (∑ j, ((U i j).re * (U i j).re +
    (U i j).im * (U i j).im)) = 1
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm] using hre

/-- Unit overlap of the first entry forces every other first-column entry to
vanish. -/
theorem unitary_firstColumn_eq_zero_of_overlap_one {n : Nat}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (i : Fin (n + 1)) (hi : i ≠ 0) : U i 0 = 0 := by
  have hsum := unitary_column_normSq_sum U hU 0
  have hzero :
      ∑ k ∈ (Finset.univ.erase (0 : Fin (n + 1))),
        Complex.normSq (U k 0) = 0 := by
    have herase := Finset.sum_erase_add Finset.univ
      (fun k => Complex.normSq (U k 0)) (Finset.mem_univ 0)
    unfold controllerTrueOverlapSq at hoverlap
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (U k 0))).mp hzero
  apply Complex.normSq_eq_zero.mp
  exact hterm i (by simp [hi])

/-- Unit overlap likewise forces every other first-row entry to vanish. -/
theorem unitary_firstRow_eq_zero_of_overlap_one {n : Nat}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (j : Fin (n + 1)) (hj : j ≠ 0) : U 0 j = 0 := by
  have hsum := unitary_row_normSq_sum U hU 0
  have hzero :
      ∑ k ∈ (Finset.univ.erase (0 : Fin (n + 1))),
        Complex.normSq (U 0 k) = 0 := by
    have herase := Finset.sum_erase_add Finset.univ
      (fun k => Complex.normSq (U 0 k)) (Finset.mem_univ 0)
    unfold controllerTrueOverlapSq at hoverlap
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Complex.normSq_nonneg (U 0 k))).mp hzero
  apply Complex.normSq_eq_zero.mp
  exact hterm j (by simp [hj])

/-- Phase-adjusted tangent block of a controller frame on the exact true-ray
fiber. -/
def fiberComplement {n : Nat}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    Matrix (Fin n) (Fin n) Complex :=
  fun a b => star (U 0 0) * U a.succ b.succ

/-- The phase-adjusted tangent block is unitary on the exact true-ray fiber. -/
theorem fiberComplement_mem_unitary {n : Nat}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1) :
    fiberComplement U ∈ Matrix.unitaryGroup (Fin n) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  have hrow := congrFun (congrFun
    (Matrix.mem_unitaryGroup_iff.mp hU) a.succ) b.succ
  have ha0 := unitary_firstColumn_eq_zero_of_overlap_one
    U hU hoverlap a.succ (Fin.succ_ne_zero a)
  have hb0 := unitary_firstColumn_eq_zero_of_overlap_one
    U hU hoverlap b.succ (Fin.succ_ne_zero b)
  unfold controllerTrueOverlapSq at hoverlap
  change (∑ k : Fin n, ((star (U 0 0) * U a.succ k.succ) *
    star (star (U 0 0) * U b.succ k.succ))) = _
  have hstar (k : Fin n) :
      star (star (U 0 0) * U b.succ k.succ) =
        U 0 0 * star (U b.succ k.succ) := by
    rw [star_mul', star_star]
  simp_rw [hstar]
  rw [show (∑ k : Fin n, ((star (U 0 0) * U a.succ k.succ) *
      (U 0 0 * star (U b.succ k.succ)))) =
      Complex.normSq (U 0 0) *
        ∑ k : Fin n, (U a.succ k.succ * star (U b.succ k.succ)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.normSq_eq_conj_mul_self]
    ac_rfl]
  rw [hoverlap]
  norm_num
  simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
    ha0, hb0] using hrow

/-- First row of the controller chi basis on the exact true-ray fiber. -/
theorem controllerChiBasis_zero_apply_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (k : Fin (n + 1)) :
    controllerChiBasis F U 0 k = U 0 0 * (F.W 0 k : Complex) := by
  unfold controllerChiBasis
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp_rw [unitary_firstRow_eq_zero_of_overlap_one U hU hoverlap
    _ (Fin.succ_ne_zero _)]
  simp [chiBasis]

/-- Tangent rows of the controller chi basis on the exact fiber. -/
theorem controllerChiBasis_succ_apply_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (a : Fin n) (k : Fin (n + 1)) :
    controllerChiBasis F U a.succ k =
      ∑ l : Fin n, (U a.succ l.succ * (F.W l.succ k : Complex)) := by
  unfold controllerChiBasis
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [unitary_firstColumn_eq_zero_of_overlap_one U hU hoverlap
    a.succ (Fin.succ_ne_zero a)]
  simp [chiBasis]

/-- First row of the controller tau basis on the exact true-ray fiber. -/
theorem controllerTauBasis_zero_apply_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (k : Fin (n + 1)) :
    controllerTauBasis F U 0 k =
      U 0 0 * (-Complex.I * (F.W 0 k : Complex)) := by
  unfold controllerTauBasis
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp_rw [unitary_firstRow_eq_zero_of_overlap_one U hU hoverlap
    _ (Fin.succ_ne_zero _)]
  simp [tauBasis_apply, phase]

/-- Tangent rows of the controller tau basis agree with those of chi on the
exact fiber. -/
theorem controllerTauBasis_succ_apply_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (a : Fin n) (k : Fin (n + 1)) :
    controllerTauBasis F U a.succ k =
      ∑ l : Fin n, (U a.succ l.succ * (F.W l.succ k : Complex)) := by
  unfold controllerTauBasis
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [unitary_firstColumn_eq_zero_of_overlap_one U hU hoverlap
    a.succ (Fin.succ_ne_zero a)]
  simp [tauBasis_apply, phase]


/-- Both adapted bases have the uniform oracle probabilities on the exact
true-ray fiber. -/
theorem controllerChiProbability_eq_baseProbability_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (k : Fin (n + 1)) :
    fixedChartBasisProbability (controllerChiBasis F U) k =
      baseProbability F k := by
  unfold fixedChartBasisProbability baseProbability
  rw [controllerChiBasis_zero_apply_of_overlap_one F U hU hoverlap k,
    map_mul]
  unfold controllerTrueOverlapSq at hoverlap
  rw [hoverlap, one_mul]
  simp
  ring

theorem controllerTauProbability_eq_baseProbability_of_overlap_one {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (k : Fin (n + 1)) :
    fixedChartBasisProbability (controllerTauBasis F U) k =
      baseProbability F k := by
  unfold fixedChartBasisProbability baseProbability
  rw [controllerTauBasis_zero_apply_of_overlap_one F U hU hoverlap k,
    map_mul]
  unfold controllerTrueOverlapSq at hoverlap
  rw [hoverlap, one_mul]
  simp
  ring







/-- Squared controller/true overlap is continuous. -/
theorem continuous_controllerTrueOverlapSq {n : Nat} :
    Continuous (controllerTrueOverlapSq (n := n)) := by
  change Continuous (fun U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
    (U 0 0).re * (U 0 0).re + (U 0 0).im * (U 0 0).im)
  fun_prop

/-- Basis probabilities are continuous functions of the basis entries. -/
theorem continuous_fixedChartBasisProbability {n : Nat}
    (k : Fin (n + 1)) :
    Continuous (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
      fixedChartBasisProbability B k) := by
  exact Complex.continuous_normSq.comp (continuous_apply_apply 0 k)

/-- Every true-chart probability-gradient coordinate is continuous in the
basis matrix. -/
theorem continuous_fixedChartBasisGradient {n : Nat}
    (k : Fin (n + 1)) (x : TangentIndex n) :
    Continuous (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
      fixedChartBasisGradient B k x) := by
  rcases x with a | a
  · unfold fixedChartBasisGradient
    exact Complex.continuous_re.comp
      ((continuous_star.comp (continuous_apply_apply 0 k)).mul
        (continuous_apply_apply a.succ k))
  · unfold fixedChartBasisGradient
    exact Complex.continuous_im.comp
      ((continuous_star.comp (continuous_apply_apply 0 k)).mul
        (continuous_apply_apply a.succ k))

/-- The fixed-chart basis Fisher map is continuous wherever every true
outcome probability is nonzero. -/
theorem continuousAt_fixedChartBasisFisher {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hprob : ∀ k, fixedChartBasisProbability B k ≠ 0) :
    ContinuousAt fixedChartBasisFisher B := by
  apply continuousAt_pi.2
  intro x
  apply continuousAt_pi.2
  intro y
  unfold fixedChartBasisFisher classicalFisher
  apply tendsto_finsetSum Finset.univ
  intro k hk
  exact ((continuous_fixedChartBasisGradient k x).continuousAt.mul
      (continuous_fixedChartBasisGradient k y).continuousAt).div₀
    (continuous_fixedChartBasisProbability k).continuousAt (hprob k)

/-- Matrix multiplication by either fixed oracle basis is continuous in the
controller frame. -/
theorem continuous_controllerChiBasis {n : Nat} (F : OracleFrame n) :
    Continuous (controllerChiBasis F) := by
  unfold controllerChiBasis
  fun_prop

theorem continuous_controllerTauBasis {n : Nat} (F : OracleFrame n) :
    Continuous (controllerTauBasis F) := by
  unfold controllerTauBasis
  fun_prop

/-- Stage Fisher information is continuous at any controller frame for which
both adapted bases have positive true probabilities. -/
theorem continuousAt_rankOneStageInformation {n : Nat}
    (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hchi : ∀ k,
      fixedChartBasisProbability (controllerChiBasis F U) k ≠ 0)
    (htau : ∀ k,
      fixedChartBasisProbability (controllerTauBasis F U) k ≠ 0) :
    ContinuousAt (rankOneStageInformation F) U := by
  have hhalf : ContinuousAt
      (fun _ : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
        (1 / 2 : Real)) U := continuousAt_const
  have hchiF : ContinuousAt
      (fun V => fixedChartBasisFisher (controllerChiBasis F V)) U :=
    (continuousAt_fixedChartBasisFisher _ hchi).comp
      (continuous_controllerChiBasis F).continuousAt
  have htauF : ContinuousAt
      (fun V => fixedChartBasisFisher (controllerTauBasis F V)) U :=
    (continuousAt_fixedChartBasisFisher _ htau).comp
      (continuous_controllerTauBasis F).continuousAt
  unfold rankOneStageInformation
  exact (hhalf.smul hchiF).add (hhalf.smul htauF)


/-- Each chi probability converges to the uniform oracle probability. -/
theorem controllerChiProbability_tendsto_base {n : Nat}
    (F : OracleFrame n)
    (controllerFrame : Nat ->
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hunitary : ∀ m, controllerFrame m ∈
      Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : Tendsto
      (fun m => controllerTrueOverlapSq (controllerFrame m))
      atTop (nhds 1)) (k : Fin (n + 1)) :
    Tendsto
      (fun m => fixedChartBasisProbability
        (controllerChiBasis F (controllerFrame m)) k)
      atTop (nhds (baseProbability F k)) := by
  have hcontinuous : Continuous
      (fun U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
        fixedChartBasisProbability (controllerChiBasis F U) k) :=
    (continuous_fixedChartBasisProbability k).comp
      (continuous_controllerChiBasis F)
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex |
      U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex}
    isCompact_unitaryMatrices controllerFrame hunitary
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 hoverlap
    (fun U => fixedChartBasisProbability (controllerChiBasis F U) k)
    (baseProbability F k) ?_
  intro U hU hOverlap
  exact ⟨hcontinuous.continuousAt,
    controllerChiProbability_eq_baseProbability_of_overlap_one
      F U hU hOverlap k⟩

/-- Each tau probability converges to the same uniform oracle probability. -/
theorem controllerTauProbability_tendsto_base {n : Nat}
    (F : OracleFrame n)
    (controllerFrame : Nat ->
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (hunitary : ∀ m, controllerFrame m ∈
      Matrix.unitaryGroup (Fin (n + 1)) Complex)
    (hoverlap : Tendsto
      (fun m => controllerTrueOverlapSq (controllerFrame m))
      atTop (nhds 1)) (k : Fin (n + 1)) :
    Tendsto
      (fun m => fixedChartBasisProbability
        (controllerTauBasis F (controllerFrame m)) k)
      atTop (nhds (baseProbability F k)) := by
  have hcontinuous : Continuous
      (fun U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex =>
        fixedChartBasisProbability (controllerTauBasis F U) k) :=
    (continuous_fixedChartBasisProbability k).comp
      (continuous_controllerTauBasis F)
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex |
      U ∈ Matrix.unitaryGroup (Fin (n + 1)) Complex}
    isCompact_unitaryMatrices controllerFrame hunitary
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 hoverlap
    (fun U => fixedChartBasisProbability (controllerTauBasis F U) k)
    (baseProbability F k) ?_
  intro U hU hOverlap
  exact ⟨hcontinuous.continuousAt,
    controllerTauProbability_eq_baseProbability_of_overlap_one
      F U hU hOverlap k⟩


namespace Label

/-- `eq:SI_general_r1_information`: fixed-chart finite-outcome Fisher
information.  The algebraic identity holds without a positivity premise;
positivity is needed only for the paper's statistical interpretation. -/
theorem eq_SI_general_r1_information {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (a b : TangentIndex n) :
    fixedChartBasisFisher B a b =
      ∑ k : Fin (n + 1),
        fixedChartBasisGradient B k a * fixedChartBasisGradient B k b /
          fixedChartBasisProbability B k :=
  rfl

/-- `eq:SI_stage_r1_info`: equal chi/tau stage information. -/
theorem eq_SI_stage_r1_info {n : Nat} (F : OracleFrame n)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex) :
    rankOneStageInformation F U =
      (1 / 2 : Real) • fixedChartBasisFisher (controllerChiBasis F U) +
        (1 / 2 : Real) • fixedChartBasisFisher (controllerTauBasis F U) :=
  rfl



end Label

end

end Paper
end QubitOracle
