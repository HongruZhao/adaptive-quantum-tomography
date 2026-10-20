import QubitOracle.AdaptiveDesign.PureTangentDimension

/-!
# Main-paper Proposition 2.1: pure-state quantum information

This permanent paper binding covers every clause of `prop:pure-qfi` and
equation (2.4), including arbitrary Hermitian directional SLDs, the full
complex trace identity, horizontal tangents, and coordinate contraction.

The project's dimension is `D = d + 1`. The statements hold for every `d`,
and therefore in particular for the paper's `D ≥ 2`. A `PureVector d`
has unit norm, `rankOneDensity h.val` is `P = h h*`, and `tangentSpace h`
consists of Hermitian matrices satisfying `P A + A P = A`. No information
identity or statistical assertion is assumed as an axiom.
-/

namespace QubitOracle.Paper.PureQuantumInformation

open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {d p : ℕ}

/-- The directional SLD equation, multiplied by two. -/
def IsDirectionalSLD (h : PureVector d) (A : tangentSpace h)
    (L : HermitianSpace (d+1)) : Prop :=
  rankOneDensity h.val * toMatrix L + toMatrix L * rankOneDensity h.val =
    (2 : ℝ) • toMatrix A.val

theorem directional_sld_equation_iff (h : PureVector d) (A : tangentSpace h)
    (L : HermitianSpace (d+1)) :
    IsDirectionalSLD h A L ↔
      (1/2 : ℝ) • (rankOneDensity h.val * toMatrix L +
        toMatrix L * rankOneDensity h.val) = toMatrix A.val := by
  constructor
  · intro hL
    rw [hL, smul_smul]
    norm_num
  · intro hL
    have hh := congrArg (fun X => (2 : ℝ) • X) hL
    simpa only [IsDirectionalSLD, smul_smul,
      show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] using hh

theorem directional_sld_exists (h : PureVector d) (A : tangentSpace h) :
    IsDirectionalSLD h A (PureSLDMetric.pureSLD h A) :=
  (directional_sld_equation_iff h A _).mpr (PureSLDMetric.sld_equation h A)

/-- The intrinsic metric evaluated using the proved SLD choice `2 A`. -/
def quantumInformation (h : PureVector d) (A B : tangentSpace h) : ℝ :=
  PureSLDMetric.metricFromSLD h A B

/-- The trace formula as printed in the paper, without taking its real part. -/
def complexSLDPairing (h : PureVector d) (L M : HermitianSpace (d+1)) : ℂ :=
  Matrix.trace (rankOneDensity h.val *
    (toMatrix L * toMatrix M + toMatrix M * toMatrix L)) / 2

theorem complex_sld_formula (h : PureVector d) (A B : tangentSpace h)
    (L M : HermitianSpace (d+1))
    (hL : IsDirectionalSLD h A L) (hM : IsDirectionalSLD h B M) :
    complexSLDPairing h L M = 2 * Matrix.trace (toMatrix A.val * toMatrix B.val) := by
  let P := rankOneDensity h.val
  let a := toMatrix A.val
  let b := toMatrix B.val
  let l := toMatrix L
  let m := toMatrix M
  have ha : P*a+a*P=a := (tangentSpace_mem h A.val).mp A.property
  have ht : Matrix.trace (P*(l*m+m*l)) = (4 : ℝ) • Matrix.trace (a*b) := by
    calc
      _ = Matrix.trace ((P*l+l*P)*m) := by
        simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, Matrix.trace_add]
        rw [Matrix.trace_mul_cycle l P m, Matrix.trace_mul_cycle m l P]
      _ = (2 : ℝ) • Matrix.trace (a*m) := by
        rw [hL, Matrix.smul_mul, Matrix.trace_smul]
      _ = (2 : ℝ) • Matrix.trace ((P*a+a*P)*m) := by rw [ha]
      _ = (2 : ℝ) • Matrix.trace (a*(P*m+m*P)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.trace_add]
        rw [Matrix.trace_mul_cycle P a m, Matrix.trace_mul_cycle m P a]
        congr 1
        ring
      _ = _ := by
        rw [hM, Matrix.mul_smul, Matrix.trace_smul, smul_smul]
        norm_num
        rfl
  change Matrix.trace (P*(l*m+m*l)) / 2 = 2 * Matrix.trace (a*b)
  rw [ht]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem intrinsic_formula (h : PureVector d) (A B : tangentSpace h) :
    (quantumInformation h A B : ℂ) =
      2 * Matrix.trace (toMatrix A.val * toMatrix B.val) := by
  rw [quantumInformation, PureSLDMetric.metricFromSLD_eq,
    ← complex_inner_eq_trace B.val A.val, real_inner_comm B.val A.val]
  push_cast
  rfl

theorem sld_pairing_eq_intrinsic (h : PureVector d) (A B : tangentSpace h)
    (L M : HermitianSpace (d+1))
    (hL : IsDirectionalSLD h A L) (hM : IsDirectionalSLD h B M) :
    complexSLDPairing h L M = (quantumInformation h A B : ℂ) := by
  rw [complex_sld_formula h A B L M hL hM, intrinsic_formula]

theorem sld_choice_independent (h : PureVector d) (A B : tangentSpace h)
    (L M L' M' : HermitianSpace (d+1))
    (hL : IsDirectionalSLD h A L) (hM : IsDirectionalSLD h B M)
    (hL' : IsDirectionalSLD h A L') (hM' : IsDirectionalSLD h B M') :
    complexSLDPairing h L M = complexSLDPairing h L' M' := by
  rw [sld_pairing_eq_intrinsic h A B L M hL hM,
    sld_pairing_eq_intrinsic h A B L' M' hL' hM']

/-- The horizontal tangent matrix `h v* + v h*`. -/
def horizontalMatrix (h : PureVector d) (v : EuclideanSpace ℂ (Fin (d+1))) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  fun i j => h.val i * star (v j) + v i * star (h.val j)

theorem horizontalMatrix_hermitian (h : PureVector d)
    (v : EuclideanSpace ℂ (Fin (d+1))) : (horizontalMatrix h v).IsHermitian := by
  change (horizontalMatrix h v).conjTranspose = horizontalMatrix h v
  ext i j
  simp [horizontalMatrix, Matrix.conjTranspose_apply, mul_comm, add_comm]

theorem horizontalMatrix_tangent (h : PureVector d)
    (v : EuclideanSpace ℂ (Fin (d+1))) (hv : ⟪pureVector h, v⟫_ℂ = 0) :
    rankOneDensity h.val * horizontalMatrix h v +
      horizontalMatrix h v * rankOneDensity h.val = horizontalMatrix h v := by
  have hz : (∑ j, h.val j * star (v j)) = 0 := inner_eq_zero_symm.mp hv
  have hz' : (∑ j, v j * star (h.val j)) = 0 := hv
  have hn : (∑ j, h.val j * star (h.val j)) = 1 := by
    have hh : (∑ j, Complex.normSq (h.val j)) = 1 := h.property
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum,
      hh, Complex.ofReal_one]
  ext i j
  change (∑ k, (h.val i * star (h.val k)) *
      (h.val k * star (v j) + v k * star (h.val j))) +
    (∑ k, (h.val i * star (v k) + v i * star (h.val k)) *
      (h.val k * star (h.val j))) = _
  calc
    _ = h.val i * (∑ k, h.val k * star (h.val k)) * star (v j) +
        h.val i * (∑ k, v k * star (h.val k)) * star (h.val j) +
        (h.val i * (∑ k, h.val k * star (v k)) * star (h.val j) +
          v i * (∑ k, h.val k * star (h.val k)) * star (h.val j)) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ = _ := by rw [hz, hz', hn]; simp [horizontalMatrix]

def horizontalTangent (h : PureVector d) (v : EuclideanSpace ℂ (Fin (d+1)))
    (hv : ⟪pureVector h, v⟫_ℂ = 0) : tangentSpace h :=
  ⟨ofMatrix (horizontalMatrix h v) (horizontalMatrix_hermitian h v),
    (tangentSpace_mem h _).mpr (horizontalMatrix_tangent h v hv)⟩

theorem horizontal_vector (h : PureVector d) (v : EuclideanSpace ℂ (Fin (d+1)))
    (hv : ⟪pureVector h, v⟫_ℂ = 0) : tangentVector h (horizontalTangent h v hv) = v := by
  have hz : (∑ j, h.val j * star (v j)) = 0 := inner_eq_zero_symm.mp hv
  have hn : (∑ j, h.val j * star (h.val j)) = 1 := by
    have hh : (∑ j, Complex.normSq (h.val j)) = 1 := h.property
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum,
      hh, Complex.ofReal_one]
  ext i
  change (∑ j, (h.val i * star (v j) + v i * star (h.val j)) * h.val j) = v i
  calc
    _ = h.val i * (∑ j, h.val j * star (v j)) +
        v i * (∑ j, h.val j * star (h.val j)) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring
    _ = v i := by rw [hz, hn]; simp

theorem horizontal_formula (h : PureVector d) (v : EuclideanSpace ℂ (Fin (d+1)))
    (hv : ⟪pureVector h, v⟫_ℂ = 0) :
    quantumInformation h (horizontalTangent h v hv) (horizontalTangent h v hv) =
      4 * ‖v‖^2 := by
  rw [quantumInformation, pure_metric_horizontal, horizontal_vector]

/-- The coordinate quantum information matrix on a finite tangent family. -/
def coordinateQFI (h : PureVector d) (basis : Fin p → tangentSpace h) :
    Matrix (Fin p) (Fin p) ℝ := fun j k => quantumInformation h (basis j) (basis k)

/-- The matrix from the general SLD definition, allowing arbitrary SLD choices. -/
def coordinateSLDQFI (h : PureVector d) (slds : Fin p → HermitianSpace (d+1)) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k => IntrinsicInformationGeometry.sldPairing h (slds j) (slds k)

theorem coordinate_sld_entries (h : PureVector d) (basis : Fin p → tangentSpace h)
    (slds : Fin p → HermitianSpace (d+1))
    (hslds : ∀ j, IsDirectionalSLD h (basis j) (slds j)) (j k : Fin p) :
    coordinateSLDQFI h slds j k = quantumInformation h (basis j) (basis k) := by
  rw [coordinateSLDQFI,
    IntrinsicInformationGeometry.sldPairing_independent h (basis j) (basis k)
      (slds j) (slds k) (hslds j) (hslds k),
    quantumInformation, PureSLDMetric.metricFromSLD_eq]

theorem coordinate_entries (h : PureVector d) (basis : Fin p → tangentSpace h)
    (j k : Fin p) : coordinateQFI h basis j k =
      2 * (Matrix.trace (toMatrix (basis j).val * toMatrix (basis k).val)).re := by
  rw [coordinateQFI, quantumInformation, PureSLDMetric.metricFromSLD_eq,
    inner_eq_trace, Matrix.trace_mul_comm]

theorem coordinate_contraction (h : PureVector d) (basis : Fin p → tangentSpace h)
    (u w : Fin p → ℝ) :
    quantumInformation h (∑ j, u j • basis j) (∑ k, w k • basis k) =
      ∑ j, ∑ k, u j * coordinateQFI h basis j k * w k := by
  simp [coordinateQFI, quantumInformation, PureSLDMetric.metricFromSLD_eq,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum, mul_comm, mul_left_comm]
  exact Finset.sum_comm

theorem coordinate_contraction_matrix (h : PureVector d)
    (basis : Fin p → tangentSpace h) (slds : Fin p → HermitianSpace (d+1))
    (hslds : ∀ j, IsDirectionalSLD h (basis j) (slds j)) (u w : Fin p → ℝ) :
    quantumInformation h (∑ j, u j • basis j) (∑ k, w k • basis k) =
      u ⬝ᵥ ((coordinateSLDQFI h slds).mulVec w) := by
  rw [coordinate_contraction]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [coordinate_sld_entries h basis slds hslds j k]
  change u j * quantumInformation h (basis j) (basis k) * w k =
    u j * (quantumInformation h (basis j) (basis k) * w k)
  ring

/-- All mathematical clauses of main Proposition 2.1 in one exported theorem.
The coordinate clauses hold for any finite tangent family, so apply in
particular to the tangent basis supplied by a local chart. -/
theorem proposition_2_1 (h : PureVector d) :
    (∀ (A B : tangentSpace h) (L M : HermitianSpace (d+1)),
      IsDirectionalSLD h A L → IsDirectionalSLD h B M →
      complexSLDPairing h L M = (quantumInformation h A B : ℂ)) ∧
    (∀ A B : tangentSpace h, (quantumInformation h A B : ℂ) =
      2 * Matrix.trace (toMatrix A.val * toMatrix B.val)) ∧
    (∀ (v : EuclideanSpace ℂ (Fin (d+1))) (hv : ⟪pureVector h, v⟫_ℂ = 0),
      quantumInformation h (horizontalTangent h v hv) (horizontalTangent h v hv) =
        4 * ‖v‖^2) ∧
    (∀ (p : ℕ) (basis : Fin p → tangentSpace h) (slds : Fin p → HermitianSpace (d+1)),
      (∀ j, IsDirectionalSLD h (basis j) (slds j)) →
      (∀ j k, coordinateSLDQFI h slds j k = quantumInformation h (basis j) (basis k)) ∧
      (∀ u w : Fin p → ℝ,
        quantumInformation h (∑ j, u j • basis j) (∑ k, w k • basis k) =
          u ⬝ᵥ ((coordinateSLDQFI h slds).mulVec w))) := by
  refine ⟨?_, intrinsic_formula h, horizontal_formula h, ?_⟩
  · intro A B L M hL hM
    exact sld_pairing_eq_intrinsic h A B L M hL hM
  · intro p basis slds hslds
    exact ⟨coordinate_sld_entries h basis slds hslds,
      coordinate_contraction_matrix h basis slds hslds⟩

end
end QubitOracle.Paper.PureQuantumInformation
