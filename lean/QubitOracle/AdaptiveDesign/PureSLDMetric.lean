import QubitOracle.AdaptiveDesign.TangentGLSCoordinates

/-! The symmetric-logarithmic-derivative metric on pure-state tangents.
These are identities of actual Hermitian matrices, not a postulated
information matrix. -/
namespace QubitOracle.AdaptiveDesign.PureSLDMetric
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open scoped InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable {d : ℕ}

def pureSLD (h : PureVector d) (A : tangentSpace h) : HermitianSpace (d+1) := (2:ℝ) • A.val

theorem sld_equation (h : PureVector d) (A : tangentSpace h) :
    (1/2:ℝ) • (rankOneDensity h.val * toMatrix (pureSLD h A)+
      toMatrix (pureSLD h A)*rankOneDensity h.val) = toMatrix A.val := by
  simp only [pureSLD, toMatrix_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul]
  norm_num
  exact (tangentSpace_mem h A.val).mp A.property

def metricFromSLD (h : PureVector d) (A B : tangentSpace h) : ℝ :=
  (Matrix.trace (rankOneDensity h.val *
    (toMatrix (pureSLD h A)*toMatrix (pureSLD h B)+
      toMatrix (pureSLD h B)*toMatrix (pureSLD h A)))).re/2

theorem metricFromSLD_eq (h : PureVector d) (A B : tangentSpace h) :
    metricFromSLD h A B = 2*⟪A.val,B.val⟫_ℝ := by
  let P := rankOneDensity h.val
  let a := toMatrix A.val
  let b := toMatrix B.val
  have hA : P*a+a*P = a := (tangentSpace_mem h A.val).mp A.property
  have ht : Matrix.trace (a*b) = Matrix.trace (P*a*b)+Matrix.trace (P*b*a) := by
    calc
      _ = Matrix.trace ((P*a+a*P)*b) := by rw [hA]
      _ = Matrix.trace (P*a*b)+Matrix.trace (a*P*b) := by rw [Matrix.add_mul, Matrix.trace_add]
      _ = _ := by rw [Matrix.trace_mul_cycle a P b, Matrix.trace_mul_cycle b a P]
  have htr : (Matrix.trace (a*b)).re = ⟪A.val,B.val⟫_ℝ := by
    rw [inner_eq_trace, Matrix.trace_mul_comm]
  unfold metricFromSLD pureSLD
  simp only [toMatrix_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have ht' := congrArg Complex.re ht
  simp only [Complex.add_re] at ht'
  change (2*2*(Matrix.trace (P*(a*b))).re+2*2*(Matrix.trace (P*(b*a))).re)/2 = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  linarith

theorem trueLift_mem (h : PureVector d) (u : EuclideanSpace ℝ (TangentIndex d)) :
    trueLift h u ∈ tangentSpace h := by
  have he := trueLift_coordinate h (trueLift h u)
  rw [trueCoordinate_lift] at he
  rw [he]
  exact (tangentSpace h).starProjection_apply_mem _

def normalizedLift (h : PureVector d) (u : EuclideanSpace ℝ (TangentIndex d)) : tangentSpace h :=
  ⟨(1/2:ℝ) • trueLift h u, (tangentSpace h).smul_mem _ (trueLift_mem h u)⟩

/-- The factor one half in the amplitude parametrization makes its
quantum information at the centre exactly the identity. -/
theorem normalized_metric (h : PureVector d) (u v : EuclideanSpace ℝ (TangentIndex d)) :
    metricFromSLD h (normalizedLift h u) (normalizedLift h v) = ⟪u,v⟫_ℝ := by
  rw [metricFromSLD_eq]
  change 2*⟪(1/2:ℝ) • trueLift h u,(1/2:ℝ) • trueLift h v⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right, trueLift_inner, trueCoordinate_lift]
  ring

end
end QubitOracle.AdaptiveDesign.PureSLDMetric
