import QubitOracle.AdaptiveDesign.TangentGLSBounds

/-! The exact variational meaning of the preliminary nearest-pure
selection. For Hermitian data it maximizes the Rayleigh quotient over
unit vectors. No positivity or spectral-gap hypothesis is used. -/
namespace QubitOracle.AdaptiveDesign.PureMatrixController
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian P2Adaptive TangentGLS
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem projector_distance_sq {d : ℕ} (A : HermitianSpace (d+1)) (h : PureVector d) :
    ‖(pureParameter d h).val-A‖^2 = ‖A‖^2+1-2*⟪(pureParameter d h).val,A⟫_ℝ := by
  rw [norm_sub_sq_real, pureParameter_norm]
  ring

theorem nearest_iff_maximizes_rayleigh {d : ℕ} (A : HermitianSpace (d+1)) (h : PureVector d) :
    (∀ g : PureVector d, ‖rankOneDensity h.val-toMatrix A‖ ≤
      ‖rankOneDensity g.val-toMatrix A‖) ↔
    (∀ g : PureVector d, (GlobalPFSIC.quadratic (toMatrix A) g.val).re ≤
      (GlobalPFSIC.quadratic (toMatrix A) h.val).re) := by
  have he (g : PureVector d) :
      ⟪(pureParameter d g).val,A⟫_ℝ = (GlobalPFSIC.quadratic (toMatrix A) g.val).re := by
    rw [inner_eq_trace]
    exact congrArg Complex.re (trace_mul_projector (toMatrix A) g.val)
  have hn (g : PureVector d) : ‖rankOneDensity g.val-toMatrix A‖ =
      ‖(pureParameter d g).val-A‖ := toMatrix_norm ((pureParameter d g).val-A)
  constructor
  · intro hm g
    have hh := hm g
    rw [hn, hn] at hh
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [projector_distance_sq, projector_distance_sq, he, he] at hsq
    linarith
  · intro hm g
    rw [hn, hn]
    have hh := hm g
    have h1 := projector_distance_sq A h
    have h2 := projector_distance_sq A g
    rw [he] at h1 h2
    nlinarith [norm_nonneg ((pureParameter d h).val-A), norm_nonneg ((pureParameter d g).val-A)]

theorem nearestVector_maximizes_rayleigh {d : ℕ} (A : HermitianSpace (d+1))
    (g : PureVector d) :
    (GlobalPFSIC.quadratic (toMatrix A) g.val).re ≤
      (GlobalPFSIC.quadratic (toMatrix A) (nearestVector d (toMatrix A)).val).re := by
  apply (nearest_iff_maximizes_rayleigh A (nearestVector d (toMatrix A))).mp
    (fun candidate => nearestVector_is_nearest d (toMatrix A) candidate) g

end
end QubitOracle.AdaptiveDesign.PureMatrixController
