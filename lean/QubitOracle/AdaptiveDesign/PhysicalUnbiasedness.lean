import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.PureChartDomain
import Mathlib.Analysis.Matrix.Order

/-! An unbiased physical estimate of a pure state must equal that state
on every outcome of positive probability. -/
namespace QubitOracle.AdaptiveDesign.PhysicalUnbiasedness
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController TangentGLS
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem positive_norm_sq_le_trace_sq {n : ℕ} (A : HermitianSpace n)
    (hp : (toMatrix A).PosSemidef) : ‖A‖^2 ≤ (Matrix.trace (toMatrix A)).re^2 := by
  let M := toMatrix A
  let eigenvals := hp.isHermitian.eigenvalues
  let U := hp.isHermitian.eigenvectorUnitary
  let L := Matrix.diagonal (fun i => (eigenvals i : ℂ))
  have hspec : M = Unitary.conjStarAlgAut ℂ _ U L := hp.isHermitian.spectral_theorem
  have hs : (Matrix.trace (M*M)).re = ∑ i, (eigenvals i)^2 := by
    rw [hspec,← map_mul]
    simp only [Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self,Matrix.one_mul]
    simp [L,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum,pow_two]
  have ht : (Matrix.trace M).re = ∑ i, eigenvals i := by
    rw [hp.isHermitian.trace_eq_sum_eigenvalues]
    simp [eigenvals]
  rw [← real_inner_self_eq_norm_sq,inner_eq_trace]
  change (Matrix.trace (M*M)).re ≤ (Matrix.trace M).re^2
  rw [hs,ht]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hp.eigenvalues_nonneg i)

theorem physical_norm_le_one {n : ℕ} (A : HermitianSpace n)
    (hp : (toMatrix A).PosSemidef) (ht : Matrix.trace (toMatrix A)=1) : ‖A‖ ≤ 1 := by
  have hh := positive_norm_sq_le_trace_sq A hp
  rw [ht] at hh
  norm_num at hh
  nlinarith [norm_nonneg A]

theorem unit_barycenter_degenerate {E Y : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype Y]
    (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y=1)
    (A : Y → E) (hA : ∀ y, ‖A y‖ ≤ 1) (P : E) (hP : ‖P‖=1)
    (hmean : ∑ y, p y • A y=P) (y : Y) (hy : 0 < p y) : A y=P := by
  have henergy : (∑ y, p y*‖A y‖^2) ≤ 1 := by
    calc
      _ ≤ ∑ y, p y := Finset.sum_le_sum (fun y _ => by
        have hsq : ‖A y‖^2 ≤ 1 := by nlinarith [hA y,norm_nonneg (A y)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (hp y)])
      _ = _ := hsum
  have hcross : (∑ y, p y*⟪A y,P⟫_ℝ)=1 := by
    have hh := congrArg (fun x => ⟪x,P⟫_ℝ) hmean
    simpa [sum_inner,real_inner_smul_left,real_inner_self_eq_norm_sq,hP] using hh
  have hs : (∑ y, p y*‖A y-P‖^2) ≤ 0 := by
    have hid : (∑ y, p y*‖A y-P‖^2) =
        (∑ y, p y*‖A y‖^2)+(∑ y, p y)*‖P‖^2-2*(∑ y, p y*⟪A y,P⟫_ℝ) := by
      simp only [norm_sub_sq_real,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid,hsum,hP,hcross]
    nlinarith
  have hterm : p y*‖A y-P‖^2 ≤ 0 := (Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset Y)) => mul_nonneg (hp i) (sq_nonneg ‖A i-P‖))
    (Finset.mem_univ y)).trans hs
  have hsq : ‖A y-P‖^2=0 := (mul_eq_zero.mp
    (le_antisymm hterm (mul_nonneg (hp y) (sq_nonneg _)))).resolve_left hy.ne'
  have hz : ‖A y-P‖=0 := by nlinarith [norm_nonneg (A y-P)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem physical_unbiased_at_pure {d : ℕ} {Y : Type*} [Fintype Y]
    (p : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hsum : ∑ y, p y=1)
    (A : Y → HermitianSpace (d+1))
    (hpos : ∀ y, (toMatrix (A y)).PosSemidef)
    (htrace : ∀ y, Matrix.trace (toMatrix (A y))=1)
    (truth : PureVector d) (hmean : ∑ y, p y • A y=(P2Adaptive.pureParameter d truth).val)
    (y : Y) (hy : 0 < p y) : A y=(P2Adaptive.pureParameter d truth).val :=
  unit_barycenter_degenerate p hp hsum A
    (fun y => physical_norm_le_one _ (hpos y) (htrace y)) _ (pureParameter_norm truth) hmean y hy

/-- Even allowing arbitrary state-dependent probabilities on the finite
record space, a fixed physical estimator cannot be unbiased at all pure
states. This therefore applies to finite adaptive experiments as well. -/
theorem no_globally_unbiased_physical_estimator {d : ℕ} (hd : 0 < d)
    {Y : Type*} [Fintype Y] (A : Y → HermitianSpace (d+1))
    (hpos : ∀ y, (toMatrix (A y)).PosSemidef)
    (htrace : ∀ y, Matrix.trace (toMatrix (A y))=1) :
    ¬ (∀ truth : PureVector d, ∃ p : Y → ℝ,
      (∀ y, 0 ≤ p y) ∧ (∑ y, p y=1) ∧
      ∑ y, p y • A y=(P2Adaptive.pureParameter d truth).val) := by
  intro hall
  have hsub : Set.range (fun h : PureVector d => (P2Adaptive.pureParameter d h).val) ⊆ Set.range A := by
    rintro P ⟨truth,rfl⟩
    obtain ⟨p,hp,hsum,hmean⟩ := hall truth
    have hex : ∃ y, 0 < p y := by
      by_contra hh
      push_neg at hh
      have hs : (∑ y, p y) ≤ 0 := Finset.sum_nonpos (fun y _ => hh y)
      linarith
    obtain ⟨y,hy⟩ := hex
    exact ⟨y,physical_unbiased_at_pure p hp hsum A hpos htrace truth hmean y hy⟩
  exact (pureProjectors_infinite d hd) ((Set.finite_range A).subset hsub)

end
end QubitOracle.AdaptiveDesign.PhysicalUnbiasedness
