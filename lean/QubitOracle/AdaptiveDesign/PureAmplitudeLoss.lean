import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.TwoBasis
/-! Exact physical pure-state losses in the amplitude chart. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem reference_overlap (d : ℕ) (A : HermitianSpace (d+1)) :
    ⟪(pureParameter d (knownReference d)).val,A⟫_ℝ = (toMatrix A 0 0).re := by
  simp [inner_eq_trace, pureParameter, knownReference, rankOneDensity,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Pi.single_apply]

theorem referenceCoordinate_norm_sq {d : ℕ} (A : HermitianSpace (d+1))
    (hA : toMatrix A * toMatrix A = toMatrix A) :
    ‖referenceCoordinate d A‖^2 = (toMatrix A 0 0).re - (toMatrix A 0 0).re^2 := by
  have hh (j : Fin (d+1)) : toMatrix A j 0 = star (toMatrix A 0 j) :=
    (congrFun (congrFun (toMatrix_isHermitian A).eq j) 0).symm
  have hi : (toMatrix A 0 0).im = 0 := by
    have := congrArg Complex.im (hh 0)
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have h := congrArg (fun B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (B 0 0).re) hA
  have hs : ∑ j : Fin (d+1), ((toMatrix A 0 j).re^2 + (toMatrix A 0 j).im^2) =
      (toMatrix A 0 0).re := by
    rw [← h]
    simp only [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hh j]
    simp [Complex.mul_re, pow_two]
  simp only [Fin.sum_univ_succ, hi, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_add_distrib] at hs
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (GeneralPOVM.matrixGradient (toMatrix A) i)^2) = _
  simp only [Fintype.sum_sum_type, GeneralPOVM.matrixGradient, neg_sq]
  nlinarith

theorem trueCoordinate_norm_sq {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1))
    (hA : toMatrix A * toMatrix A = toMatrix A) :
    ‖trueCoordinate truth (A-(pureParameter d truth).val)‖^2 =
      ⟪(pureParameter d truth).val,A⟫_ℝ - ⟪(pureParameter d truth).val,A⟫_ℝ^2 := by
  let U := conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
  have hp : (pureParameter d truth).val = U (pureParameter d (knownReference d)).val :=
    (trueFrame_referenceParameter truth).symm
  have hmat : toMatrix (U.symm A) =
      (trueFrame d truth).conjTranspose * toMatrix A * trueFrame d truth := by
    change (trueFrame d truth).conjTranspose * toMatrix A *
      (trueFrame d truth).conjTranspose.conjTranspose = _
    rw [Matrix.conjTranspose_conjTranspose]
  have hi : toMatrix (U.symm A) * toMatrix (U.symm A) = toMatrix (U.symm A) := by
    have hu : trueFrame d truth * (trueFrame d truth).conjTranspose = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (trueFrame_unitary d truth)
    rw [hmat]
    calc
      _ = (trueFrame d truth).conjTranspose * toMatrix A *
          (trueFrame d truth * (trueFrame d truth).conjTranspose) *
          toMatrix A * trueFrame d truth := by noncomm_ring
      _ = (trueFrame d truth).conjTranspose * (toMatrix A * toMatrix A) *
          trueFrame d truth := by rw [hu]; simp [Matrix.mul_assoc]
      _ = _ := by rw [hA]
  have hov : ⟪(pureParameter d truth).val,A⟫_ℝ = (toMatrix (U.symm A) 0 0).re := by
    calc
      _ = ⟪U (pureParameter d (knownReference d)).val,U (U.symm A)⟫_ℝ := by
        rw [U.apply_symm_apply, ← hp]
      _ = _ := by rw [U.inner_map_map, reference_overlap]
  have hc : trueCoordinate truth (A-(pureParameter d truth).val) =
      referenceCoordinate d (U.symm A) := by
    change referenceCoordinate d (U.symm (A-(pureParameter d truth).val)) = _
    rw [hp, map_sub, U.symm_apply_apply, map_sub, referenceCoordinate_reference, sub_zero]
  rw [hc, referenceCoordinate_norm_sq _ hi, ← hov]

theorem amplitudeCoordinates_norm_sq {d : ℕ} (truth h : PureVector d)
    (hp : 0 < ⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ) :
    ‖amplitudeCoordinates truth (pureParameter d h).val‖^2 =
      4*(1-⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ) := by
  have hi : toMatrix (pureParameter d h).val * toMatrix (pureParameter d h).val =
      toMatrix (pureParameter d h).val := pureProjector_idempotent h
  rw [amplitudeCoordinates, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hp.le, trueCoordinate_norm_sq truth _ hi]
  field_simp [hp.ne']
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The physical infidelity law follows from the amplitude CLT and
consistency. The right side is half a chi-square with `2*d` degrees of
freedom, written explicitly as the squared norm of the Gaussian limit. -/
theorem infidelity_clt_of_amplitude_clt {d : ℕ} (truth : PureVector d)
    (h : ℕ → Ω → PureVector d)
    (hm : ∀ n, StronglyMeasurable (fun ω => (pureParameter d (h n ω)).val))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => (pureParameter d (h n ω)).val) atTop
      (𝓝 (pureParameter d truth).val))
    (hclt : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (pureParameter d (h n ω)).val)
      atTop id (fun _ => μ)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)))) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (n:ℝ)*(1-⟪(pureParameter d truth).val,(pureParameter d (h n ω)).val⟫_ℝ))
      atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/4) (fun _ => μ)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  let X := fun (n : ℕ) ω =>
    ‖Real.sqrt (n:ℝ) • amplitudeCoordinates truth (pureParameter d (h n ω)).val‖^2/4
  let Y := fun (n : ℕ) ω => (n:ℝ)*(1-⟪(pureParameter d truth).val,(pureParameter d (h n ω)).val⟫_ℝ)
  have hX : TendstoInDistribution X atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/4)
      (fun _ => μ) (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) :=
    hclt.continuous_comp (g := fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/4) (by fun_prop)
  have hY (n : ℕ) : Measurable (Y n) :=
    measurable_const.mul (measurable_const.sub (stronglyMeasurable_const.inner (hm n)).measurable)
  apply tendstoInDistribution_of_tendstoInMeasure_sub Y _ hX _ (fun n => (hY n).aemeasurable)
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((hY n).aemeasurable.sub (hX.forall_aemeasurable n)).aestronglyMeasurable)
  filter_upwards [hc] with ω hω
  have ho : Tendsto (fun n => ⟪(pureParameter d truth).val,(pureParameter d (h n ω)).val⟫_ℝ)
      atTop (𝓝 (1:ℝ)) := by
    simpa only [real_inner_self_eq_norm_sq, pureParameter_norm, one_pow] using
      (tendsto_const_nhds (x := (pureParameter d truth).val)).inner (𝕜 := ℝ) hω
  have hp := ho.eventually (eventually_gt_nhds (show (0:ℝ) < 1 by norm_num))
  apply tendsto_const_nhds.congr'
  filter_upwards [hp] with n hn
  change 0 = Y n ω-X n ω
  have he : X n ω = Y n ω := by
    dsimp only [X,Y]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg n), amplitudeCoordinates_norm_sq truth (h n ω) hn]
    ring
  rw [he, sub_self]

/-- The physical Frobenius law, with no moment or unbiasedness premise. -/
theorem frobenius_clt_of_amplitude_clt {d : ℕ} (truth : PureVector d)
    (h : ℕ → Ω → PureVector d)
    (hm : ∀ n, StronglyMeasurable (fun ω => (pureParameter d (h n ω)).val))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => (pureParameter d (h n ω)).val) atTop
      (𝓝 (pureParameter d truth).val))
    (hclt : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (pureParameter d (h n ω)).val)
      atTop id (fun _ => μ)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)))) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (n:ℝ)*‖(pureParameter d (h n ω)).val-(pureParameter d truth).val‖^2)
      atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/2) (fun _ => μ)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have H := (infidelity_clt_of_amplitude_clt truth h hm hc hclt).continuous_comp
    (g := fun x : ℝ => 2*x) (by fun_prop)
  apply H.congr
  · intro n
    exact Eventually.of_forall fun ω => by
      dsimp only [Function.comp_def]
      rw [norm_sub_sq_real, pureParameter_norm, pureParameter_norm, real_inner_comm]
      ring
  · exact Eventually.of_forall fun z => by dsimp only [Function.comp_def]; ring

end
end QubitOracle.AdaptiveDesign.TangentGLS
