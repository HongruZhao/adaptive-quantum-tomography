import Mathlib

/-! Covariance computations in the same-record simulations. These are
exact identities and moment statements, independent of the numerical
Monte Carlo results. Finite second moments are explicit. -/
namespace QubitOracle.Paper.EmpiricalCovariance
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {p R : ℕ}

def covarianceMatrix {ι : Type*} (X : Ω → EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j => covariance (fun ω => X ω i) (fun ω => X ω j) μ

theorem covariance_trace (X : Ω → EuclideanSpace ℝ (Fin p))
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    Matrix.trace (covarianceMatrix (μ:=μ) X) =
      ∫ ω, ∑ i, (X ω i - ∫ v, X v i ∂μ)^2 ∂μ := by
  unfold covarianceMatrix Matrix.trace Matrix.diag covariance
  simp only [pow_two,Pi.mul_apply]
  exact (integral_finsetSum Finset.univ (fun i _ =>
    (hX i |>.sub (memLp_const _)).integrable_mul (hX i |>.sub (memLp_const _)))).symm

theorem centered_second_moment (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    ∫ ω, (X ω)^2 ∂μ = covariance X X μ + (∫ ω, X ω ∂μ)^2 := by
  rw [covariance_eq_sub hX hX]
  simp only [pow_two,Pi.mul_apply]
  ring

theorem covariance_basis_change (X : Ω → EuclideanSpace ℝ (Fin p))
    (hX : ∀ i,MemLp (fun ω => X ω i) 2 μ) (B : Matrix (Fin p) (Fin p) ℝ) :
    covarianceMatrix (μ:=μ) (fun ω => WithLp.toLp 2 (B.mulVec (X ω))) =
      B * covarianceMatrix (μ:=μ) X * B.transpose := by
  ext i j
  change covariance (fun ω => ∑ k,B i k*X ω k) (fun ω => ∑ k,B j k*X ω k) μ = _
  rw [covariance_fun_sum_fun_sum (fun k => (hX k).const_mul (B i k))
    (fun k => (hX k).const_mul (B j k))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    Matrix.mul_apply,Matrix.transpose_apply,covarianceMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem covariance_trace_orthogonal_invariant (X : Ω → EuclideanSpace ℝ (Fin p))
    (hX : ∀ i,MemLp (fun ω => X ω i) 2 μ) (B : Matrix (Fin p) (Fin p) ℝ)
    (hB : B.transpose*B=1) :
    Matrix.trace (covarianceMatrix (μ:=μ) (fun ω => WithLp.toLp 2 (B.mulVec (X ω)))) =
      Matrix.trace (covarianceMatrix (μ:=μ) X) := by
  rw [covariance_basis_change X hX B,Matrix.trace_mul_cycle,hB,Matrix.one_mul]

def sampleMean (X : Fin R → EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  (R:ℝ)⁻¹ • ∑ r, X r

def sampleCovariance (X : Fin R → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j => ((R:ℝ)-1)⁻¹ * ∑ r,
    (X r i - sampleMean X i)*(X r j - sampleMean X j)

theorem sample_covariance_trace (X : Fin R → EuclideanSpace ℝ (Fin p)) :
    Matrix.trace (sampleCovariance X) =
      ((R:ℝ)-1)⁻¹ * ∑ r, ‖X r - sampleMean X‖^2 := by
  unfold Matrix.trace Matrix.diag sampleCovariance
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [PiLp.sub_apply,Real.norm_eq_abs,sq_abs]
  simp only [pow_two]

theorem normalized_trace_forces_identity (COV : Matrix (Fin p) (Fin p) ℝ)
    (hpos : (COV-1).PosSemidef) (ht : Matrix.trace COV=p) : COV=1 := by
  apply sub_eq_zero.mp
  apply hpos.trace_eq_zero_iff.mp
  simpa [Matrix.trace_sub,Matrix.trace_one,ht] 

theorem sample_centering_identity (X Y : Fin R → ℝ) (hR : R ≠ 0) :
    (∑ r, (X r-(R:ℝ)⁻¹*∑ s,X s)*(Y r-(R:ℝ)⁻¹*∑ s,Y s)) =
      (∑ r,X r*Y r) - (R:ℝ)⁻¹*(∑ r,X r)*(∑ r,Y r) := by
  have hn : (R:ℝ) ≠ 0 := by exact_mod_cast hR
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hn]
  ring

def scalarSampleCovariance (X Y : Fin R → Ω → ℝ) (ω : Ω) : ℝ :=
  ((R:ℝ)-1)⁻¹ * ∑ r,
    (X r ω-(R:ℝ)⁻¹*∑ s,X s ω)*(Y r ω-(R:ℝ)⁻¹*∑ s,Y s ω)

/-- Identical means and within-replicate covariance, together with
independence across replicates, suffice for the usual R-1 correction.
These assumptions follow from independent, identically distributed
replicate vectors; the covariance conclusion is not assumed. -/
theorem sample_covariance_unbiased (X Y : Fin R → Ω → ℝ)
    (hR : 1 < R) (hX : ∀ r, MemLp (X r) 2 μ) (hY : ∀ r, MemLp (Y r) 2 μ)
    (mx my C : ℝ) (hmeanX : ∀ r, ∫ ω,X r ω ∂μ=mx)
    (hmeanY : ∀ r, ∫ ω,Y r ω ∂μ=my)
    (hsame : ∀ r, covariance (X r) (Y r) μ=C)
    (hind : ∀ r s, r ≠ s → IndepFun (X r) (Y s) μ) :
    ∫ ω, scalarSampleCovariance X Y ω ∂μ=C := by
  have hn : (R:ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hm : (R:ℝ)-1 ≠ 0 := by
    have hh : (1:ℝ) < R := by exact_mod_cast hR
    linarith
  have hSX : MemLp (fun ω => ∑ r,X r ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun r _ => hX r)
  have hSY : MemLp (fun ω => ∑ r,Y r ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun r _ => hY r)
  have hp (r s : Fin R) : ∫ ω,X r ω*Y s ω ∂μ =
      if r=s then C+mx*my else mx*my := by
    by_cases hrs : r=s
    · subst s
      rw [if_pos rfl,← hmeanX r,← hmeanY r,← hsame r,
        covariance_eq_sub (hX r) (hY r)]
      simp only [Pi.mul_apply]
      ring
    · change (∫ ω,(X r*Y s) ω ∂μ)=_
      rw [if_neg hrs,(hind r s hrs).integral_mul_eq_mul_integral
        (hX r).aestronglyMeasurable (hY s).aestronglyMeasurable,hmeanX,hmeanY]
  have hi : ∫ ω,(∑ r,X r ω)*(∑ s,Y s ω) ∂μ =
      (R:ℝ)*C+(R:ℝ)^2*mx*my := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [integral_finsetSum Finset.univ]
    · simp_rw [integral_finsetSum Finset.univ
        (fun s _ => show Integrable (fun ω => X s ω*Y _ ω) μ from
          (hX s).integrable_mul (hY _)),hp]
      simp_rw [show ∀ r s : Fin R, (if r=s then C+mx*my else mx*my) =
        (if r=s then C else 0)+mx*my by intro r s; split_ifs <;> ring]
      simp [Finset.sum_add_distrib]
      ring
    · intro r _
      exact integrable_finsetSum Finset.univ (fun s _ =>
        show Integrable (fun ω => X s ω*Y r ω) μ from (hX s).integrable_mul (hY r))
  have hd : ∫ ω,∑ r,X r ω*Y r ω ∂μ=(R:ℝ)*(C+mx*my) := by
    rw [integral_finsetSum Finset.univ
      (fun r _ => show Integrable (fun ω => X r ω*Y r ω) μ from (hX r).integrable_mul (hY r))]
    simp [hp]
    ring
  have he (ω : Ω) := sample_centering_identity (fun r => X r ω)
    (fun r => Y r ω) (show R ≠ 0 by omega)
  simp only [scalarSampleCovariance,he,integral_const_mul]
  simp only [mul_assoc]
  rw [integral_sub,integral_const_mul,hd,hi]
  · field_simp [hn,hm]
    ring
  · exact integrable_finsetSum Finset.univ (fun r _ => (hX r).integrable_mul (hY r))
  · exact (hSX.integrable_mul hSY).const_mul _

/-- The R-1 covariance formula for genuinely independent, identically
distributed replicate vectors. The common covariance is derived from
the identical laws, rather than supplied as a covariance hypothesis. -/
theorem iid_vector_sample_covariance_unbiased
    (X : Fin R → Ω → EuclideanSpace ℝ (Fin p))
    (Z : Ω → EuclideanSpace ℝ (Fin p)) (hR : 1 < R)
    (hind : iIndepFun X μ) (hident : ∀ r, IdentDistrib (X r) Z μ μ)
    (hZ : ∀ i, MemLp (fun ω => Z ω i) 2 μ) (i j : Fin p) :
    (∫ ω,sampleCovariance (fun r => X r ω) i j ∂μ) =
      covarianceMatrix (μ:=μ) Z i j := by
  have hid (r : Fin R) (k : Fin p) :
      IdentDistrib (fun ω => X r ω k) (fun ω => Z ω k) μ μ :=
    (hident r).comp (EuclideanSpace.proj k).continuous.measurable
  have hm (r : Fin R) (k : Fin p) : MemLp (fun ω => X r ω k) 2 μ :=
    (hid r k).memLp_iff.mpr (hZ k)
  have hc (r : Fin R) : covariance (fun ω => X r ω i) (fun ω => X r ω j) μ =
      covarianceMatrix (μ:=μ) Z i j := by
    rw [covarianceMatrix,covariance_eq_sub (hm r i) (hm r j),
      covariance_eq_sub (hZ i) (hZ j),(hid r i).integral_eq,(hid r j).integral_eq]
    congr 1
    simpa only [Pi.mul_apply,Function.comp_def] using
      ((hident r).comp (show Measurable (fun x : EuclideanSpace ℝ (Fin p) =>
        x i*x j) from by fun_prop)).integral_eq
  have hi (r s : Fin R) (hrs : r ≠ s) :
      IndepFun (fun ω => X r ω i) (fun ω => X s ω j) μ :=
    (hind.indepFun hrs).comp (EuclideanSpace.proj i).continuous.measurable
      (EuclideanSpace.proj j).continuous.measurable
  simpa only [sampleCovariance,sampleMean,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul,
    scalarSampleCovariance] using
    sample_covariance_unbiased (fun r ω => X r ω i) (fun r ω => X r ω j)
      hR (fun r => hm r i) (fun r => hm r j) _ _ _
      (fun r => (hid r i).integral_eq) (fun r => (hid r j).integral_eq) hc hi

end
end QubitOracle.Paper.EmpiricalCovariance
