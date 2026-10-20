import QubitOracle.AdaptiveDesign.GeneralBoundedMartingaleCLT
import QubitOracle.AdaptiveDesign.MartingaleCharacteristicBounds
import QubitOracle.Paper.MartingaleCLT
/-! The matrix form of the supplement's Gaussian-limit lemma, including
positive semidefinite (possibly singular) limiting covariance matrices. -/
namespace QubitOracle.AdaptiveDesign.MartingaleCharacteristic
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condExp_finite_linear_sum {ι : Type*} [Fintype ι]
    {m : MeasurableSpace Ω} (a : ι → ℝ) (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ) :
    μ[(fun ω => ∑ i, a i*Y i ω) | m] =ᵐ[μ] fun ω => ∑ i, a i*μ[Y i | m] ω := by
  letI : MeasurableSpace Ω := mΩ
  have hs := condExp_finsetSum (s:=Finset.univ) (fun i _ => (hY i).const_mul (a i)) m
  have hi := ae_all_iff.mpr (fun i => condExp_smul (μ:=μ) (a i) (Y i) m)
  filter_upwards [hs,hi] with ω hsω hiω
  have he : (∑ i, fun ω => a i*Y i ω) = (fun ω => ∑ i, a i*Y i ω) := by funext ω; simp
  rw [he] at hsω
  rw [hsω]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact hiω i

variable {I : Type} [Fintype I] [DecidableEq I]

def conditionalCovariance (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (k : ℕ) (ω : Ω) : Matrix I I ℝ :=
  fun i j => μ[fun ω => X k ω i*X k ω j | F k] ω

theorem inner_sq_expansion (u x : EuclideanSpace ℝ I) :
    ⟪u,x⟫_ℝ^2 = ∑ ij : I×I, (u ij.1*u ij.2)*(x ij.1*x ij.2) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct,pow_two,Finset.sum_mul,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_expansion (M : Matrix I I ℝ) (u : EuclideanSpace ℝ I) :
    martingaleScoreQuadraticForm M u = ∑ ij : I×I, (u ij.1*u ij.2)*M ij.1 ij.2 := by
  simp only [martingaleScoreQuadraticForm,dotProduct,Matrix.mulVec,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem projected_variance_eq (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (C : ℝ) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (u : EuclideanSpace ℝ I) (k : ℕ) :
    variance (μ:=μ) F (fun k ω => ⟪u,X k ω⟫_ℝ) k =ᵐ[μ]
      fun ω => martingaleScoreQuadraticForm (conditionalCovariance (μ:=μ) F X k ω) u := by
  have hi (ij : I×I) : Integrable (fun ω => X k ω ij.1*X k ω ij.2) μ := by
    have hcoord (i : I) : StronglyMeasurable (fun ω => X k ω i) :=
      (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable ((ha k).mono (F.le (k+1)))
    apply Integrable.of_bound ((hcoord ij.1).mul (hcoord ij.2)).aestronglyMeasurable (C^2)
    apply Eventually.of_forall
    intro ω
    change ‖X k ω ij.1*X k ω ij.2‖ ≤ C^2
    rw [norm_mul,pow_two]
    have hi := (PiLp.norm_apply_le (X k ω) ij.1).trans (hb k ω)
    have hj := (PiLp.norm_apply_le (X k ω) ij.2).trans (hb k ω)
    exact mul_le_mul hi hj (norm_nonneg _) ((norm_nonneg _).trans hi)
  have h := condExp_finite_linear_sum (μ:=μ) (m:=F k)
    (fun ij : I×I => u ij.1*u ij.2) (fun ij ω => X k ω ij.1*X k ω ij.2) hi
  simpa only [variance,inner_sq_expansion,quadratic_expansion,conditionalCovariance] using h

/-- Literal conditional covariance matrices tend to `M`. Since the
increments are conditionally centered, these are also conditional second
moments. The conclusion is the ordinary weak Gaussian limit. -/
theorem vector_clt_of_covariance (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (M : Matrix I I ℝ) (hM : M.PosSemidef)
    (hvar : ∀ᵐ ω ∂μ, Tendsto (fun k => conditionalCovariance (μ:=μ) F X k ω) atTop (𝓝 M)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, X k ω)
      atTop id (fun _ => μ) (multivariateGaussian 0 M) := by
  apply vector_clt F X ha hc C hC hb M hM
  intro u
  have he := ae_all_iff.mpr (fun k => projected_variance_eq (μ:=μ) F X ha C hb u k)
  filter_upwards [hvar,he] with ω hω heω
  have hq : Continuous (fun A : Matrix I I ℝ => martingaleScoreQuadraticForm A u) := by
    simp only [quadratic_expansion]
    fun_prop
  have ht := hq.continuousAt.tendsto.comp hω
  exact ht.congr (fun k => (heω k).symm)

/-- The usual almost-everywhere boundedness convention suffices.
Changing increments on null sets changes neither the adaptive conditional
moments nor the distributions of their finite sums. -/
theorem vector_clt_of_ae_bounded_covariance (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ C)
    (M : Matrix I I ℝ) (hM : M.PosSemidef)
    (hvar : ∀ᵐ ω ∂μ, Tendsto (fun k => conditionalCovariance (μ:=μ) F X k ω) atTop (𝓝 M)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, X k ω)
      atTop id (fun _ => μ) (multivariateGaussian 0 M) := by
  classical
  let Y := fun n ω => if ‖X n ω‖ ≤ C then X n ω else 0
  have hYa (n : ℕ) : StronglyMeasurable[F (n+1)] (Y n) :=
    StronglyMeasurable.ite (measurableSet_le (ha n).norm.measurable measurable_const)
      (ha n) stronglyMeasurable_const
  have he (n : ℕ) : Y n =ᵐ[μ] X n := by
    filter_upwards [hb n] with ω hω
    simp [Y,hω]
  have hYb (n : ℕ) (ω : Ω) : ‖Y n ω‖ ≤ C := by
    dsimp [Y]
    split_ifs with h
    · exact h
    · simpa using hC
  have hYc (n : ℕ) : μ[Y n | F n] =ᵐ[μ] 0 := (condExp_congr_ae (he n)).trans (hc n)
  have hcov (n : ℕ) : conditionalCovariance (μ:=μ) F Y n =ᵐ[μ] conditionalCovariance (μ:=μ) F X n := by
    have hij (i j : I) : μ[fun ω => Y n ω i*Y n ω j | F n] =ᵐ[μ]
        μ[fun ω => X n ω i*X n ω j | F n] := by
      apply condExp_congr_ae
      filter_upwards [he n] with ω hω
      rw [hω]
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hij i))] with ω hω
    ext i j
    exact hω i j
  have hYvar : ∀ᵐ ω ∂μ, Tendsto (fun k => conditionalCovariance (μ:=μ) F Y k ω) atTop (𝓝 M) := by
    filter_upwards [hvar,ae_all_iff.mpr hcov] with ω hω heω
    exact hω.congr (fun k => (heω k).symm)
  have hclt := vector_clt_of_covariance F Y hYa hYc C hC hYb M hM hYvar
  apply hclt.congr _ (EventuallyEq.refl _ _)
  intro n
  filter_upwards [ae_all_iff.mpr he] with ω hω
  simp only [hω]

end
end QubitOracle.AdaptiveDesign.MartingaleCharacteristic
