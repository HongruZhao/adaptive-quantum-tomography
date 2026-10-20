import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.Paper.MartingaleCLTConsolidated
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure

/-!
# Bounded centered responses on the actual adaptive path: CLT

The experiment and all increments below are literal adaptive responses.
Martingale differences and Lindeberg are proved from a finite-action mean
identity and a uniform bound. The only remaining stochastic input to this
generic theorem is convergence of the displayed conditional variance;
applications must prove that input from their actual measurement design.
The general scalar CLT uses the existing source-faithful Hall--Heyde atom.
-/

namespace QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Theta Action Outcome I : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome] [Fintype I] [DecidableEq I]

def normalization (n : ℕ) : ℝ := (Real.sqrt (n : ℝ))⁻¹

def problem (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I) : MartingaleCLTProblem I where
  Omega := AdaptiveInfinitePath Outcome
  measurableSpace := inferInstance
  mu := adaptiveInfiniteTrajectoryMeasure protocol theta
  probabilityMeasure := inferInstance
  filtration := fun _ => MeasureTheory.Filtration.piLE
  increment := fun n k path => normalization n • actualVectorResponse protocol g (k+1) path

def projected (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (g : Action → Outcome → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I)
    (n k : ℕ) (path : AdaptiveInfinitePath Outcome) : ℝ :=
  normalization n * actualResponse protocol (fun a y => ⟪u, g a y⟫_ℝ) (k+1) path

theorem projected_eq (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (u : EuclideanSpace ℝ I) :
    (problem protocol theta g).projectedIncrement u = projected protocol g u := by
  funext n k path
  simp only [MartingaleCLTProblem.projectedIncrement, problem,
    inner_smul_right, projected, actualVectorResponse, actualResponse]

theorem projected_bound (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (g : Action → Outcome → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I)
    (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n k : ℕ)
    (path : AdaptiveInfinitePath Outcome) :
    ‖projected protocol g u n k path‖ ≤ normalization n * (‖u‖ * C) := by
  have hn : 0 ≤ normalization n := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [projected, norm_mul, Real.norm_eq_abs, abs_of_nonneg hn]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbound _ _) (norm_nonneg u))

theorem projected_measurable (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (g : Action → Outcome → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I) (n k : ℕ) :
    StronglyMeasurable[MeasureTheory.Filtration.piLE (k+1)]
      (projected protocol g u n k) :=
  (actualResponse_stronglyMeasurable_piLE protocol (fun a y => ⟪u, g a y⟫_ℝ) (k+1)).const_mul _

theorem projected_integrable (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (u : EuclideanSpace ℝ I) (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n k : ℕ) :
    Integrable (projected protocol g u n k) (adaptiveInfiniteTrajectoryMeasure protocol theta) := by
  exact Integrable.of_bound
    ((projected_measurable protocol g u n k).mono
      (MeasureTheory.Filtration.piLE.le (k+1))).aestronglyMeasurable
    (normalization n * (‖u‖ * C)) (ae_of_all _ (projected_bound protocol g u C hbound n k))

theorem projected_memLp_two (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (u : EuclideanSpace ℝ I) (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n k : ℕ) :
    MemLp (projected protocol g u n k) 2 (adaptiveInfiniteTrajectoryMeasure protocol theta) :=
  MemLp.of_bound (projected_integrable protocol theta g u C hbound n k).aestronglyMeasurable
    (normalization n * (‖u‖ * C)) (ae_of_all _ (projected_bound protocol g u C hbound n k))

theorem projected_centered (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (u : EuclideanSpace ℝ I) (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n k : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure protocol theta)[
      projected protocol g u n k | MeasureTheory.Filtration.piLE k]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta] 0 := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  have hc := actualResponse_condExp_zero protocol theta (fun a y => ⟪u, g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite, hmean a, inner_zero_right])
    (‖u‖ * C)
    (fun a y => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hbound a y) (norm_nonneg u))) k
  have hscale := condExp_smul (μ := adaptiveInfiniteTrajectoryMeasure protocol theta)
    (normalization n)
    (actualResponse protocol (fun a y => ⟪u, g a y⟫_ℝ) (k+1))
    (MeasureTheory.Filtration.piLE k)
  change (adaptiveInfiniteTrajectoryMeasure protocol theta)[
    normalization n • actualResponse protocol (fun a y => ⟪u, g a y⟫_ℝ) (k+1) |
      MeasureTheory.Filtration.piLE k] =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta] 0
  simpa only [smul_zero] using hscale.trans (hc.const_smul (normalization n))

theorem projected_martingale (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (u : EuclideanSpace ℝ I) (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n : ℕ) :
    Martingale (martingaleArrayPartialSum (projected protocol g u) n)
      MeasureTheory.Filtration.piLE (adaptiveInfiniteTrajectoryMeasure protocol theta) := by
  let mu := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X := martingaleArrayPartialSum (projected protocol g u) n
  have ha : StronglyAdapted MeasureTheory.Filtration.piLE X := by
    intro t
    have hs := Finset.stronglyMeasurable_sum (Finset.range t) (fun k hk =>
      (projected_measurable protocol g u n k).mono
        (MeasureTheory.Filtration.piLE.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))))
    have heq : X t = ∑ k ∈ Finset.range t, projected protocol g u n k := by
      funext path
      simp [X, martingaleArrayPartialSum]
    rw [heq]
    exact hs
  have hi : ∀ t, Integrable (X t) mu := by
    intro t
    apply Integrable.of_bound ((ha t).mono (MeasureTheory.Filtration.piLE.le t)).aestronglyMeasurable
      ((t : ℝ) * (normalization n * (‖u‖ * C)))
    filter_upwards [] with path
    change ‖∑ k ∈ Finset.range t, projected protocol g u n k path‖ ≤ _
    calc
      _ ≤ ∑ k ∈ Finset.range t, ‖projected protocol g u n k path‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range t, normalization n * (‖u‖ * C) :=
        Finset.sum_le_sum (fun k _ => projected_bound protocol g u C hbound n k path)
      _ = _ := by simp
  apply martingale_nat ha hi
  intro t
  have hc := projected_centered protocol theta g hmean u C hbound n t
  have hself := condExp_of_stronglyMeasurable (MeasureTheory.Filtration.piLE.le t) (ha t) (hi t)
  have hadd := condExp_add (hi t) (projected_integrable protocol theta g u C hbound n t)
    (MeasureTheory.Filtration.piLE t)
  have hrec : X t + projected protocol g u n t = X (t+1) := by
    funext path
    simp [X, martingaleArrayPartialSum, Finset.sum_range_succ]
  calc
    X t =ᵐ[mu] mu[X t | MeasureTheory.Filtration.piLE t] :=
      ae_of_all _ (congrFun hself.symm)
    _ =ᵐ[mu] mu[X t | MeasureTheory.Filtration.piLE t] +
        mu[projected protocol g u n t | MeasureTheory.Filtration.piLE t] := by
      filter_upwards [hc] with path hp
      change mu[projected protocol g u n t | MeasureTheory.Filtration.piLE t] path = 0 at hp
      simp [hp]
    _ =ᵐ[mu] mu[X t + projected protocol g u n t | MeasureTheory.Filtration.piLE t] := hadd.symm
    _ =ᵐ[mu] mu[X (t+1) | MeasureTheory.Filtration.piLE t] := by rw [hrec]

theorem problem_martingale_conditions
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) :
    (problem protocol theta g).IsSquareIntegrableMartingaleDifferenceArray := by
  refine ⟨?_, ?_, fun _ _ => le_rfl⟩
  · intro u n
    rw [projected_eq]
    exact projected_martingale protocol theta g hmean u C hbound n
  · intro u n k
    rw [projected_eq]
    exact projected_memLp_two protocol theta g u C hbound n k

theorem problem_lindeberg
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I)
    (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) :
    (problem protocol theta g).HasConditionalLindeberg := by
  letI : MeasurableSpace (problem protocol theta g).Omega := (problem protocol theta g).measurableSpace
  letI : IsProbabilityMeasure (problem protocol theta g).mu := (problem protocol theta g).probabilityMeasure
  intro u epsilon hepsilon
  have hlim : Tendsto (fun n => normalization n * (‖u‖ * C)) atTop (𝓝 0) := by
    simpa [normalization, div_eq_mul_inv, mul_comm] using constant_div_sqrt_nat_tendsto_zero (‖u‖ * C)
  have hsmall := hlim.eventually (Iio_mem_nhds hepsilon)
  have hz : ∀ᶠ n in atTop,
      hallHeydeArrayConditionalLindeberg
        (problem protocol theta g).mu (problem protocol theta g).filtration
        ((problem protocol theta g).projectedIncrement u) epsilon n = 0 := by
    filter_upwards [hsmall] with n hn
    funext path
    unfold hallHeydeArrayConditionalLindeberg
    apply Finset.sum_eq_zero
    intro k _
    have hzfun : (fun path => if epsilon <
        |(problem protocol theta g).projectedIncrement u n k path|
        then ((problem protocol theta g).projectedIncrement u n k path)^2 else 0) = 0 := by
      funext path
      have hb := projected_bound protocol g u C hbound n k path
      rw [Real.norm_eq_abs] at hb
      rw [projected_eq]
      exact if_neg (not_lt.mpr (hb.trans hn.le))
    rw [hzfun, condExp_zero]
    rfl
  have hc : TendstoInMeasure (problem protocol theta g).mu
      (fun (_ : ℕ) (_ : AdaptiveInfinitePath Outcome) => (0 : ℝ))
      atTop (fun (_ : AdaptiveInfinitePath Outcome) => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_norm]
    intro delta hd
    simpa only [sub_self, norm_zero, not_le.mpr hd,
      Set.setOf_false, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  exact hc.congr' (hz.mono fun n hn => ae_of_all _ (congrFun hn.symm)) EventuallyEq.rfl

/-- Gaussian limits for bounded centered adaptive responses. The covariance
convergence remains explicit and must be verified by the concrete model. -/
theorem scalar_clt_of_covariance
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C)
    (M : Matrix I I ℝ) (hM : M.PosDef)
    (hcov : (problem protocol theta g).ConditionalCovarianceConverges M) :
    (problem protocol theta g).SumConvergesToGaussian M :=
  martingale_score_clt_consolidated (problem protocol theta g) M hM
    (problem_martingale_conditions protocol theta g hmean C hbound)
    (problem_lindeberg protocol theta g C hbound) hcov

theorem actualVectorResponse_measurable
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (g : Action → Outcome → EuclideanSpace ℝ I) (n : ℕ) :
    Measurable (actualVectorResponse protocol g n) := by
  let f : Prefix (Outcome := Outcome) n → EuclideanSpace ℝ I := fun pref =>
    WithLp.toLp 2 (fun i => prefixResponse protocol (fun a y => g a y i) n pref)
  have heq : actualVectorResponse protocol g n = f ∘ Preorder.frestrictLe n := by
    funext path
    ext i
    exact congrFun (actualResponse_eq_prefix protocol (fun a y => g a y i) n) path
  rw [heq]
  exact (measurable_of_countable f).comp (Preorder.measurable_frestrictLe n)

theorem problem_terminal_measurable
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I) (n : ℕ) :
    AEMeasurable ((problem protocol theta g).terminalSum n)
      (adaptiveInfiniteTrajectoryMeasure protocol theta) := by
  change AEMeasurable (fun path => ∑ k ∈ Finset.range n,
    normalization n • actualVectorResponse protocol g (k+1) path) _
  exact (Finset.measurable_sum (Finset.range n) (fun k _ =>
    (actualVectorResponse_measurable protocol g (k+1)).const_smul (normalization n))).aemeasurable

theorem vector_clt_of_covariance
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C)
    (M : Matrix I I ℝ) (hM : M.PosDef)
    (hcov : (problem protocol theta g).ConditionalCovarianceConverges M) :
    (problem protocol theta g).VectorSumConvergesToGaussian M :=
  martingale_score_clt_multivariate_consolidated (problem protocol theta g) M hM
    (problem_martingale_conditions protocol theta g hmean C hbound)
    (problem_lindeberg protocol theta g C hbound) hcov
    (problem_terminal_measurable protocol theta g)

end
end QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT
