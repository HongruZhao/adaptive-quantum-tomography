import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1PositiveBatches
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedCLT
import QubitOracle.AdaptiveDesign.P1WeightedConsistency
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedCovariance
import QubitOracle.AdaptiveDesign.P1WeightedGeometry
import QubitOracle.AdaptiveDesign.P1WeightedInformation
import QubitOracle.AdaptiveDesign.P1WeightedLimits
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
/-! Gaussian limits for the literal, all-observation P1 ridge estimator.
The random inverse Gram and the ridge bias are handled by Slutsky's theorem. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩
local instance : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
local instance : TopologicalSpace.PseudoMetrizableSpace Mat :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
local instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
local instance : MeasurableSpace Mat := borel Mat
local instance : BorelSpace Mat := ⟨rfl⟩
local instance : BorelSpace (Mat × Vector) := inferInstance

theorem matrixMap_mul (A B : Mat) (x : Vector) :
    matrixMap (A*B) x = matrixMap A (matrixMap B x) := by
  simp [matrixMap,Matrix.toEuclideanLin_apply,Matrix.mulVec_mulVec]

theorem matrixMap_one (x : Vector) : matrixMap 1 x = x := by
  simp [matrixMap,Matrix.toEuclideanLin_apply]

theorem matrixMap_smul (c : ℝ) (A : Mat) (x : Vector) :
    matrixMap (c • A) x = c • matrixMap A x := by
  ext i
  simp [matrixMap,Matrix.toEuclideanLin_apply,Matrix.smul_mulVec]

theorem matrixMap_continuous : Continuous (fun z : Mat × Vector => matrixMap z.1 z.2) := by
  change Continuous (fun z : Mat × Vector => WithLp.toLp 2 (z.1.mulVec z.2.ofLp))
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem matrix_inv_tendsto {A : ℕ → Mat} {Q : Mat} (hQ : Q.PosDef) (hA : Tendsto A atTop (𝓝 Q)) :
    Tendsto (fun n => (A n)⁻¹) atTop (𝓝 Q⁻¹) := by
  apply (continuousAt_matrix_inv Q _).tendsto.comp hA
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hQ.det_pos.ne')

def normalizedError (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector :=
  Real.sqrt (n:ℝ) • WithLp.toLp 2 (estimate loss ridge refresh n path - θ)

def normalizedGram (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) : Mat :=
  (n:ℝ)⁻¹ • (pathState loss ridge refresh n path).gram

def regressionFactor (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Mat :=
  (normalizedGram loss ridge refresh n path)⁻¹ * meanGramTarget loss θ

def regressionBias (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector :=
  -matrixMap (normalizedGram loss ridge refresh n path)⁻¹
    ((Real.sqrt (n:ℝ))⁻¹ • (ridge • WithLp.toLp 2 θ))

theorem historyStatistic_measurable {E : Type*} [MeasurableSpace E]
    (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (f : RidgeState → E) :
    Measurable (fun path => f (pathState loss ridge refresh n path)) :=
  (measurable_of_countable (fun history => f (historyState loss ridge refresh history))).comp
    (measurable_adaptiveInfinitePathPrefix n)

theorem regressionPair_measurable (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ) (n : ℕ) :
    Measurable (fun path => (regressionFactor loss ridge refresh θ n path,
      regressionBias loss ridge refresh θ n path)) :=
  historyStatistic_measurable loss ridge refresh n (fun state =>
    (((n:ℝ)⁻¹ • state.gram)⁻¹ * meanGramTarget loss θ,
      -matrixMap ((n:ℝ)⁻¹ • state.gram)⁻¹ ((Real.sqrt (n:ℝ))⁻¹ • (ridge • WithLp.toLp 2 θ))))

theorem regressionPair_tendsto (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => (regressionFactor loss ridge refresh θ.1 n path,
        regressionBias loss ridge refresh θ.1 n path)) atTop (𝓝 ((1:Mat),(0:Vector))) := by
  filter_upwards [observedGram_tendsto loss ridge hr refresh hrefresh θ hθ] with path hp
  have hi := matrix_inv_tendsto (meanGram_posDef loss θ.1 hθ) hp
  have hf := hi.mul_const (meanGramTarget loss θ.1)
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (meanGram_posDef loss θ.1 hθ).det_pos.ne')] at hf
  have hz : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹ • (ridge • WithLp.toLp 2 θ.1 : Vector)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 (0:ℝ)) := by
      simpa using constant_div_sqrt_nat_tendsto_zero 1
    simpa using h0.smul_const (ridge • WithLp.toLp 2 θ.1 : Vector)
  have hb := (matrixMap_continuous.continuousAt.tendsto.comp (hi.prodMk_nhds hz)).neg
  simpa only [Function.comp_def,map_zero,neg_zero,regressionFactor,regressionBias,normalizedGram] using hf.prodMk_nhds hb

theorem normalizedError_decomposition (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) (n : ℕ) (path : Path) :
    normalizedError loss ridge refresh θ n path =
      matrixMap (regressionFactor loss ridge refresh θ n path) (influenceSum loss ridge refresh θ n path) +
        regressionBias loss ridge refresh θ n path := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedError,regressionFactor,regressionBias,normalizedGram,influenceSum]
  have hnpos : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hG : (normalizedGram loss ridge refresh n path).PosDef := by
    unfold normalizedGram
    rw [pathState_gram]
    exact (ridge_posDef ridge hr _ n).smul (by positivity)
  have hGi := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  have hQi := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (meanGram_posDef loss θ hθ).det_pos.ne')
  have hnscale : (n:ℝ)⁻¹ * Real.sqrt (n:ℝ) = (Real.sqrt (n:ℝ))⁻¹ := by
    have hs := Real.sq_sqrt hnpos.le
    have hspos := Real.sqrt_pos.mpr hnpos
    field_simp
    nlinarith
  have he : matrixMap (normalizedGram loss ridge refresh n path)
      (normalizedError loss ridge refresh θ n path) =
      (Real.sqrt (n:ℝ))⁻¹ • (∑ t ∈ Finset.range n,
        residual θ (actualAction (policy loss ridge refresh) t path) (path t)) -
      (Real.sqrt (n:ℝ))⁻¹ • (ridge • WithLp.toLp 2 θ) := by
    rw [normalizedGram,normalizedError,matrixMap_smul,map_smul,smul_smul,hnscale]
    change _ • ((pathState loss ridge refresh n path).gram.toEuclideanLin _) = _
    rw [normal_error loss ridge hr,smul_sub]
  have hlin := congrArg (matrixMap (normalizedGram loss ridge refresh n path)⁻¹) he
  rw [← matrixMap_mul,hGi,matrixMap_one,map_sub] at hlin
  rw [hlin,regressionBias,regressionFactor,matrixMap_mul,influenceSum]
  simp only [influence,← map_sum,← map_smul]
  simp only [← matrixMap_mul,Matrix.mul_assoc,hQi,mul_one,sub_eq_add_neg]

/-- Actual ridge least squares is asymptotically efficient for both P1 designs.
No estimator normality or covariance convergence is assumed. -/
theorem estimate_normal (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    TendstoInDistribution (normalizedError loss ridge refresh θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (multivariateGaussian 0 (covarianceTarget loss θ.1)) := by
  let Y := fun n path => ((fun ij : Fin 3 × Fin 3 => regressionFactor loss ridge refresh θ.1 n path ij.1 ij.2),
    regressionBias loss ridge refresh θ.1 n path)
  let c : ((Fin 3 × Fin 3 → ℝ) × Vector) := ((fun ij => (1:Mat) ij.1 ij.2),0)
  have hYm : ∀ n, Measurable (Y n) := by
    intro n
    have hf : Continuous (fun z : Mat × Vector => ((fun ij : Fin 3 × Fin 3 => z.1 ij.1 ij.2),z.2)) := by fun_prop
    exact hf.measurable.comp (regressionPair_measurable loss ridge refresh θ.1 n)
  have hYae : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => Y n path) atTop (𝓝 c) := by
    filter_upwards [regressionPair_tendsto loss ridge hr refresh hrefresh θ hθ] with path hp
    have hf : Continuous (fun z : Mat × Vector => ((fun ij : Fin 3 × Fin 3 => z.1 ij.1 ij.2),z.2)) := by fun_prop
    exact hf.continuousAt.tendsto.comp hp
  have hY := tendstoInMeasure_of_tendsto_ae (fun n => (hYm n).aestronglyMeasurable) hYae
  have hpair := TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    (influenceSum loss ridge refresh θ.1) Y id
    (influenceSum_clt loss ridge hr refresh hrefresh θ hθ) hY (fun n => (hYm n).aemeasurable)
  have hcont : Continuous (fun z : Vector × ((Fin 3 × Fin 3 → ℝ) × Vector) =>
      matrixMap (fun i j => z.2.1 (i,j)) z.1 + z.2.2) := by
    have harg : Continuous (fun z : Vector × ((Fin 3 × Fin 3 → ℝ) × Vector) =>
        ((fun i j => z.2.1 (i,j) : Mat),z.1)) :=
      (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply (i,j)).comp continuous_snd.fst).prodMk continuous_fst
    exact (matrixMap_continuous.comp harg).add continuous_snd.snd
  have hc := hpair.continuous_comp hcont
  convert hc using 1
  · funext n path
    exact normalizedError_decomposition loss ridge hr refresh θ.1 hθ n path
  · funext x
    change x = matrixMap (1:Mat) x + 0
    rw [matrixMap_one,add_zero]

/-- Both P1 algorithms, with any prescribed positive finite batches. -/
theorem positive_batches_normal (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    TendstoInDistribution (normalizedError loss ridge (P1.batchRefresh m) θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ)
      (multivariateGaussian 0 (informationTarget loss θ.1)⁻¹) := by
  rw [← covariance_eq_information_inv loss θ.1 hθ]
  exact estimate_normal loss ridge hr (P1.batchRefresh m) (P1.batchRefresh_unbounded m hm) θ hθ

end
end QubitOracle.AdaptiveDesign.P1Weighted
