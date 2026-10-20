import QubitOracle.AdaptiveDesign.ExplorationRate
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency

/-! Quantitative response law under the literal history-dependent Born kernel. -/
namespace QubitOracle.AdaptiveDesign.ExplorationRate
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section

lemma weight_tendsto_zero : Tendsto
    (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)).comp ht using 1 <;> norm_num [Function.comp_def]

variable {Theta Action Outcome E : Type*}
variable [MeasurableSpace Action] [MeasurableSpace Outcome]
variable [Fintype Outcome] [MeasurableSingletonClass Outcome]
variable [StandardBorelSpace Outcome] [Nonempty Outcome]
theorem actualResponse_threeQuarter_ae_tendsto_zero
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → ℝ)
    (hcenter : ∀ action, ∫ y, centered action y ∂protocol.response theta action = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto
        (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) *
          ∑ t ∈ Finset.range n, actualResponse protocol centered t path)
        atTop (𝓝 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let shifted : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | n + 1, path => actualResponse protocol centered (n + 1) path
  have hadapted : StronglyAdapted MeasureTheory.Filtration.piLE shifted := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol centered (n + 1)
  have hzero : shifted 0 = 0 := rfl
  have hcentered (n : ℕ) : μ[shifted (n + 1) | MeasureTheory.Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta centered hcenter C hbound n
  have hbounded (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖shifted n path‖ ≤ C := by
    cases n with
    | zero => simpa [shifted] using hC
    | succ n => exact hbound _ _
  have hraw := bounded_sum_threeQuarter_ae
    μ MeasureTheory.Filtration.piLE shifted hadapted hzero hcentered C hC hbounded
  have hsum (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ t ∈ Finset.range n, actualResponse protocol centered t path) =
        (∑ t ∈ Finset.range (n + 1), shifted t path) +
          (actualResponse protocol centered 0 path - actualResponse protocol centered n path) := by
    have hleft := Finset.sum_range_succ
      (fun t => actualResponse protocol centered t path) n
    have hright := Finset.sum_range_succ'
      (fun t => actualResponse protocol centered t path) n
    rw [Finset.sum_range_succ']
    simp only [shifted, add_zero]
    linarith
  filter_upwards [hraw] with path hpath
  have hendpoint : Tendsto
      (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) *
        (actualResponse protocol centered 0 path - actualResponse protocol centered n path))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => ?_)
      (by simpa using (weight_tendsto_zero.mul_const (2*C)))
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    calc
      ‖actualResponse protocol centered 0 path - actualResponse protocol centered n path‖ ≤
          ‖actualResponse protocol centered 0 path‖ + ‖actualResponse protocol centered n path‖ :=
        norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound _ _) (hbound _ _)
      _ = 2 * C := by ring
  simpa only [hsum, mul_add, add_zero] using hpath.add hendpoint

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem actualVectorResponse_threeQuarter_ae_tendsto_zero
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → E)
    (hcenter : ∀ action, ∫ y, centered action y ∂protocol.response theta action = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto
        (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) •
          ∑ t ∈ Finset.range n, actualVectorResponse protocol centered t path)
        atTop (𝓝 0) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hcoordinate (i : Fin (Module.finrank ℝ E)) :
      ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
        Tendsto
          (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) * ∑ t ∈ Finset.range n,
            ⟪b i, actualVectorResponse protocol centered t path⟫_ℝ)
          atTop (𝓝 0) := by
    apply actualResponse_threeQuarter_ae_tendsto_zero protocol theta
      (fun action outcome => ⟪b i, centered action outcome⟫_ℝ)
    · intro action
      rw [integral_inner Integrable.of_finite, hcenter action, inner_zero_right]
    · exact hC
    · intro action outcome
      calc
        ‖⟪b i, centered action outcome⟫_ℝ‖ ≤ ‖b i‖ * ‖centered action outcome‖ :=
          norm_inner_le_norm _ _
        _ = ‖centered action outcome‖ := by rw [b.norm_eq_one, one_mul]
        _ ≤ C := hbound action outcome
  have hall : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      ∀ i : Fin (Module.finrank ℝ E),
        Tendsto
          (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) * ∑ t ∈ Finset.range n,
            ⟪b i, actualVectorResponse protocol centered t path⟫_ℝ)
          atTop (𝓝 0) := ae_all_iff.2 hcoordinate
  filter_upwards [hall] with path hpath
  have hsum := tendsto_finset_sum Finset.univ
    (fun i _ => (hpath i).smul_const (b i))
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr',
    zero_smul, Finset.sum_const_zero] using hsum


end
end QubitOracle.AdaptiveDesign.ExplorationRate
