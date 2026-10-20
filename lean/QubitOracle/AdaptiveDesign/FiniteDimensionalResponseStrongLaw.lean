import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates

namespace QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped BigOperators Topology
noncomputable section
variable {Theta Action Outcome E : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem actualResponse_average_ae_normed
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse p g k path)
        atTop (𝓝 0) := by
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  have hc (i : Fin (Module.finrank ℝ E)) := actualResponse_average_ae_tendsto_zero p theta
    (fun a y => coordinate i (g a y))
    (fun a => by rw [(coordinate i).integral_comp_comm Integrable.of_finite,hm a,map_zero])
    (‖coordinate (E:=E) i‖*C) (mul_nonneg (norm_nonneg (coordinate (E:=E) i)) hC)
    (fun a y => ((coordinate i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg _)))
  filter_upwards [ae_all_iff.2 hc] with path hp
  have hs := tendsto_finsetSum Finset.univ (fun i _ => (hp i).smul_const ((Module.finBasis ℝ E) i))
  have he (n : ℕ) : (∑ i, ((n:ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      coordinate i (actualVectorResponse p g k path)) • (Module.finBasis ℝ E) i) =
      (n:ℝ)⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse p g k path := by
    simpa only [map_smul,map_sum,smul_eq_mul] using sum_coordinate
      ((n:ℝ)⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse p g k path)
  change Tendsto (fun n : ℕ => ∑ i, ((n:ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      coordinate i (actualVectorResponse p g k path)) • (Module.finBasis ℝ E) i)
    atTop (𝓝 (∑ i : Fin (Module.finrank ℝ E), (0:ℝ) • (Module.finBasis ℝ E) i)) at hs
  simpa only [he, zero_smul, Finset.sum_const_zero] using hs

end
end QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates
