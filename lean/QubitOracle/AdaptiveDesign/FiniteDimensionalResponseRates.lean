import QubitOracle.AdaptiveDesign.AdaptiveResponseTightness

/-! Rates in arbitrary finite-dimensional normed spaces. In particular the
bounded adaptive response may be a linear operator, with its operator norm. -/

namespace QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency BoundedResponseQuarterRate
open ProbabilityCalculus AdaptiveResponseTightness
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Theta Action Outcome E : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coordinate (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord i).toContinuousLinearMap

theorem sum_coordinate (x : E) :
    ∑ i, coordinate i x • (Module.finBasis ℝ E) i = x :=
  (Module.finBasis ℝ E).sum_repr x

theorem actualResponse_quarterRate_normed
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) atTop (fun _ => (0 : E)) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := Module.finBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :=
    actualResponse_quarterRate protocol theta (fun a y => coordinate i (g a y))
      (fun a => by rw [(coordinate i).integral_comp_comm Integrable.of_finite, hmean a, map_zero])
      (‖coordinate (E := E) i‖*C) (mul_nonneg (norm_nonneg _) hC)
      (fun a y => ((coordinate i).le_opNorm (g a y)).trans
        (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg _)))
  have hs := ProbabilityZeroAlgebra.finite_sum Finset.univ
    (fun i n path => ((quarterScale n / ((n+1 : ℕ) : ℝ)) *
      ∑ k ∈ Finset.range (n+1), coordinate i (actualVectorResponse protocol g k path)) • b i)
    (fun i _ => ProbabilityZeroAlgebra.smul_fixed (hc i) (b i))
  have heq (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ i, ((quarterScale n / ((n+1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.range (n+1), coordinate i (actualVectorResponse protocol g k path)) • b i) =
      (quarterScale n / ((n+1 : ℕ) : ℝ)) •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path := by
    simpa only [map_smul, map_sum, smul_eq_mul] using sum_coordinate
      ((quarterScale n / ((n+1 : ℕ) : ℝ)) •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path)
  simpa only [heq] using hs

theorem actualResponse_rootTight_normed
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) atTop := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := Module.finBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :=
    actualResponse_rootTight protocol theta (fun a y => coordinate i (g a y))
      (fun a => by rw [(coordinate i).integral_comp_comm Integrable.of_finite, hmean a, map_zero])
      (‖coordinate (E := E) i‖*C) (mul_nonneg (norm_nonneg _) hC)
      (fun a y => ((coordinate i).le_opNorm (g a y)).trans
        (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg _)))
  have hvec (i : Fin (Module.finrank ℝ E)) : TightNorm
      (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), coordinate i (actualVectorResponse protocol g k path)) • b i) atTop := by
    apply tight_dominated (hc i) (‖b i‖+1) (by positivity)
    intro n path
    rw [norm_smul]
    dsimp only [actualResponse, actualVectorResponse]
    nlinarith [norm_nonneg (b i), norm_nonneg
      ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), coordinate i
          (g (protocol.design k (adaptiveInfinitePathPrefix k path)) (path k)))]
  have hs := tight_finite_sum Finset.univ _ (fun i _ => hvec i)
  have heq (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ i, ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), coordinate i (actualVectorResponse protocol g k path)) • b i) =
      (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path := by
    simpa only [map_smul, map_sum, smul_eq_mul] using sum_coordinate
      ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path)
  simpa only [heq] using hs

end
end QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates
