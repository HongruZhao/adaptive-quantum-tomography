import Mathlib.MeasureTheory.Function.L2Space
import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-!
# All-observation ridge consistency on a genuine adaptive experiment

For finite-dimensional real response vectors, the bounded-response strong law
is proved coordinatewise in an orthonormal basis. The actual inverse-Gram ridge
estimate is then strongly consistent when each physical action has a uniformly
coercive information frame and its response satisfies the exact kernel mean
identity. These are finite-measurement algebra obligations, not stochastic
consistency assumptions.
-/

namespace QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares AdaptiveResponseStrongLaw
open scoped BigOperators Topology InnerProductSpace

noncomputable section

variable {Theta Action Outcome E : Type*}
variable [MeasurableSpace Action] [MeasurableSpace Outcome]
variable [Fintype Outcome] [MeasurableSingletonClass Outcome]
variable [StandardBorelSpace Outcome] [Nonempty Outcome]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def actualVectorResponse
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (centered : Action → Outcome → E) (n : ℕ)
    (path : AdaptiveInfinitePath Outcome) : E :=
  centered (protocol.design n (adaptiveInfinitePathPrefix n path)) (path n)

theorem actualVectorResponse_average_ae_tendsto_zero
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → E)
    (hcenter : ∀ action, ∫ y, centered action y ∂protocol.response theta action = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ t ∈ Finset.range n, actualVectorResponse protocol centered t path)
        atTop (𝓝 0) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hcoordinate (i : Fin (Module.finrank ℝ E)) :
      ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
            ⟪b i, actualVectorResponse protocol centered t path⟫_ℝ)
          atTop (𝓝 0) := by
    apply actualResponse_average_ae_tendsto_zero protocol theta
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
          (fun n : ℕ => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
            ⟪b i, actualVectorResponse protocol centered t path⟫_ℝ)
          atTop (𝓝 0) := ae_all_iff.2 hcoordinate
  filter_upwards [hall] with path hpath
  have hsum := tendsto_finset_sum Finset.univ
    (fun i _ => (hpath i).smul_const (b i))
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr',
    zero_smul, Finset.sum_const_zero] using hsum

/-- Realized predictable action at a shot. -/
def actualAction
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) : Action :=
  protocol.design n (adaptiveInfinitePathPrefix n path)

/-- Ridge estimate formed from the actual actions and every observed outcome.
The protocol may freeze its actions over batches of any prescribed lengths. -/
def actualRidgeEstimate
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 ≤ κ) (hframe : ∀ action, Coercive (frame action) κ)
    (path : AdaptiveInfinitePath Outcome) (n : ℕ) : E :=
  ridgeEstimate
    (fun t => frame (actualAction protocol path t))
    (fun t => response (actualAction protocol path t) (path t))
    regularization κ hregularization hκ
    (fun t => hframe (actualAction protocol path t)) n

/-- Strong consistency of the explicitly defined all-data ridge estimate
under the exact adaptive path law. Only finite-measurement expectation and
coercivity identities remain for a concrete POVM to instantiate. -/
theorem actualRidgeEstimate_tendsto_ae
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E) (truth : E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 < κ) (hframe : ∀ action, Coercive (frame action) κ)
    (hmean : ∀ action,
      ∫ y, response action y ∂protocol.response theta action = frame action truth)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖response action outcome - frame action truth‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto
        (actualRidgeEstimate protocol frame response regularization κ
          hregularization hκ.le hframe path)
        atTop (𝓝 truth) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let centered := fun action outcome => response action outcome - frame action truth
  have hcenter (action : Action) :
      ∫ y, centered action y ∂protocol.response theta action = 0 := by
    dsimp [centered]
    rw [integral_sub Integrable.of_finite (integrable_const _), hmean]
    simp
  have hstrong := actualVectorResponse_average_ae_tendsto_zero
    protocol theta centered hcenter C hC hbound
  filter_upwards [hstrong] with path hpath
  exact ridgeEstimate_tendsto_of_averageInnovation
    (fun t => frame (actualAction protocol path t))
    (fun t => response (actualAction protocol path t) (path t))
    truth regularization κ hregularization hκ
    (fun t => hframe (actualAction protocol path t)) hpath

end

end QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
