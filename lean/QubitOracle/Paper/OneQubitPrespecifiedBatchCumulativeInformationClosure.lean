import Mathlib.Probability.BorelCantelli
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitAPSRLSContract
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Filter MeasureTheory Matrix
open scoped BigOperators ENNReal Topology Matrix

noncomputable section

set_option maxRecDepth 2000




/-! ## Summable exact pilot tails and almost-sure controller convergence -/

/-- Shrinking coordinate threshold used for the first Borel--Cantelli step. -/
def exactConcretePilotShrinkingThreshold (k : Nat) : Real :=
  (k + 1 : Real)⁻¹

theorem exactConcretePilotShrinkingThreshold_pos (k : Nat) :
    0 < exactConcretePilotShrinkingThreshold k := by
  unfold exactConcretePilotShrinkingThreshold
  positivity

theorem exactConcretePilotShrinkingThreshold_tendsto_zero :
    Tendsto exactConcretePilotShrinkingThreshold atTop (nhds 0) := by
  unfold exactConcretePilotShrinkingThreshold
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : Nat => 1 / ((k : Real) + 1)) atTop (nhds 0))


/-- A geometric ENNReal envelope dominating the shrinking-threshold pilot
failure probability. -/
def exactConcretePilotGeometricEnvelope (k : Nat) : ENNReal :=
  ENNReal.ofReal (2 * Real.exp (-(27 / 2 : Real) * (k + 1)))


theorem exactConcretePilotGeometricEnvelope_tsum_ne_top :
    (∑' k : Nat, exactConcretePilotGeometricEnvelope k) ≠ ∞ := by
  have hreal : Summable
      (fun k : Nat => 2 * Real.exp (-(27 / 2 : Real) * (k + 1))) := by
    exact (Real.summable_exp_nat_mul_of_ge
      (c := -(27 / 2 : Real)) (by norm_num) (fun k => by norm_num)).mul_left 2
  exact hreal.tsum_ofReal_ne_top



/-! ## Uniform concrete exploration and exploitation bounds -/

/-- Interior squared-norm gap used in all finite information bounds. -/
def exactConcreteMixedInformationGap (theta : RLSVector 3) : Real :=
  1 - QubitOracle.blochNormSq theta








/-! ## Exact cumulative final-shot Fisher identity -/


/-! ## Almost-sure and in-probability cumulative closure -/





/-! ## Exact Bures normalization -/





end

end QubitOracle.Paper
