import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.MixedStageStability
import QubitOracle.Paper.P1AdaptiveRidgePolicy
import QubitOracle.Paper.P1UniformFrameInformation
/-! The two actual P1 allocation rules and the expanding-interior controller.
The floor is derived before consistency; no excitation assumption is hidden. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

inductive Loss where
  | bures
  | frobenius
  deriving DecidableEq

def weight (loss : Loss) (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  match loss with
  | .bures => radialTangentMass (1/3) (1/3)
  | .frobenius => radialTangentMass (mixedCoherenceAllocation r) (mixedRadialAllocation r)

def referenceAction (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) : Action where
  frame := P1.canonicalUniformFrame r
  weight := weight loss r
  nonneg := by
    cases loss with
    | bures => exact radialTangentMass_nonnegative _ _ (by norm_num) (by norm_num)
    | frobenius =>
        exact radialTangentMass_nonnegative _ _
          (mixedCoherenceAllocation_pos r hr).le (mixedRadialAllocation_pos r hr).le
  total := by
    cases loss with
    | bures => exact radialTangentMass_sum _ _ (by norm_num)
    | frobenius => exact radialTangentMass_sum _ _ (mixedAllocations_sum r hr)

def radius (n : ℕ) : ℝ := Real.sqrt (1 - ExplorationRidge.epsilon n ^ 2)

def clip (n : ℕ) (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if blochNormSq r ≤ 1 - ExplorationRidge.epsilon n ^ 2 then r
  else (radius n / Real.sqrt (blochNormSq r)) • r

theorem normSq_nonneg (r : Fin 3 → ℝ) : 0 ≤ blochNormSq r :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSq_smul (a : ℝ) (r : Fin 3 → ℝ) :
    blochNormSq (a • r) = a^2 * blochNormSq r := by
  simp [blochNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem radius_sq (n : ℕ) : radius n ^ 2 = 1 - ExplorationRidge.epsilon n ^ 2 := by
  apply Real.sq_sqrt
  have h := ExplorationRidge.epsilon_le_one n
  have hp := (ExplorationRidge.epsilon_pos n).le
  nlinarith

theorem clip_normSq (n : ℕ) (r : Fin 3 → ℝ) :
    blochNormSq (clip n r) ≤ 1 - ExplorationRidge.epsilon n ^ 2 := by
  unfold clip
  split_ifs with h
  · exact h
  · rw [normSq_smul]
    have hr : 0 < blochNormSq r := by
      have hh := ExplorationRidge.epsilon_le_one n
      have hp := (ExplorationRidge.epsilon_pos n).le
      have ht := lt_of_not_ge h
      nlinarith
    have hs : Real.sqrt (blochNormSq r) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
    have he : (radius n / Real.sqrt (blochNormSq r))^2 * blochNormSq r = radius n^2 := by
      nth_rw 2 [← Real.sq_sqrt hr.le]
      field_simp
    rw [he, radius_sq]

theorem clip_interior (n : ℕ) (r : Fin 3 → ℝ) : blochNormSq (clip n r) < 1 := by
  have h := clip_normSq n r
  have hp := sq_pos_of_pos (ExplorationRidge.epsilon_pos n)
  linarith

def controller (loss : Loss) (n : ℕ) (r : Fin 3 → ℝ) : Fin 3 → ℝ :=
  match loss with
  | .bures => P1.interiorize r
  | .frobenius => clip n r

theorem controller_interior (loss : Loss) (n : ℕ) (r : Fin 3 → ℝ) :
    blochNormSq (controller loss n r) < 1 := by
  cases loss with
  | bures => exact P1.interiorize_interior r
  | frobenius => exact clip_interior n r

theorem clip_eventually_eq {θ : Fin 3 → ℝ} (hθ : blochNormSq θ < 1)
    {r : ℕ → Fin 3 → ℝ} (hr : Tendsto r atTop (𝓝 θ)) :
    (fun n => clip n (r n)) =ᶠ[atTop] r := by
  have hnorm := continuous_blochNormSq.continuousAt.tendsto.comp hr
  have hcap : Tendsto (fun n => 1 - ExplorationRidge.epsilon n ^ 2) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.sub (ExplorationRidge.epsilon_tendsto_zero.pow 2)
  have hlo := hnorm.eventually (Iio_mem_nhds (show blochNormSq θ < (1+blochNormSq θ)/2 by linarith))
  have hhi := hcap.eventually (Ioi_mem_nhds (show (1+blochNormSq θ)/2 < (1:ℝ) by linarith))
  filter_upwards [hlo,hhi] with n hn hn'
  exact if_pos (le_of_lt (hn.trans hn'))

theorem controller_eventually_eq {θ : Fin 3 → ℝ} (hθ : blochNormSq θ < 1)
    (loss : Loss) {r : ℕ → Fin 3 → ℝ} (hr : Tendsto r atTop (𝓝 θ)) :
    (fun n => controller loss n (r n)) =ᶠ[atTop] r := by
  cases loss with
  | frobenius => exact clip_eventually_eq hθ hr
  | bures =>
    have hh := (continuous_blochNormSq.continuousAt.tendsto.comp hr).eventually (Iio_mem_nhds hθ)
    filter_upwards [hh] with n hn
    exact if_pos hn

theorem gap_le_one (r : Fin 3 → ℝ) : mixedRadialGap r ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  linarith [normSq_nonneg r]

theorem clip_gap_floor (n : ℕ) (r : Fin 3 → ℝ) :
    ExplorationRidge.epsilon n ≤ mixedRadialGap (clip n r) := by
  apply (Real.le_sqrt (ExplorationRidge.epsilon_pos n).le (sub_pos.mpr (clip_interior n r)).le).mpr
  linarith [clip_normSq n r]

theorem weight_floor (loss : Loss) (n : ℕ) (r : Fin 3 → ℝ) (k : Fin 3) :
    ExplorationRidge.epsilon n / 3 ≤ weight loss (controller loss n r) k := by
  cases loss with
  | bures =>
    have h := ExplorationRidge.epsilon_le_one n
    fin_cases k <;> norm_num [weight,radialTangentMass] <;> linarith
  | frobenius =>
    have hg := clip_gap_floor n r
    have hu := gap_le_one (clip n r)
    have hp := mixedRadialGap_pos _ (clip_interior n r)
    have he := ExplorationRidge.epsilon_le_one n
    have ha : ExplorationRidge.epsilon n / 3 ≤ mixedCoherenceAllocation (clip n r) := by
      unfold mixedCoherenceAllocation
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ mixedRadialGap (clip n r) by positivity)]
    have hb : ExplorationRidge.epsilon n / 3 ≤ mixedRadialAllocation (clip n r) := by
      unfold mixedRadialAllocation
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (ExplorationRidge.epsilon_pos n).le]
    fin_cases k <;> simp [weight,controller,radialTangentMass] <;> assumption

end
end QubitOracle.AdaptiveDesign.P1Weighted
