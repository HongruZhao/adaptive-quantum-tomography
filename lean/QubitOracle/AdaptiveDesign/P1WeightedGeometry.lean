import QubitOracle.AdaptiveDesign.P1WeightedInformation
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.ConcreteProtocolA1A3
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitGeneralScheduleFrobeniusTraceInformation
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.P1UniformFrameBorn
import QubitOracle.Paper.P1UniformFrameInformation
/-! Closed, center-safe formulas for the least-squares Gram and residual
covariance. These are distinct from Fisher information. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def meanGramTarget (loss : Loss) (r : Fin 3 → ℝ) : Mat :=
  match loss with
  | .bures => (1/3:ℝ) • 1
  | .frobenius => (2+mixedRadialGap r)⁻¹ • 1 -
      ((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ • blochOuter r

def radialWeight (loss : Loss) (r : Fin 3 → ℝ) : ℝ :=
  match loss with
  | .bures => 1/3
  | .frobenius => mixedRadialAllocation r

def noiseTarget (loss : Loss) (r : Fin 3 → ℝ) : Mat :=
  meanGramTarget loss r - radialWeight loss r • blochOuter r

def covarianceTarget (loss : Loss) (r : Fin 3 → ℝ) : Mat :=
  match loss with
  | .bures => (3:ℝ) • (1-blochOuter r)
  | .frobenius => (2+mixedRadialGap r) • (1-(1+mixedRadialGap r)⁻¹ • blochOuter r)

theorem gap_sq (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    mixedRadialGap r ^ 2 = 1-blochNormSq r := Real.sq_sqrt (sub_pos.mpr hr).le

theorem normSq_eq_zero (r : Fin 3 → ℝ) (hr : blochNormSq r = 0) : r = 0 := by
  funext i
  have hh := coordinate_sq_le r i
  rw [hr] at hh
  change r i = 0
  nlinarith [sq_nonneg (r i)]

theorem radial_scaled (r : Fin 3 → ℝ) (f : MixedRadialTangentFrame r) :
    blochNormSq r • blochOuter f.radial = blochOuter r := by
  by_cases h : blochNormSq r = 0
  · rw [h,zero_smul]
    have hb := congrArg blochOuter (normSq_eq_zero r h)
    ext i j
    have hij := congrFun (congrFun hb i) j
    simpa [blochOuter] using hij.symm
  · rw [f.radial_outer_of_nonzero h,mixedRadialProjector,smul_smul,mul_inv_cancel₀ h,one_smul]

theorem allocation_difference (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    mixedRadialAllocation r - mixedCoherenceAllocation r =
      -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ * blochNormSq r := by
  have hp := mixedRadialGap_pos r hr
  have h2 : (2+mixedRadialGap r) ≠ 0 := by positivity
  have h1 : (1+mixedRadialGap r) ≠ 0 := by positivity
  unfold mixedRadialAllocation mixedCoherenceAllocation
  field_simp
  nlinarith [gap_sq r hr]

theorem gram_reference (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    gram (referenceAction loss r hr) = meanGramTarget loss r := by
  let f := mixedCanonicalRadialTangentFrame r
  cases loss with
  | bures =>
    ext i j
    have h := congrFun (congrFun f.resolution i) j
    simp only [Matrix.add_apply,Matrix.one_apply,blochOuter] at h
    simp [gram,referenceAction,axis,P1.canonicalUniformFrame,P1.fromRadialFrame,
      radialTangentAxes,weight,radialTangentMass,Fin.sum_univ_succ,meanGramTarget,
      Matrix.smul_apply,Matrix.one_apply,blochOuter]
    dsimp [f] at h
    split_ifs at h ⊢ <;> norm_num at * <;> linarith
  | frobenius =>
    have hrad : (mixedRadialAllocation r-mixedCoherenceAllocation r) • blochOuter f.radial =
        -((2+mixedRadialGap r)*(1+mixedRadialGap r))⁻¹ • blochOuter r := by
      rw [allocation_difference r hr,mul_smul,radial_scaled]
    ext i j
    have hh := congrFun (congrFun f.resolution i) j
    have hh' := congrFun (congrFun hrad i) j
    simp only [Matrix.add_apply,Matrix.one_apply,blochOuter] at hh
    simp only [Matrix.smul_apply,smul_eq_mul,blochOuter] at hh'
    simp [gram,referenceAction,axis,P1.canonicalUniformFrame,P1.fromRadialFrame,
      radialTangentAxes,weight,radialTangentMass,Fin.sum_univ_succ,meanGramTarget,
      Matrix.smul_apply,Matrix.one_apply,blochOuter,mixedCoherenceAllocation]
    dsimp [f] at hh hh'
    unfold mixedCoherenceAllocation at hh'
    simp only [mul_inv_rev] at hh'
    split_ifs at hh ⊢ <;>
      linear_combination (2+mixedRadialGap r)⁻¹ * hh + hh'

theorem noise_reference (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    noiseCovariance r (referenceAction loss r hr) = noiseTarget loss r := by
  let f := mixedCanonicalRadialTangentFrame r
  have hs := radial_scaled r f
  rw [noiseTarget,← gram_reference loss r hr]
  have hfirst := f.tangentFirst_orthogonal
  have hsecond := f.tangentSecond_orthogonal
  have hrad := f.radial_dot_sq
  cases loss <;>
    simp [noiseCovariance,gram,referenceAction,axis,P1.canonicalUniformFrame,
      P1.fromRadialFrame,radialTangentAxes,weight,radialTangentMass,Fin.sum_univ_succ]
  all_goals
    change _ = _
    dsimp [f] at hfirst hsecond hrad hs
    rw [hfirst,hsecond,hrad]
    ext i j
    have h := congrFun (congrFun hs i) j
    simp only [Matrix.smul_apply,smul_eq_mul,blochOuter] at h
    simp [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      radialWeight,blochOuter]
    first | linear_combination -(1/3:ℝ) * h | linear_combination -(mixedRadialAllocation r) * h

theorem continuous_meanGramTarget (loss : Loss) : Continuous (meanGramTarget loss) := by
  have hs := continuous_mixedRadialGap
  have ho := continuous_blochOuter
  cases loss <;> unfold meanGramTarget
  · exact continuous_const
  · have hs0 : ∀ r, 0 ≤ mixedRadialGap r := fun r => Real.sqrt_nonneg _
    have h2 : ∀ r, 2+mixedRadialGap r ≠ 0 := fun r => by have := hs0 r; positivity
    have h1 : ∀ r, 1+mixedRadialGap r ≠ 0 := fun r => by have := hs0 r; positivity
    exact ((continuous_const.add hs).inv₀ h2).smul continuous_const |>.sub
      ((((continuous_const.add hs).mul (continuous_const.add hs)).inv₀
        (fun r => mul_ne_zero (h2 r) (h1 r))).smul ho)

theorem continuous_noiseTarget (loss : Loss) : Continuous (noiseTarget loss) := by
  have hq := continuous_meanGramTarget loss
  have hs := continuous_mixedRadialGap
  have ho := continuous_blochOuter
  unfold noiseTarget
  apply hq.sub
  have hw : Continuous (radialWeight loss) := by
    cases loss <;> unfold radialWeight
    · exact continuous_const
    · unfold mixedRadialAllocation
      have hs0 : ∀ r, 0 ≤ mixedRadialGap r := fun r => Real.sqrt_nonneg _
      exact hs.div (continuous_const.add hs) (fun r => by have := hs0 r; positivity)
  exact hw.smul ho

end
end QubitOracle.AdaptiveDesign.P1Weighted
