import QubitOracle.AdaptiveDesign.TangentGLSInformation
import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICFisher
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.Paper.CompactLimitTransfer
import QubitOracle.Paper.RankOneStageContinuity
import QubitOracle.TwoBasis
/-! Exact unweighted tangent moments of the optional finite-library POVM.
These are Gram and noise moments, not Fisher information. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian TangentGLS
open Filter
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

def gramConstant (d : ℕ) : ℝ := (4*(d+1)-5)/(32*(d*(4*d+1))*d)
def noiseConstant (d : ℕ) : ℝ := (5*(d+1)-7)/(256*(d*(4*d+1))^2*d)
def tangentVariance (d : ℕ) : ℝ := 4*d*(5*(d+1)-7)/(4*(d+1)-5)^2

lemma constants_positive {d : ℕ} (hd : 0 < d) :
    0 < gramConstant d ∧ 0 < noiseConstant d := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold gramConstant noiseConstant
  constructor <;> apply div_pos
  · linarith
  · positivity
  · linarith
  · positivity

lemma variance_ratio {d : ℕ} (hd : 0 < d) :
    noiseConstant d / (gramConstant d)^2 = tangentVariance d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hh : 4*((d:ℝ)+1)-5 ≠ 0 := by
    have h : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold noiseConstant gramConstant tangentVariance
  field_simp
  <;> ring

lemma phaseCoordinate_sum {d : ℕ} (v : Fin d → ℂ) (x : TangentIndex d) :
    ∑ s : Fin 4, phaseCoordinate s v x = 0 := by
  cases x <;> simp [phaseCoordinate, phase4, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

def gram {d : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o : Outcome d, transportedGradient U o x * transportedGradient U o y

def mean {d : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : TangentIndex d → ℝ :=
  fun x => ∑ o : Outcome d, transportedMass U o * transportedGradient U o x

def moment {d : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fun x y => ∑ o : Outcome d, transportedMass U o *
    ((transportedGradient U o x-mean U x)*(transportedGradient U o y-mean U y))

lemma gram_continuous {d : ℕ} : Continuous (@gram d) := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  exact continuous_finset_sum _ (fun o _ =>
    (transportedGradient_continuous o x).mul (transportedGradient_continuous o y))

lemma mean_continuous {d : ℕ} : Continuous (@mean d) := by
  apply continuous_pi; intro x
  exact continuous_finset_sum _ (fun o _ =>
    (transportedMass_continuous o).mul (transportedGradient_continuous o x))

lemma moment_continuous {d : ℕ} : Continuous (@moment d) := by
  apply continuous_pi; intro x
  apply continuous_pi; intro y
  exact continuous_finset_sum _ (fun o _ =>
    (transportedMass_continuous o).mul
      (((transportedGradient_continuous o x).sub ((continuous_apply x).comp mean_continuous)).mul
        ((transportedGradient_continuous o y).sub ((continuous_apply y).comp mean_continuous))))

lemma gradient_product {d : ℕ} (hd : 0 < d) (b : Bool) (a z : ℝ) :
    (effectWeight d*Real.sqrt (latitude d b)*Real.sqrt (1-latitude d b)*a)*
      (effectWeight d*Real.sqrt (latitude d b)*Real.sqrt (1-latitude d b)*z) =
      (effectWeight d)^2*latitude d b*(1-latitude d b)*(a*z) := by
  have ht := Real.sq_sqrt (latitude_pos d b).le
  have hu := Real.sq_sqrt (sub_nonneg.mpr (latitude_lt_one d hd b).le)
  calc
    _ = (effectWeight d)^2*(Real.sqrt (latitude d b))^2*
        (Real.sqrt (1-latitude d b))^2*(a*z) := by ring
    _ = _ := by rw [ht,hu]

lemma gram_scalar {d : ℕ} (hd : 0 < d) :
    ∑ b : Bool, (effectWeight d)^2*latitude d b*(1-latitude d b)*(2*(4*(d:ℝ)+1)) =
      gramConstant d/2 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  simp only [Fintype.sum_bool, effectWeight, latitude, Bool.false_eq_true, ↓reduceIte, gramConstant]
  field_simp
  <;> ring

lemma noise_scalar {d : ℕ} (hd : 0 < d) :
    ∑ b : Bool, effectWeight d*latitude d b*
      ((effectWeight d)^2*latitude d b*(1-latitude d b)*(2*(4*(d:ℝ)+1))) =
      noiseConstant d/2 := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  simp only [Fintype.sum_bool, effectWeight, latitude, Bool.false_eq_true, ↓reduceIte, noiseConstant]
  field_simp
  <;> ring

lemma mean_at_alignment {d : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) : mean U = 0 := by
  funext x
  simp only [mean, transportedMass_of_overlap_one U hU h,
    transportedGradient_of_overlap_one U hU h, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  simp only [← mul_assoc, ← Finset.mul_sum, phaseCoordinate_sum, mul_zero]

lemma gram_at_alignment {d : ℕ} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) :
    gram U = (gramConstant d/2) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  have hcov := phaseCoordinate_family_covariance
    (fun v : LibraryIndex d => (fiberComplement U).mulVec (libraryVector v))
    (4*(d:ℝ)+1) (by simpa using transformed_library_tight _ (fiberComplement_mem_unitary U hU h))
  ext x y
  simp only [gram, transportedGradient_of_overlap_one U hU h, gradient_product hd,
    Fintype.sum_prod_type, ← Finset.mul_sum, hcov, Matrix.smul_apply, smul_eq_mul]
  have hs := gram_scalar hd
  rw [← Finset.sum_mul] at hs
  rw [← Finset.sum_mul, ← mul_assoc, hs]

lemma moment_at_alignment {d : ℕ} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : controllerTrueOverlapSq U = 1) :
    moment U = (noiseConstant d/2) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  have hcov := phaseCoordinate_family_covariance
    (fun v : LibraryIndex d => (fiberComplement U).mulVec (libraryVector v))
    (4*(d:ℝ)+1) (by simpa using transformed_library_tight _ (fiberComplement_mem_unitary U hU h))
  ext x y
  simp only [moment, mean_at_alignment U hU h, Pi.zero_apply, sub_zero,
    transportedMass_of_overlap_one U hU h, transportedGradient_of_overlap_one U hU h,
    gradient_product hd, Fintype.sum_prod_type, ← Finset.mul_sum, hcov,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simpa only [← mul_assoc] using noise_scalar hd

theorem moment_limits {d : ℕ} (hd : 0 < d)
    (U : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => controllerTrueOverlapSq (U n)) atTop (𝓝 1)) :
    Tendsto (fun n => gram (U n)) atTop
      (𝓝 ((gramConstant d/2) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
    Tendsto (fun n => moment (U n)) atTop
      (𝓝 ((noiseConstant d/2) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  constructor
  · refine tendsto_of_compact_identified_fiber _ isCompact_unitaryMatrices U hU
      controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h gram _ ?_
    exact fun V hV hv => ⟨gram_continuous.continuousAt, gram_at_alignment hd V hV hv⟩
  · refine tendsto_of_compact_identified_fiber _ isCompact_unitaryMatrices U hU
      controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h moment _ ?_
    exact fun V hV hv => ⟨moment_continuous.continuousAt, moment_at_alignment hd V hV hv⟩

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
