import QubitOracle.AdaptiveDesign.P1ControllerBounds
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder
import QubitOracle.Paper.P1BuresOptimality
/-! An exact continuous quadratic representation of mixed-qubit Bures
loss. It remains valid at pure estimated states when the truth is interior. -/
namespace QubitOracle.AdaptiveDesign.MixedBuresContinuousQuadratic
open QubitOracle QubitOracle.Paper P1Weighted
open scoped InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def gap (x : Vector) : ℝ := Real.sqrt (1-‖x‖^2)
def fidelity (θ s : Vector) : ℝ := (1+⟪θ,s⟫_ℝ+gap θ*gap s)/2
def bures (θ s : Vector) : ℝ := 2*(1-Real.sqrt (fidelity θ s))
def form (θ s z : Vector) : ℝ :=
  (‖z‖^2+(⟪s+θ,z⟫_ℝ/(gap θ+gap s))^2)/(2*(1+Real.sqrt (fidelity θ s)))

theorem gap_sq (x : Vector) (hx : ‖x‖ ≤ 1) : gap x^2=1-‖x‖^2 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg x]

theorem gap_pos (θ : Vector) (hθ : ‖θ‖ < 1) : 0 < gap θ := by
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg θ]

theorem fidelity_identity (θ s : Vector) (hθ : ‖θ‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    4*(1-fidelity θ s)=‖s-θ‖^2+(gap θ-gap s)^2 := by
  have hθg := gap_sq θ hθ
  have hsg := gap_sq s hs
  rw [norm_sub_sq_real]
  have hi : ⟪s,θ⟫_ℝ=⟪θ,s⟫_ℝ := real_inner_comm _ _
  dsimp only [fidelity]
  nlinarith only [hθg,hsg,hi]

theorem fidelity_nonneg (θ s : Vector) (hθ : ‖θ‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    0 ≤ fidelity θ s := by
  have hprod : ‖θ‖*‖s‖ ≤ 1 := (mul_le_mul hθ hs (norm_nonneg s) zero_le_one).trans (by norm_num)
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm θ s)
  have hg : 0 ≤ gap θ*gap s := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  dsimp only [fidelity]
  nlinarith only [hprod,hi,hg]

theorem fidelity_self (θ : Vector) (hθ : ‖θ‖ ≤ 1) : fidelity θ θ=1 := by
  have h := gap_sq θ hθ
  dsimp only [fidelity]
  rw [real_inner_self_eq_norm_sq]
  nlinarith only [h]

theorem gap_difference (θ s : Vector) (hθ : ‖θ‖ < 1) (hs : ‖s‖ ≤ 1) :
    gap θ-gap s=⟪s+θ,s-θ⟫_ℝ/(gap θ+gap s) := by
  have hθg := gap_sq θ hθ.le
  have hsg := gap_sq s hs
  have hp : 0 < gap θ+gap s := add_pos_of_pos_of_nonneg (gap_pos θ hθ) (Real.sqrt_nonneg _)
  apply (eq_div_iff hp.ne').mpr
  rw [inner_add_left,inner_sub_right,inner_sub_right,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq,real_inner_comm θ s]
  nlinarith only [hθg,hsg]

theorem exact_loss (θ s : Vector) (hθ : ‖θ‖ < 1) (hs : ‖s‖ ≤ 1) :
    bures θ s=form θ s (s-θ) := by
  have hi := fidelity_identity θ s hθ.le hs
  have hf := Real.sq_sqrt (fidelity_nonneg θ s hθ.le hs)
  rw [gap_difference θ s hθ hs] at hi
  have hp : 0 < 2*(1+Real.sqrt (fidelity θ s)) := by positivity
  unfold bures form
  apply (eq_div_iff hp.ne').mpr
  nlinarith only [hi,hf]

theorem form_continuous (θ : Vector) (hθ : ‖θ‖ < 1) :
    Continuous (fun sz : Vector × Vector => form θ sz.1 sz.2) := by
  have hgap : Continuous gap := by unfold gap; fun_prop
  have hfid : Continuous (fun s => fidelity θ s) := by unfold fidelity; fun_prop
  have hden (s : Vector) : gap θ+gap s ≠ 0 :=
    (add_pos_of_pos_of_nonneg (gap_pos θ hθ) (Real.sqrt_nonneg _)).ne'
  unfold form
  apply Continuous.div
  · apply Continuous.add (by fun_prop)
    exact ((by fun_prop : Continuous (fun sz : Vector × Vector => ⟪sz.1+θ,sz.2⟫_ℝ)).div
      (continuous_const.add (hgap.comp continuous_fst)) (fun sz => hden sz.1)).pow 2
  · fun_prop
  · intro sz
    positivity

theorem form_nonneg (θ s z : Vector) : 0 ≤ form θ s z := by unfold form; positivity

theorem form_smul (θ s z : Vector) (a : ℝ) : form θ s (a • z)=a^2*form θ s z := by
  unfold form
  rw [norm_smul,real_inner_smul_right,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem form_at_truth (θ z : Vector) (hθ : ‖θ‖ < 1) :
    form θ θ z = quadratic ((1/4:ℝ) • (qubitSLDFisherInv θ.ofLp)⁻¹) z.ofLp := by
  have hn (v : Vector) : blochNormSq v.ofLp=‖v‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,blochNormSq]
  have ht : blochNormSq θ.ofLp < 1 := by rw [hn]; nlinarith [norm_nonneg θ]
  have hi : blochDot θ.ofLp z.ofLp=⟪θ,z⟫_ℝ := by
    simp only [blochDot,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]
  rw [P1.qubitSLDFisherInv_inv θ.ofLp ht,quadratic_smul,quadratic_add,quadratic_one,
    quadratic_smul,quadratic_outer,hn,hn,hi,← gap_sq θ hθ.le]
  rw [form,fidelity_self θ hθ.le,inner_add_left]
  norm_num
  field_simp [(gap_pos θ hθ).ne'] <;> ring

theorem form_bound (θ s z : Vector) (hθ : ‖θ‖ < 1) (hs : ‖s‖ ≤ 1) :
    form θ s z ≤ ((1+4/(gap θ)^2)/2)*‖z‖^2 := by
  have ht := gap_pos θ hθ
  have hg : gap θ ≤ gap θ+gap s := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hg0 : 0 < gap θ+gap s := ht.trans_le hg
  have hsum : ‖s+θ‖ ≤ 2 := (norm_add_le _ _).trans (by linarith only [hs,hθ])
  have hi := abs_real_inner_le_norm (s+θ) z
  have hi' : |⟪s+θ,z⟫_ℝ| ≤ 2*‖z‖ := hi.trans (mul_le_mul_of_nonneg_right hsum (norm_nonneg _))
  have hd : |⟪s+θ,z⟫_ℝ/(gap θ+gap s)| ≤ 2*‖z‖/gap θ := by
    rw [abs_div,abs_of_pos hg0]
    exact (div_le_div_of_nonneg_right hi' hg0.le).trans
      (div_le_div_of_nonneg_left (by positivity) ht hg)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hd 2
  simp only [sq_abs,div_pow,mul_pow] at hp
  have hden : 2 ≤ 2*(1+Real.sqrt (fidelity θ s)) := by linarith [Real.sqrt_nonneg (fidelity θ s)]
  calc
    _ ≤ (‖z‖^2+(⟪s+θ,z⟫_ℝ/(gap θ+gap s))^2)/2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ (‖z‖^2+4*‖z‖^2/(gap θ)^2)/2 := by
      simp only [div_pow]
      norm_num at hp
      linarith only [hp]
    _ = _ := by ring

theorem bloch_fidelity (θ s : Vector) (hθ : ‖θ‖ ≤ 1) :
    fidelity θ s=mixedQubitBlochFidelitySqBetween θ.ofLp s.ofLp := by
  have hn (z : Vector) : blochNormSq z.ofLp=‖z‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,blochNormSq]
  have hi : blochDot θ.ofLp s.ofLp=⟪θ,s⟫_ℝ := by
    simp only [blochDot,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]
  rw [mixedQubitBlochFidelitySqBetween,hn,hn,hi,
    Real.sqrt_mul (by nlinarith [norm_nonneg θ] : 0 ≤ 1-‖θ‖^2)]
  rfl

theorem bloch_bures (θ s : Vector) (hθ : ‖θ‖ ≤ 1) :
    bures θ s=mixedQubitBlochBuresSqBetween θ.ofLp s.ofLp := by
  rw [bures,bloch_fidelity θ s hθ]
  rfl

end
end QubitOracle.AdaptiveDesign.MixedBuresContinuousQuadratic
