import QubitOracle.AdaptiveDesign.GeneralWeightedOracle

/-! Full matrix information, rather than only its weighted trace, for
the literal finite adaptive product law. Zero-probability records are
handled explicitly; no independence assumption is introduced. -/
namespace QubitOracle.AdaptiveDesign.FiniteRegularOracle
open Matrix
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
variable {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Ξ]

namespace RegularModel

theorem information_apply (P : RegularModel ι Ω) (i j : ι) :
    P.information i j=P.expectation (fun w => P.score w i*P.score w j) := by
  simp [information,expectation,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec]

theorem score_product_add (P : RegularModel ι Ω) (a b : ℝ) (i j : ι) :
    P.expectation (fun w => (a+P.score w i)*(b+P.score w j))=
      a*b+P.information i j := by
  have hi := P.score_centered i
  have hj := P.score_centered j
  rw [information_apply]
  unfold expectation at *
  calc
    _ = a*b*(∑ w, P.mass P.theta w)+
        a*(∑ w, P.mass P.theta w*P.score w j)+
        b*(∑ w, P.mass P.theta w*P.score w i)+
        ∑ w, P.mass P.theta w*(P.score w i*P.score w j) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by rw [P.total,hi,hj]; ring

theorem bind_information (P : RegularModel ι Ω) (Q : Ω → RegularModel ι Ξ)
    (hθ : ∀ w, (Q w).theta=P.theta) :
    (P.bind Q hθ).information=P.information+
      ∑ w, P.mass P.theta w • (Q w).information := by
  ext i j
  rw [information_apply]
  change (∑ wv : Ω×Ξ, _) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ w, P.mass P.theta w*(Q w).expectation
        (fun v => (P.score w i+(Q w).score v i)*(P.score w j+(Q w).score v j)) := by
      apply Finset.sum_congr rfl
      intro w _
      unfold expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hp : P.mass P.theta w=0
      · simp [bind,hp]
      by_cases hq : (Q w).mass P.theta v=0
      · simp [bind,hq,hθ]
      change (P.mass P.theta w*(Q w).mass P.theta v)*
        ((P.bind Q hθ).score (w,v) i*(P.bind Q hθ).score (w,v) j)=_
      rw [P.bind_score Q hθ w v hp hq,P.bind_score Q hθ w v hp hq,hθ]
      ring
    _ = ∑ w, P.mass P.theta w*(P.score w i*P.score w j+(Q w).information i j) := by
      simp only [score_product_add]
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Matrix.add_apply,Matrix.sum_apply,
        Matrix.smul_apply,smul_eq_mul,information_apply,expectation]

end RegularModel

/-- The sum of the conditional per-copy information matrices along a
complete record, with each setting chosen from its preceding history. -/
def conditionalInformationSum {Y : Type} [Fintype Y] (theta : ι → ℝ)
    (step : List Y → AtTruth theta Y) :
    (n : ℕ) → List Y → Record Y n → Matrix ι ι ℝ
  | 0, _, _ => 0
  | n+1, history, record => (step history).val.information+
      conditionalInformationSum theta step n (record.1 :: history) record.2

/-- Exact information-chain-rule equality for the joint adaptive law. -/
theorem adaptive_information_eq_expected_sum {Y : Type} [Fintype Y]
    (theta : ι → ℝ) (step : List Y → AtTruth theta Y)
    (n : ℕ) (history : List Y) :
    (adaptiveExperiment theta step n history).val.information=
      ∑ record, (adaptiveExperiment theta step n history).val.mass theta record •
        conditionalInformationSum theta step n history record := by
  induction n generalizing history with
  | zero =>
      ext i j
      simp [adaptiveExperiment,emptyExperiment,RegularModel.information,
        RegularModel.score,conditionalInformationSum,Matrix.vecMulVec]
  | succ n ih =>
      change ((step history).val.bind
        (fun y => (adaptiveExperiment theta step n (y :: history)).val)
        (fun y => (adaptiveExperiment theta step n (y :: history)).property.trans
          (step history).property.symm)).information=_
      rw [RegularModel.bind_information]
      change _ = ∑ r : Y × Record Y n,
        ((step history).val.mass theta r.1 *
          (adaptiveExperiment theta step n (r.1::history)).val.mass theta r.2) •
          ((step history).val.information+conditionalInformationSum theta step n (r.1::history) r.2)
      rw [Fintype.sum_prod_type]
      simp only [smul_add,Finset.sum_add_distrib]
      have ht := (step history).property
      rw [ht]
      have hfirst : (∑ y, ∑ r,
          ((step history).val.mass theta y*(adaptiveExperiment theta step n (y::history)).val.mass theta r) •
            (step history).val.information)=(step history).val.information := by
        simp only [← Finset.sum_smul,← Finset.mul_sum,RegularModel.total,mul_one]
        simp
      rw [hfirst]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      rw [ih (y::history)]
      simp only [Finset.smul_sum,smul_smul]

end
end QubitOracle.AdaptiveDesign.FiniteRegularOracle
