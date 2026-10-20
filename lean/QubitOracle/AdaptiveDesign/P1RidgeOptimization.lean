import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra

/-! The displayed mixed-qubit least-squares optimization problem has
the literal recursive ridge estimate as its unique minimizer. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def regressionFeature (p : Policy) (n : ℕ) (path : Path) (t : Fin n) : Vector :=
  WithLp.toLp 2 (actualAxis p t.val path)

def ridgeObjective (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (x : Fin 3 → ℝ) : ℝ :=
  ridge/2*blochNormSq x+(∑ t : Fin n,
    ((path t.val).2.sign-blochDot (actualAxis (policy loss ridge refresh) t.val path) x)^2)/2

theorem vector_inner_bloch (x y : Fin 3 → ℝ) :
    ⟪WithLp.toLp 2 x,WithLp.toLp 2 y⟫_ℝ=blochDot x y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,blochDot,dotProduct,mul_comm]

theorem normalMap_regression (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (x : Vector) :
    TangentGLS.normalMap (regressionFeature (policy loss ridge refresh) n path) (fun _ => 1) ridge x =
      (pathState loss ridge refresh n path).gram.toEuclideanLin x := by
  ext i
  simp only [TangentGLS.normalMap_apply,TangentGLS.gram_apply,one_mul,regressionFeature,
    PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,smul_eq_mul,WithLp.ofLp_sum,WithLp.ofLp_smul,
    Matrix.toEuclideanLin_apply,WithLp.ofLp_toLp,pathState_gram,
    Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,Pi.add_apply,Pi.smul_apply,
    Matrix.sum_mulVec,Finset.sum_apply,Matrix.mulVec,dotProduct,blochOuter]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    ⟪WithLp.toLp 2 (actualAxis (policy loss ridge refresh) t path),x⟫_ℝ *
      actualAxis (policy loss ridge refresh) t path i) n]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,WithLp.ofLp_toLp]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem regression_score (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) :
    TangentGLS.score (regressionFeature (policy loss ridge refresh) n path) (fun _ => 1)
      (fun t => (path t.val).2.sign) = WithLp.toLp 2 (pathState loss ridge refresh n path).rhs := by
  ext i
  simp only [TangentGLS.score,regressionFeature,one_mul,WithLp.ofLp_sum,WithLp.ofLp_smul,
    WithLp.ofLp_toLp,PiLp.toLp_apply,pathState_rhs,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    (path t).2.sign * actualAxis (policy loss ridge refresh) t path i) n

theorem estimate_eq_correction (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    WithLp.toLp 2 (estimate loss ridge refresh n path) =
      TangentGLS.correction (regressionFeature (policy loss ridge refresh) n path)
        (fun _ => 1) (fun t => (path t.val).2.sign) (fun _ => zero_le_one) ridge hr := by
  apply TangentGLS.correction_unique
  rw [normalMap_regression,regression_score]
  exact congrArg (WithLp.toLp 2) (estimate_normalEquation loss ridge hr refresh n path)

theorem objective_regression (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (x : Fin 3 → ℝ) :
    ridgeObjective loss ridge refresh n path x =
      TangentGLS.objective (regressionFeature (policy loss ridge refresh) n path)
        (fun _ => 1) (fun t => (path t.val).2.sign) ridge (WithLp.toLp 2 x) := by
  simp only [ridgeObjective,TangentGLS.objective,regressionFeature,vector_inner_bloch,one_mul,
    EuclideanSpace.real_norm_sq_eq,blochNormSq]

theorem estimate_unique_minimizer (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    (∀ x, ridgeObjective loss ridge refresh n path (estimate loss ridge refresh n path) ≤
      ridgeObjective loss ridge refresh n path x) ∧
    (∀ x, ridgeObjective loss ridge refresh n path x =
      ridgeObjective loss ridge refresh n path (estimate loss ridge refresh n path) →
      x=estimate loss ridge refresh n path) := by
  let feature := regressionFeature (policy loss ridge refresh) n path
  let y := fun t : Fin n => (path t.val).2.sign
  let c := TangentGLS.correction feature (fun _ => 1) y (fun _ => zero_le_one) ridge hr
  have he : WithLp.toLp 2 (estimate loss ridge refresh n path)=c :=
    estimate_eq_correction loss ridge hr refresh n path
  constructor
  · intro x
    rw [objective_regression,objective_regression,he]
    exact TangentGLS.correction_minimizes feature (fun _ => 1) y (fun _ => zero_le_one) ridge hr _
  · intro x hx
    simp only [objective_regression,he] at hx
    have hh := TangentGLS.objective_expansion feature (fun _ => 1) y ridge c (WithLp.toLp 2 x-c)
    rw [add_sub_cancel,TangentGLS.correction_normalEquation,sub_self,inner_zero_right,zero_add,hx,sub_self] at hh
    have hc := TangentGLS.normalMap_coercive feature (fun _ => 1) (fun _ => zero_le_one) ridge (WithLp.toLp 2 x-c)
    have hz : ‖WithLp.toLp 2 x-c‖=0 := by
      have hprod : ridge*‖WithLp.toLp 2 x-c‖^2 ≤ 0 := by linarith only [hh,hc]
      have hs : ‖WithLp.toLp 2 x-c‖^2 ≤ 0 := by
        by_contra hh
        exact (not_lt_of_ge hprod) (mul_pos hr (lt_of_not_ge hh))
      nlinarith [norm_nonneg (WithLp.toLp 2 x-c)]
    have hxc := sub_eq_zero.mp (norm_eq_zero.mp hz)
    exact (WithLp.toLp_injective 2) (hxc.trans he.symm)

end
end QubitOracle.AdaptiveDesign.P1Weighted
