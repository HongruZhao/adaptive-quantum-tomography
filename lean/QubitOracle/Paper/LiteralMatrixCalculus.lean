import Mathlib

/-! Differentiate the actual matrix identities used in Section 2.4.
Curves are differentiated entry by entry, so no matrix norm convention
or postulated tangent-space equation is needed in the hypotheses.
-/
namespace QubitOracle.Paper.LiteralMatrixCalculus
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivative_of_projector_curve (γ : ℝ → Matrix ι ι ℂ) (P A : Matrix ι ι ℂ)
    (h0 : γ 0 = P) (hproj : ∀ s, γ s * γ s = γ s)
    (hderiv : ∀ i j, HasDerivAt (fun s => γ s i j) (A i j) 0) :
    P * A + A * P = A := by
  ext i j
  have hm := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hderiv i k).mul (hderiv k j))
  simp only [Pi.mul_apply] at hm
  have hsame : (fun s => ∑ k, γ s i k * γ s k j) = (fun s => γ s i j) := by
    funext s
    exact congrArg (fun M : Matrix ι ι ℂ => M i j) (hproj s)
  rw [hsame] at hm
  have he := hm.unique (hderiv i j)
  rw [h0] at he
  simpa only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib, add_comm] using he

theorem derivative_of_trace_one_curve (γ : ℝ → Matrix ι ι ℂ) (A : Matrix ι ι ℂ)
    (htrace : ∀ s, Matrix.trace (γ s) = 1)
    (hderiv : ∀ i j, HasDerivAt (fun s => γ s i j) (A i j) 0) :
    Matrix.trace A = 0 := by
  have ht := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hderiv i i)
  have he : (fun s => ∑ i, γ s i i) = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    exact htrace s
  rw [he] at ht
  exact ht.unique (hasDerivAt_const 0 (1 : ℂ))

theorem directional_sld {J : Type*} [Fintype J]
    (P : Matrix ι ι ℂ) (A L : J → Matrix ι ι ℂ) (u : J → ℝ)
    (h : ∀ j, P * L j + L j * P = (2 : ℝ) • A j) :
    P * (∑ j, u j • L j) + (∑ j, u j • L j) * P =
      (2 : ℝ) • (∑ j, u j • A j) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_add_distrib, ← smul_add, Finset.smul_sum, h, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

end
end QubitOracle.Paper.LiteralMatrixCalculus
