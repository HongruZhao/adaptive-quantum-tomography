import QubitOracle.Paper.MartingaleCLT

/-!
# Adaptive LAN assembly in convergence in probability

The stochastic error notion is Mathlib's `TendstoInMeasure`, which is
convergence in probability on a probability space.  This file proves the
addition closure needed to combine the regular Taylor, Hessian replacement,
and exceptional-round comparison errors, then joins that result with the
audited martingale-CLT interface.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory

noncomputable section

/-- Sum of two real random errors converging to zero in probability also
converges to zero in probability. -/
theorem tendstoInMeasure_add_zero_real
    {Omega I : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {l : Filter I}
    {f g : I -> Omega -> ℝ}
    (hf : TendstoInMeasure mu f l 0)
    (hg : TendstoInMeasure mu g l 0) :
    TendstoInMeasure mu (fun i omega => f i omega + g i omega) l 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hf' := hf (epsilon / 2) hhalf
  have hg' := hg (epsilon / 2) hhalf
  have hsum : Tendsto (fun i =>
      mu {omega | epsilon / 2 ≤ ‖f i omega‖} +
        mu {omega | epsilon / 2 ≤ ‖g i omega‖}) l (nhds 0) := by
    simpa using hf'.add hg'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) ?_
  intro i
  simp only [Pi.zero_apply, sub_zero]
  calc
    mu {omega | epsilon ≤ ‖f i omega + g i omega‖} ≤
        mu ({omega | epsilon / 2 ≤ ‖f i omega‖} ∪
          {omega | epsilon / 2 ≤ ‖g i omega‖}) := by
      apply measure_mono
      intro omega homega
      change epsilon ≤ ‖f i omega + g i omega‖ at homega
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_cases hfhalf : epsilon / 2 ≤ ‖f i omega‖
      · exact Or.inl hfhalf
      · right
        have hf_lt : ‖f i omega‖ < epsilon / 2 := lt_of_not_ge hfhalf
        by_contra hghalf
        have hg_lt : ‖g i omega‖ < epsilon / 2 := lt_of_not_ge hghalf
        have htriangle := norm_add_le (f i omega) (g i omega)
        linarith
    _ ≤ mu {omega | epsilon / 2 ≤ ‖f i omega‖} +
        mu {omega | epsilon / 2 ≤ ‖g i omega‖} := measure_union_le _ _

/-- Three explicit stochastic error terms whose sum is the full uniform LAN
error. -/
structure AdaptiveLANErrorProblem
    (Omega : Type*) [MeasurableSpace Omega] (mu : Measure Omega) where
  regularTaylorError : ℕ -> Omega -> ℝ
  hessianReplacementError : ℕ -> Omega -> ℝ
  exceptionalComparisonError : ℕ -> Omega -> ℝ
  fullLANError : ℕ -> Omega -> ℝ
  fullLANError_decomposition : ∀ n,
    fullLANError n =ᵐ[mu] fun omega =>
      (regularTaylorError n omega + hessianReplacementError n omega) +
        exceptionalComparisonError n omega

/-- The three convergent error components imply convergence of the full LAN
error in probability. -/
theorem adaptiveLANError_tendstoInMeasure
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANErrorProblem Omega mu)
    (hregular : TendstoInMeasure mu problem.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.exceptionalComparisonError atTop 0) :
    TendstoInMeasure mu problem.fullLANError atTop 0 := by
  have hregularHessian :=
    tendstoInMeasure_add_zero_real hregular hhessian
  have hall := tendstoInMeasure_add_zero_real hregularHessian hexception
  exact hall.congr_left fun n => (problem.fullLANError_decomposition n).symm

/-- General data for the score-CLT and full-LAN assembly. -/
structure AdaptiveLANProblem
    (D Omega : Type*) [Fintype D] [MeasurableSpace Omega]
    (mu : Measure Omega) where
  martingale : MartingaleCLTProblem D
  errors : AdaptiveLANErrorProblem Omega mu

/-- Adaptive LAN from explicit martingale and three-error convergence
conditions.  The only project axiom used is the named Hall--Heyde CLT
interface. -/
theorem adaptive_quantum_LAN_of_conditions
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANProblem D Omega mu) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.martingale.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.martingale.HasConditionalLindeberg)
    (hCovariance : problem.martingale.ConditionalCovarianceConverges M)
    (hregular : TendstoInMeasure mu problem.errors.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.errors.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.errors.exceptionalComparisonError atTop 0) :
    problem.martingale.SumConvergesToGaussian M ∧
      TendstoInMeasure mu problem.errors.fullLANError atTop 0 := by
  exact ⟨adaptiveScoreCLT_of_martingale_conditions
      problem.martingale M hM hMDS hLindeberg hCovariance,
    adaptiveLANError_tendstoInMeasure problem.errors
      hregular hhessian hexception⟩

end

end QubitOracle.Paper
