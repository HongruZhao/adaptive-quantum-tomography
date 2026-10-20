import QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding
import QubitOracle.AdaptiveDesign.FiniteGaussianTails
import QubitOracle.AdaptiveDesign.FiniteVarianceMoments

/-! The two conclusions of Lemma S7.1 on arbitrary filtered probability spaces. -/
namespace QubitOracle.AdaptiveDesign.SupplementProbability
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {I : Type*} [Fintype I]

theorem gaussian_tail (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n x, 0 ≤ x →
      μ.real {ω | x ≤ ‖∑ k ∈ Finset.range (n+1), X k ω‖} ≤
        B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
  let D := C+1
  have hD : 0<D := by dsimp [D]; positivity
  have hai (i : I) (n : ℕ) : StronglyMeasurable[F (n+1)] (fun ω => X n ω i) :=
    (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable (ha n)
  have hi (n : ℕ) : Integrable (X n) μ := Integrable.of_bound
    ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (Eventually.of_forall (hb n))
  have hci (i : I) (n : ℕ) : μ[(fun ω => X n ω i) | F n] =ᵐ[μ] 0 := by
    have he := (EuclideanSpace.proj i).comp_condExp_comm (m:=F n) (hi n)
    filter_upwards [he,hc n] with ω heω hcω
    simpa [Function.comp_def,hcω] using heω.symm
  have hbi (i : I) (n : ℕ) (ω : Ω) : ‖X n ω i‖ ≤ D :=
    (PiLp.norm_apply_le (X n ω) i).trans ((hb n ω).trans (by dsimp [D]; linarith))
  have ht (i : I) : ∃ B c : ℝ, 0<B ∧ 0<c ∧ ∀ n x, 0≤x →
      μ.real {ω | x ≤ |∑ k ∈ Finset.range (n+1), X k ω i|} ≤
        B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
    refine ⟨2,(2*D^2)⁻¹,by norm_num,by positivity,fun n x hx => ?_⟩
    have hsg := BoundedMartingaleHoeffding.partialSum_subGaussian F
      (fun k ω => X k ω i) (hai i) (hci i) D hD (hbi i) (n+1)
    have hh := BoundedResponseQuarterRate.subGaussian_twoSided μ
      (partialSum (fun k ω => X k ω i) (n+1))
      ⟨((n+1:ℕ):ℝ)*D^2,by positivity⟩ hsg x hx
    change μ.real {ω | x ≤ |∑ k ∈ Finset.range (n+1), X k ω i|} ≤
      2*Real.exp (-x^2/(2*(((n+1:ℕ):ℝ)*D^2))) at hh
    convert hh using 1 <;> congr 2 <;> ring
  obtain ⟨B,c,hB,hc',ht'⟩ := AdaptiveGaussianTails.finiteSum
    (fun i n ω => ∑ k ∈ Finset.range (n+1), X k ω i) ht
  refine ⟨B,c,hB,hc',fun n x hx => (measureReal_mono ?_).trans (ht' n x hx)⟩
  intro ω hω
  change x ≤ ∑ i, |∑ k ∈ Finset.range (n+1), X k ω i|
  apply (show x ≤ ‖∑ k ∈ Finset.range (n+1), X k ω‖ from hω).trans
  simpa only [WithLp.ofLp_sum,Finset.sum_apply] using
    BoundedVarianceMGF.euclidean_norm_le_sum_abs (∑ k ∈ Finset.range (n+1), X k ω)

theorem real_moments (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun ω => ‖∑ k ∈ Finset.range (n+1), X k ω‖^r) μ ∧
      (∫ ω, ‖∑ k ∈ Finset.range (n+1), X k ω‖^r ∂μ) ≤ K*((n+1:ℕ):ℝ)^(r/2) := by
  have hv (k : ℕ) : ∀ᵐ ω ∂μ, μ[fun ω => ‖X k ω‖^2 | F k] ω ≤ C^2 := by
    have hh := ae_bdd_norm_condExp_of_ae_bdd_norm (m:=F k) (μ:=μ)
      (Eventually.of_forall (fun ω => show ‖‖X k ω‖^2‖ ≤ C^2 from by
        rw [norm_pow,norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb k ω) 2))
    filter_upwards [hh] with ω hω
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hω)
  obtain ⟨K,hK,hKm⟩ := BoundedVarianceMGF.vector_real_moments F X ha hc C hC hb
    (fun _ => C^2) hv (fun n => (n:ℝ)*C^2) (fun _ => by positivity)
    (fun n => by simp) r hr
  refine ⟨K*(1+C^2)^(r/2),by positivity,fun n => ⟨(hKm (n+1)).1,?_⟩⟩
  have hbase : 1+((n+1:ℕ):ℝ)*C^2 ≤ ((n+1:ℕ):ℝ)*(1+C^2) := by
    have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  apply (hKm (n+1)).2.trans
  calc
    _ ≤ K*(((n+1:ℕ):ℝ)*(1+C^2))^(r/2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase (by positivity)) hK
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

end
end QubitOracle.AdaptiveDesign.SupplementProbability
