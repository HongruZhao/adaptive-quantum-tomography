import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Module.Basic

/-! Elementary convergence-in-probability operations, with no statistical axiom. -/

namespace QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators
noncomputable section

variable {Omega J E F : Type*} [MeasurableSpace Omega]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  {mu : Measure Omega} {l : Filter J}

theorem zero : TendstoInMeasure mu (fun (_ : J) (_ : Omega) => (0 : E)) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon he
  simpa only [sub_self, norm_zero, not_le.mpr he, Set.setOf_false, measure_empty] using
    (tendsto_const_nhds : Tendsto (fun _ : J => (0 : ENNReal)) l (𝓝 0))

theorem add {f g : J → Omega → E}
    (hf : TendstoInMeasure mu f l (fun _ => 0))
    (hg : TendstoInMeasure mu g l (fun _ => 0)) :
    TendstoInMeasure mu (fun n omega => f n omega + g n omega) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  simp only [sub_zero] at hf hg ⊢
  intro epsilon he
  have hsum : Tendsto (fun n => mu {omega | epsilon/2 ≤ ‖f n omega‖} +
      mu {omega | epsilon/2 ≤ ‖g n omega‖}) l (𝓝 0) := by
    simpa using (hf (epsilon/2) (half_pos he)).add (hg (epsilon/2) (half_pos he))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  calc
    _ ≤ mu ({omega | epsilon/2 ≤ ‖f n omega‖} ∪ {omega | epsilon/2 ≤ ‖g n omega‖}) := by
      apply measure_mono
      intro omega ho
      change epsilon ≤ ‖f n omega + g n omega‖ at ho
      change epsilon/2 ≤ ‖f n omega‖ ∨ epsilon/2 ≤ ‖g n omega‖
      by_cases h : epsilon/2 ≤ ‖f n omega‖
      · exact Or.inl h
      · right
        by_contra h'
        have h1 := lt_of_not_ge h
        have h2 := lt_of_not_ge h'
        have h3 := norm_add_le (f n omega) (g n omega)
        linarith
    _ ≤ _ := measure_union_le _ _

theorem dominated {f : J → Omega → E} {g : J → Omega → F}
    (hf : TendstoInMeasure mu f l (fun _ => 0)) (C : ℝ) (hC : 0 < C)
    (hb : ∀ n omega, ‖g n omega‖ ≤ C * ‖f n omega‖) :
    TendstoInMeasure mu g l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  simp only [sub_zero] at hf ⊢
  intro epsilon he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (epsilon/C) (div_pos he hC)) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro omega ho
  change epsilon/C ≤ ‖f n omega‖
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using ho.trans (hb n omega))

theorem smul_fixed [NormedSpace ℝ E] {f : J → Omega → ℝ}
    (hf : TendstoInMeasure mu f l (fun _ => 0)) (v : E) :
    TendstoInMeasure mu (fun n omega => f n omega • v) l (fun _ => 0) := by
  apply dominated hf (‖v‖+1) (by positivity)
  intro n omega
  rw [norm_smul]
  nlinarith [norm_nonneg v, norm_nonneg (f n omega)]

theorem finite_sum {R : Type*} (s : Finset R) (f : R → J → Omega → E)
    (hf : ∀ r ∈ s, TendstoInMeasure mu (f r) l (fun _ => 0)) :
    TendstoInMeasure mu (fun n omega => ∑ r ∈ s, f r n omega) l (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (mu := mu) (l := l) (E := E))
  | @insert r s hr ih =>
    have h := add (hf r (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hr] using h

theorem uniform_norm_bound {g : J → Omega → E} (b : J → ℝ)
    (hb : Tendsto b l (𝓝 0)) (hbound : ∀ n omega, ‖g n omega‖ ≤ b n) :
    TendstoInMeasure mu g l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  simp only [sub_zero]
  intro epsilon he
  have hs := hb.eventually (Iio_mem_nhds he)
  have hz : ∀ᶠ n in l, mu {omega | epsilon ≤ ‖g n omega‖} = 0 := by
    filter_upwards [hs] with n hn
    have heq : {omega | epsilon ≤ ‖g n omega‖} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro omega ho
      exact (not_le_of_gt ((hbound n omega).trans_lt hn)) ho
    rw [heq, measure_empty]
  exact tendsto_const_nhds.congr' (hz.mono (fun _ h => h.symm))

end
end QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
