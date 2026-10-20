import QubitOracle.AdaptiveDesign.ProbabilityCalculus

/-! Products and pathwise localization for stochastic order bounds.
None of these arguments assumes independence of the factors. -/
namespace QubitOracle.AdaptiveDesign.ProbabilityCalculus
open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {Ω E F G : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

theorem tight_product_bound {f : ℕ → Ω → E} {g : ℕ → Ω → F} {z : ℕ → Ω → G}
    (hf : TightNorm μ f atTop) (hg : TightNorm μ g atTop)
    (hz : ∀ n ω, ‖z n ω‖ ≤ ‖f n ω‖*‖g n ω‖) : TightNorm μ z atTop := by
  intro ε hε
  have he : (0:ℝ≥0∞) < ε/2 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨B,hB,hfB⟩ := hf (ε/2) he
  obtain ⟨C,hC,hgC⟩ := hg (ε/2) he
  refine ⟨B*C,mul_pos hB hC,?_⟩
  filter_upwards [hfB,hgC] with n hn hn'
  calc
    _ ≤ μ ({ω | B ≤ ‖f n ω‖} ∪ {ω | C ≤ ‖g n ω‖}) := by
      apply measure_mono
      intro ω hω
      by_cases h : B ≤ ‖f n ω‖
      · exact Or.inl h
      · right
        by_contra hh
        have hb : ‖f n ω‖ < B := lt_of_not_ge h
        have hc : ‖g n ω‖ < C := lt_of_not_ge hh
        have ht : ‖f n ω‖*‖g n ω‖ < B*C :=
          (mul_le_mul_of_nonneg_right hb.le (norm_nonneg _)).trans_lt
            (mul_lt_mul_of_pos_left hc hB)
        exact (not_lt_of_ge hω) ((hz n ω).trans_lt ht)
    _ ≤ μ {ω | B ≤ ‖f n ω‖}+μ {ω | C ≤ ‖g n ω‖} := measure_union_le _ _
    _ ≤ ε/2+ε/2 := add_le_add hn hn'
    _ = ε := ENNReal.add_halves ε

theorem tight_square_norm {f : ℕ → Ω → E} (hf : TightNorm μ f atTop) :
    TightNorm μ (fun n ω => ‖f n ω‖^2) atTop :=
  tight_product_bound hf hf (fun n ω => by simp [pow_two])

theorem tight_of_ae_eventually_bounded {f : ℕ → Ω → E}
    (hm : ∀ n, Measurable (fun ω => ‖f n ω‖))
    (hb : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ᶠ n in atTop, ‖f n ω‖ ≤ B) :
    TightNorm μ f atTop := by
  let S := fun m : ℕ => {ω | ∃ n : ℕ, m ≤ n ∧ (m:ℝ) ≤ ‖f n ω‖}
  have hs (m : ℕ) : MeasurableSet (S m) := by
    have he : S m=⋃ n : ℕ, {ω | m ≤ n ∧ (m:ℝ) ≤ ‖f n ω‖} := by ext; simp [S]
    rw [he]
    exact MeasurableSet.iUnion (fun n => by
      by_cases h : m ≤ n
      · simpa only [h,true_and] using
          (show MeasurableSet {ω | (m:ℝ) ≤ ‖f n ω‖} from measurableSet_le measurable_const (hm n))
      · simp [h])
  have hanti : Antitone S := by
    intro a b hab ω hω
    obtain ⟨n,hn,ht⟩ := hω
    exact ⟨n,hab.trans hn,(show (a:ℝ) ≤ b by exact_mod_cast hab).trans ht⟩
  have hzero : μ (⋂ m, S m)=0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hb] with ω hω
    obtain ⟨B,hB⟩ := hω
    obtain ⟨N,hN⟩ := eventually_atTop.mp hB
    obtain ⟨M,hM⟩ := exists_nat_gt B
    intro hmem
    obtain ⟨n,hn,ht⟩ := Set.mem_iInter.mp hmem (max N M)
    have hbn := hN n ((le_max_left N M).trans hn)
    have hmax : (M:ℝ) ≤ (max N M:ℕ) := by exact_mod_cast le_max_right N M
    linarith
  have hlim := tendsto_measure_iInter_atTop (fun m => (hs m).nullMeasurableSet)
    hanti (show ∃ m, μ (S m) ≠ ∞ from ⟨0,measure_ne_top _ _⟩)
  rw [hzero] at hlim
  intro ε hε
  obtain ⟨N,hN⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  refine ⟨(N:ℝ)+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  apply le_trans (measure_mono ?_) hN.le
  intro ω hω
  change (N:ℝ)+1 ≤ ‖f n ω‖ at hω
  exact ⟨n,hn,by linarith only [hω]⟩

theorem tight_eventual_ae_bound {f : ℕ → Ω → E} {g : ℕ → Ω → F}
    (hmf : ∀ n, Measurable (fun ω => ‖f n ω‖))
    (hmg : ∀ n, Measurable (fun ω => ‖g n ω‖))
    (hg : TightNorm μ g atTop) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ᶠ n in atTop, ‖f n ω‖ ≤ C*‖g n ω‖+B) :
    TightNorm μ f atTop := by
  let r := fun n ω => max (‖f n ω‖-C*‖g n ω‖) 0
  have hr : TightNorm μ r atTop := by
    apply tight_of_ae_eventually_bounded
    · intro n
      exact (((hmf n).sub ((hmg n).const_mul C)).max measurable_const).norm
    · filter_upwards [hb] with ω hω
      obtain ⟨B,hB⟩ := hω
      refine ⟨max B 0,?_⟩
      filter_upwards [hB] with n hn
      dsimp only [r]
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le_max (by linarith) le_rfl
  have hgt : TightNorm μ (fun n ω => (C+1)*‖g n ω‖) atTop := by
    apply tight_dominated hg (C+1) (by positivity)
    intro n ω
    rw [Real.norm_of_nonneg (by positivity)]
  apply tight_dominated (tight_add hgt hr) 1 (by norm_num)
  intro n ω
  rw [one_mul,Real.norm_of_nonneg (add_nonneg (by positivity) (le_max_right _ _))]
  have hh := le_max_left (‖f n ω‖-C*‖g n ω‖) 0
  nlinarith [norm_nonneg (g n ω)]

end
end QubitOracle.AdaptiveDesign.ProbabilityCalculus
