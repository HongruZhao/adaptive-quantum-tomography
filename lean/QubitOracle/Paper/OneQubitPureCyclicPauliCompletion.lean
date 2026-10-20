import QubitOracle.Paper.OneQubitPureCyclicPauliLAN

open scoped BigOperators Topology
open Filter

namespace QubitOracle.Paper

/-- Every fixed two-dimensional pure-state local direction enters the valid chart eventually. -/
theorem pureCyclicPauliLocalChart_eventually_valid (h : Fin 2 → ℝ) :
    ∀ᶠ q : ℕ in atTop, PureCyclicPauliLocalChartValid q h := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have htilt (axis : Fin 2) :
      Tendsto (fun q => pureCyclicPauliLocalTilt q h axis) atTop (𝓝 0) := by
    change Tendsto (fun q : ℕ => (Real.sqrt 2 * h axis) * (Real.sqrt (q : ℝ))⁻¹)
      atTop (𝓝 0)
    simpa [pureCyclicPauliLocalTilt, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hinv.const_mul (Real.sqrt 2 * h axis)
  have hsum : Tendsto
      (fun q => pureCyclicPauliLocalTilt q h 0 ^ 2 +
        pureCyclicPauliLocalTilt q h 1 ^ 2) atTop (𝓝 0) := by
    convert (htilt 0).pow 2 |>.add ((htilt 1).pow 2) using 1 <;> ring
  have hle : ∀ᶠ q : ℕ in atTop,
      pureCyclicPauliLocalTilt q h 0 ^ 2 +
        pureCyclicPauliLocalTilt q h 1 ^ 2 ≤ 1 :=
    ((tendsto_order.1 hsum).2 1 (by norm_num)).mono fun _ hq => le_of_lt hq
  filter_upwards [eventually_ge_atTop 1, hle] with q hq htilts
  exact ⟨lt_of_lt_of_le Nat.zero_lt_one hq, htilts⟩

/-- The pure local Bloch chart therefore represents norm-one qubit states eventually. -/
theorem pureCyclicPauliLocalBloch_eventually_normSq_one (h : Fin 2 → ℝ) :
    ∀ᶠ q : ℕ in atTop,
      pureCyclicPauliBlochNormSq (pureCyclicPauliLocalBloch q h) = 1 := by
  filter_upwards [pureCyclicPauliLocalChart_eventually_valid h] with q hvalid
  exact pureCyclicPauliLocalBloch_normSq_eq_one hvalid

end QubitOracle.Paper
