import QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

namespace QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMomentClosed

/-!
# Closing the finite-product fourth-moment bridge

This module proves the two fields of
`PureLinearFiniteProductIntegralBridge` from the concrete independent fair
shot family.  It introduces no axiom and leaves no probabilistic premise in
the fourth-moment formulas.
-/

private theorem finite_integrable_of_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] [Finite Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → ℝ} (hf : Measurable f) : Integrable f mu := by
  exact Integrable.of_finite

private theorem integral_add_pointwise
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f g : Omega → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu) :
    (∫ omega, f omega + g omega ∂mu) =
      (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) := by
  simpa only [Pi.add_apply] using integral_add hf hg

private theorem integral_add_three_pointwise
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f g h : Omega → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu) (hh : Integrable h mu) :
    (∫ omega, f omega + g omega + h omega ∂mu) =
      (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) := by
  calc
    (∫ omega, f omega + g omega + h omega ∂mu) =
        (∫ omega, f omega + g omega ∂mu) +
          (∫ omega, h omega ∂mu) :=
      integral_add_pointwise (hf.add hg) hh
    _ = (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) := by
      rw [integral_add_pointwise hf hg]

private theorem integral_add_four_pointwise
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f g h k : Omega → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hh : Integrable h mu) (hk : Integrable k mu) :
    (∫ omega, f omega + g omega + h omega + k omega ∂mu) =
      (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) + (∫ omega, k omega ∂mu) := by
  calc
    (∫ omega, f omega + g omega + h omega + k omega ∂mu) =
        (∫ omega, f omega + g omega + h omega ∂mu) +
          (∫ omega, k omega ∂mu) :=
      integral_add_pointwise ((hf.add hg).add hh) hk
    _ = (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) + (∫ omega, k omega ∂mu) := by
      rw [integral_add_three_pointwise hf hg hh]

private theorem integral_add_five_pointwise
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f g h k l : Omega → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hh : Integrable h mu) (hk : Integrable k mu) (hl : Integrable l mu) :
    (∫ omega, f omega + g omega + h omega + k omega + l omega ∂mu) =
      (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) + (∫ omega, k omega ∂mu) +
          (∫ omega, l omega ∂mu) := by
  calc
    (∫ omega, f omega + g omega + h omega + k omega + l omega ∂mu) =
        (∫ omega, f omega + g omega + h omega + k omega ∂mu) +
          (∫ omega, l omega ∂mu) :=
      integral_add_pointwise (((hf.add hg).add hh).add hk) hl
    _ = (∫ omega, f omega ∂mu) + (∫ omega, g omega ∂mu) +
        (∫ omega, h omega ∂mu) + (∫ omega, k omega ∂mu) +
          (∫ omega, l omega ∂mu) := by
      rw [integral_add_four_pointwise hf hg hh hk]

/-- Independence factors arbitrary powers of two real random variables. -/
private theorem integral_mul_powers_of_indep
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {S Z : Omega → ℝ}
    (hSZ : IndepFun S Z mu)
    (hS : Measurable S) (hZ : Measurable Z)
    (r t : ℕ) :
    (∫ omega, S omega ^ r * Z omega ^ t ∂mu) =
      (∫ omega, S omega ^ r ∂mu) *
        (∫ omega, Z omega ^ t ∂mu) := by
  simpa only [Function.comp_apply, Pi.mul_apply, id_eq] using
    hSZ.integral_comp_mul_comp
      hS.aemeasurable hZ.aemeasurable
      ((measurable_id.pow_const r).aestronglyMeasurable)
      ((measurable_id.pow_const t).aestronglyMeasurable)

/-- The first four moments of a finite sum of independent, centered fair
Rademacher variables.  The induction is finite and uses no limit theorem. -/
private theorem finite_iIndep_rademacher_sum_moments
    {Omega Index : Type*} [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] [Finite Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Index → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hMeas : ∀ i : Index, Measurable (X i))
    (hFirst : ∀ i : Index, (∫ omega, X i omega ∂mu) = 0)
    (hSecond : ∀ i : Index, (∫ omega, X i omega ^ 2 ∂mu) = 1)
    (hThird : ∀ i : Index, (∫ omega, X i omega ^ 3 ∂mu) = 0)
    (hFourth : ∀ i : Index, (∫ omega, X i omega ^ 4 ∂mu) = 1)
    (s : Finset Index) :
    ((∫ omega, (∑ i ∈ s, X i omega) ∂mu) = 0) ∧
      ((∫ omega, (∑ i ∈ s, X i omega) ^ 2 ∂mu) = (s.card : ℝ)) ∧
      ((∫ omega, (∑ i ∈ s, X i omega) ^ 3 ∂mu) = 0) ∧
      ((∫ omega, (∑ i ∈ s, X i omega) ^ 4 ∂mu) =
        3 * (s.card : ℝ) ^ 2 - 2 * (s.card : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let S : Omega → ℝ := fun omega => ∑ i ∈ s, X i omega
      let Z : Omega → ℝ := X a
      have hSmeas : Measurable S := by
        dsimp only [S]
        exact Finset.measurable_fun_sum s (fun i _ => hMeas i)
      have hZmeas : Measurable Z := hMeas a
      have hSZ : IndepFun S Z mu := by
        have hsumApply :
            S = (∑ i ∈ s, X i) := by
          funext omega
          simp only [S, Finset.sum_apply]
        rw [hsumApply]
        simpa only [Z] using
          hIndep.indepFun_finsetSum_of_notMem hMeas ha
      have ihFirst : (∫ omega, S omega ∂mu) = 0 := by
        simpa only [S] using ih.1
      have ihSecond : (∫ omega, S omega ^ 2 ∂mu) = (s.card : ℝ) := by
        simpa only [S] using ih.2.1
      have ihThird : (∫ omega, S omega ^ 3 ∂mu) = 0 := by
        simpa only [S] using ih.2.2.1
      have ihFourth :
          (∫ omega, S omega ^ 4 ∂mu) =
            3 * (s.card : ℝ) ^ 2 - 2 * (s.card : ℝ) := by
        simpa only [S] using ih.2.2.2
      have hZFirst : (∫ omega, Z omega ∂mu) = 0 := by
        simpa only [Z] using hFirst a
      have hZSecond : (∫ omega, Z omega ^ 2 ∂mu) = 1 := by
        simpa only [Z] using hSecond a
      have hZThird : (∫ omega, Z omega ^ 3 ∂mu) = 0 := by
        simpa only [Z] using hThird a
      have hZFourth : (∫ omega, Z omega ^ 4 ∂mu) = 1 := by
        simpa only [Z] using hFourth a
      have hS1 : Integrable S mu :=
        finite_integrable_of_measurable mu hSmeas
      have hZ1 : Integrable Z mu :=
        finite_integrable_of_measurable mu hZmeas
      have hS2 : Integrable (fun omega => S omega ^ 2) mu :=
        finite_integrable_of_measurable mu (hSmeas.pow_const 2)
      have hZ2 : Integrable (fun omega => Z omega ^ 2) mu :=
        finite_integrable_of_measurable mu (hZmeas.pow_const 2)
      have hS3 : Integrable (fun omega => S omega ^ 3) mu :=
        finite_integrable_of_measurable mu (hSmeas.pow_const 3)
      have hZ3 : Integrable (fun omega => Z omega ^ 3) mu :=
        finite_integrable_of_measurable mu (hZmeas.pow_const 3)
      have hS4 : Integrable (fun omega => S omega ^ 4) mu :=
        finite_integrable_of_measurable mu (hSmeas.pow_const 4)
      have hZ4 : Integrable (fun omega => Z omega ^ 4) mu :=
        finite_integrable_of_measurable mu (hZmeas.pow_const 4)
      have h11 : (∫ omega, S omega * Z omega ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 1 1
        simpa only [pow_one, ihFirst, hZFirst, zero_mul] using h
      have h21 : (∫ omega, S omega ^ 2 * Z omega ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 2 1
        simpa only [pow_one, ihSecond, hZFirst, mul_zero] using h
      have h12 : (∫ omega, S omega * Z omega ^ 2 ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 1 2
        simpa only [pow_one, ihFirst, hZSecond, zero_mul] using h
      have h31 : (∫ omega, S omega ^ 3 * Z omega ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 3 1
        simpa only [pow_one, ihThird, hZFirst, zero_mul] using h
      have h22 :
          (∫ omega, S omega ^ 2 * Z omega ^ 2 ∂mu) = (s.card : ℝ) := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 2 2
        simpa only [ihSecond, hZSecond, mul_one] using h
      have h13 : (∫ omega, S omega * Z omega ^ 3 ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep hSZ hSmeas hZmeas 1 3
        simpa only [pow_one, ihFirst, hZThird, zero_mul] using h
      have hTwo11 : Integrable (fun omega => 2 * (S omega * Z omega)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul (hSmeas.mul hZmeas))
      have hThree21 :
          Integrable (fun omega => 3 * (S omega ^ 2 * Z omega)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul ((hSmeas.pow_const 2).mul hZmeas))
      have hThree12 :
          Integrable (fun omega => 3 * (S omega * Z omega ^ 2)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul (hSmeas.mul (hZmeas.pow_const 2)))
      have hFour31 :
          Integrable (fun omega => 4 * (S omega ^ 3 * Z omega)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul ((hSmeas.pow_const 3).mul hZmeas))
      have hSix22 :
          Integrable (fun omega => 6 * (S omega ^ 2 * Z omega ^ 2)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul
            ((hSmeas.pow_const 2).mul (hZmeas.pow_const 2)))
      have hFour13 :
          Integrable (fun omega => 4 * (S omega * Z omega ^ 3)) mu :=
        finite_integrable_of_measurable mu
          (measurable_const.mul (hSmeas.mul (hZmeas.pow_const 3)))
      have hm1 : (∫ omega, Z omega + S omega ∂mu) = 0 := by
        rw [integral_add hZ1 hS1, hFirst a, ihFirst]
        norm_num
      have hm2 :
          (∫ omega, (Z omega + S omega) ^ 2 ∂mu) = (s.card : ℝ) + 1 := by
        calc
          (∫ omega, (Z omega + S omega) ^ 2 ∂mu) =
              ∫ omega,
                S omega ^ 2 + 2 * (S omega * Z omega) + Z omega ^ 2
              ∂mu := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega => by ring
          _ =
              (∫ omega, S omega ^ 2 ∂mu) +
                2 * (∫ omega, S omega * Z omega ∂mu) +
                (∫ omega, Z omega ^ 2 ∂mu) := by
                  simpa only [integral_const_mul] using
                    (integral_add_three_pointwise hS2 hTwo11 hZ2)
          _ = (s.card : ℝ) + 1 := by
                rw [ihSecond, h11, hZSecond]
                ring
      have hm3 : (∫ omega, (Z omega + S omega) ^ 3 ∂mu) = 0 := by
        calc
          (∫ omega, (Z omega + S omega) ^ 3 ∂mu) =
              ∫ omega,
                S omega ^ 3 + 3 * (S omega ^ 2 * Z omega) +
                  3 * (S omega * Z omega ^ 2) + Z omega ^ 3
              ∂mu := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega => by ring
          _ =
              (∫ omega, S omega ^ 3 ∂mu) +
                3 * (∫ omega, S omega ^ 2 * Z omega ∂mu) +
                3 * (∫ omega, S omega * Z omega ^ 2 ∂mu) +
                (∫ omega, Z omega ^ 3 ∂mu) := by
                  simpa only [integral_const_mul] using
                    (integral_add_four_pointwise hS3 hThree21 hThree12 hZ3)
          _ = 0 := by
                rw [ihThird, h21, h12, hZThird]
                ring
      have hm4 :
          (∫ omega, (Z omega + S omega) ^ 4 ∂mu) =
            3 * ((s.card : ℝ) + 1) ^ 2 - 2 * ((s.card : ℝ) + 1) := by
        calc
          (∫ omega, (Z omega + S omega) ^ 4 ∂mu) =
              ∫ omega,
                S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                  6 * (S omega ^ 2 * Z omega ^ 2) +
                  4 * (S omega * Z omega ^ 3) + Z omega ^ 4
              ∂mu := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega => by ring
          _ =
              (∫ omega, S omega ^ 4 ∂mu) +
                4 * (∫ omega, S omega ^ 3 * Z omega ∂mu) +
                6 * (∫ omega, S omega ^ 2 * Z omega ^ 2 ∂mu) +
                4 * (∫ omega, S omega * Z omega ^ 3 ∂mu) +
                (∫ omega, Z omega ^ 4 ∂mu) := by
                  simpa only [integral_const_mul] using
                    (integral_add_five_pointwise
                      hS4 hFour31 hSix22 hFour13 hZ4)
          _ = 3 * ((s.card : ℝ) + 1) ^ 2 - 2 * ((s.card : ℝ) + 1) := by
                rw [ihFourth, h31, h22, h13, hZFourth]
                ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [Finset.sum_insert ha, S, Z] using hm1
      · simpa only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
          Nat.cast_add, Nat.cast_one, S, Z] using hm2
      · simpa only [Finset.sum_insert ha, S, Z] using hm3
      · simpa only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
          Nat.cast_add, Nat.cast_one, S, Z] using hm4

private def pureLinearAxisEmbedding (q : ℕ) (axis : Fin 2) :
    Fin q ↪
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q where
  toFun shot := (axis, shot)
  inj' := by
    intro i j hij
    exact congrArg Prod.snd hij

private def pureLinearAxisShotSet (q : ℕ) (axis : Fin 2) :
    Finset
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q) :=
  Finset.univ.map (pureLinearAxisEmbedding q axis)

private theorem pureLinearAxisShotSet_card (q : ℕ) (axis : Fin 2) :
    (pureLinearAxisShotSet q axis).card = q := by
  simp [pureLinearAxisShotSet]

private theorem pureLinearAxisShotSets_disjoint (q : ℕ) :
    Disjoint
      (pureLinearAxisShotSet q (0 : Fin 2))
      (pureLinearAxisShotSet q (1 : Fin 2)) := by
  classical
  rw [Finset.disjoint_left]
  intro index hzero hone
  rcases Finset.mem_map.mp hzero with ⟨shot, _, rfl⟩
  rcases Finset.mem_map.mp hone with ⟨oneShot, _, heq⟩
  have haxis := congrArg
    (fun index :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q =>
        index.1.1) heq
  change (1 : ℕ) = 0 at haxis
  norm_num at haxis

private def pureLinearAxisEquiv (q : ℕ) (axis : Fin 2) :
    Fin q ≃ ↥(pureLinearAxisShotSet q axis) where
  toFun shot := ⟨(axis, shot), by
    refine Finset.mem_map.mpr ⟨shot, Finset.mem_univ _, ?_⟩
    rfl⟩
  invFun index := index.1.2
  left_inv shot := rfl
  right_inv index := by
    apply Subtype.ext
    rcases Finset.mem_map.mp index.property with ⟨shot, _, heq⟩
    change (axis, index.1.2) = index.1
    change (axis, shot) = index.1 at heq
    have hfirst : axis = index.1.1 := by
      exact congrArg
        (fun pair :
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q =>
            pair.1) heq
    apply Prod.ext
    · exact hfirst
    · rfl

private theorem pureLinearAxisSubtypeSum_eq_raw
    (q : ℕ) (axis : Fin 2)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    (∑ index : ↥(pureLinearAxisShotSet q axis),
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
          q index.1 omega) =
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
        q axis omega := by
  classical
  unfold QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
  exact (Fintype.sum_equiv
    (pureLinearAxisEquiv q axis)
    (fun shot : Fin q =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q (axis, shot) omega)
    (fun index : ↥(pureLinearAxisShotSet q axis) =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q index.1 omega)
    (fun _ => rfl)).symm

private theorem pureLinearAxisFinsetSum_eq_raw
    (q : ℕ) (axis : Fin 2)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    (∑ index ∈ pureLinearAxisShotSet q axis,
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q index omega) =
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
        q axis omega := by
  classical
  calc
    (∑ index ∈ pureLinearAxisShotSet q axis,
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q index omega) =
        ∑ index : ↥(pureLinearAxisShotSet q axis),
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
            q index.1 omega := by
      symm
      simpa using
        (Finset.sum_attach
          (pureLinearAxisShotSet q axis)
          (fun index =>
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
              q index omega))
    _ =
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
        q axis omega := pureLinearAxisSubtypeSum_eq_raw q axis omega

private theorem pureLinearShot_cube
    (q : ℕ)
    (index :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot q index omega ^ 3 =
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot q index omega := by
  cases h : omega index <;>
    norm_num [QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot,
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearBoolSign, h]

private theorem pureLinearShot_fourth_eq_square
    (q : ℕ)
    (index :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot q index omega ^ 4 =
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot q index omega ^ 2 := by
  cases h : omega index <;>
    norm_num [QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot,
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearBoolSign, h]

private theorem pureLinearShot_thirdMoment
    (q : ℕ)
    (index :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
          q index omega ^ 3
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) = 0 := by
  calc
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
          q index omega ^ 3
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        ∫ omega,
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
            q index omega
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (pureLinearShot_cube q index)
    _ = 0 :=
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_mean_zero
        q index

private theorem pureLinearShot_fourthMoment
    (q : ℕ)
    (index :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearShotIndex q) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
          q index omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) = 1 := by
  calc
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
          q index omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        ∫ omega,
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
            q index omega ^ 2
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (pureLinearShot_fourth_eq_square q index)
    _ = 1 :=
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_secondMoment_one
        q index

/-- The actual one-axis raw sum has the combinatorial fourth moment. -/
theorem pureLinearRawAxisFourth
    (q : ℕ) (axis : Fin 2) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
            q axis omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.fairRademacherFourthMoment q := by
  classical
  let shotFamily :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot q
  have hmoments :=
    finite_iIndep_rademacher_sum_moments
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q)
      shotFamily
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShots_iIndepFun q)
      (fun index =>
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_measurable
          q index)
      (fun index =>
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_mean_zero
          q index)
      (fun index =>
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_secondMoment_one
          q index)
      (pureLinearShot_thirdMoment q)
      (pureLinearShot_fourthMoment q)
      (pureLinearAxisShotSet q axis)
  have hfourth := hmoments.2.2.2
  rw [pureLinearAxisShotSet_card] at hfourth
  calc
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearRawAxisSum
            q axis omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        ∫ omega,
          (∑ index ∈ pureLinearAxisShotSet q axis,
            shotFamily index omega) ^ 4
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun omega => by
            dsimp only [shotFamily]
            rw [pureLinearAxisFinsetSum_eq_raw]
    _ = 3 * (q : ℝ) ^ 2 - 2 * (q : ℝ) := hfourth
    _ =
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.fairRademacherFourthMoment q :=
      (QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.fairRademacherFourthMoment_eq
        q).symm

/-- The two coordinate estimators are functions of disjoint independent shot
blocks, hence their squares have factored expectation. -/
theorem pureLinearAxisSquareFactorization (q : ℕ) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (0 : Fin 2) omega ^ 2 *
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (1 : Fin 2) omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      (∫ omega,
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
              q (0 : Fin 2) omega ^ 2
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) *
        (∫ omega,
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
                q (1 : Fin 2) omega ^ 2
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) := by
  classical
  let S0 := pureLinearAxisShotSet q (0 : Fin 2)
  let S1 := pureLinearAxisShotSet q (1 : Fin 2)
  let U :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q →
        (index : ↥S0) → ℝ :=
    fun omega index =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q index.1 omega
  let V :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q →
        (index : ↥S1) → ℝ :=
    fun omega index =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q index.1 omega
  let F : ((index : ↥S0) → ℝ) → ℝ :=
    fun z => ((∑ index : ↥S0, z index) / (q : ℝ)) ^ 2
  let G : ((index : ↥S1) → ℝ) → ℝ :=
    fun z => ((∑ index : ↥S1, z index) / (q : ℝ)) ^ 2
  have hU : Measurable U := by
    dsimp only [U]
    exact measurable_pi_lambda _ fun index =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_measurable
        q index.1
  have hV : Measurable V := by
    dsimp only [V]
    exact measurable_pi_lambda _ fun index =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_measurable
        q index.1
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have hG : Measurable G := by
    dsimp only [G]
    fun_prop
  have hUV : IndepFun U V
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) := by
    dsimp only [U, V, S0, S1]
    exact ProbabilityTheory.iIndepFun.indepFun_finset
      (pureLinearAxisShotSet q (0 : Fin 2))
      (pureLinearAxisShotSet q (1 : Fin 2))
      (pureLinearAxisShotSets_disjoint q)
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShots_iIndepFun q)
      (fun index =>
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_measurable
          q index)
  have hfactor :=
    hUV.integral_comp_mul_comp
      hU.aemeasurable hV.aemeasurable
      hF.aestronglyMeasurable hG.aestronglyMeasurable
  have hFU
      (omega :
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
      F (U omega) =
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
          q (0 : Fin 2) omega ^ 2 := by
    dsimp only [F, U, S0]
    rw [pureLinearAxisSubtypeSum_eq_raw]
    rfl
  have hGV
      (omega :
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
      G (V omega) =
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
          q (1 : Fin 2) omega ^ 2 := by
    dsimp only [G, V, S1]
    rw [pureLinearAxisSubtypeSum_eq_raw]
    rfl
  simpa only [Function.comp_apply, Pi.mul_apply, hFU, hGV] using hfactor

/-- Both fields of the formerly explicit finite-product bridge are now
constructed from the concrete fair product experiment. -/
theorem pureLinearFiniteProductIntegralBridge_closed :
    QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.PureLinearFiniteProductIntegralBridge := by
  exact
    { rawAxisFourth := pureLinearRawAxisFourth
      axisSquareFactorization := pureLinearAxisSquareFactorization }

/-! ## Unconditional instantiations -/

theorem pureLinearCoordinateEstimator_fourthMoment_closed
    {q : ℕ} (hq : 0 < q) (axis : Fin 2) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q axis omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      3 / (q : ℝ) ^ 2 - 2 / (q : ℝ) ^ 3 :=
  QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearCoordinateEstimator_fourthMoment
    pureLinearFiniteProductIntegralBridge_closed hq axis

theorem pureLinearCoordinateEstimator_crossSquareMoment_closed
    {q : ℕ} (hq : 0 < q) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (0 : Fin 2) omega ^ 2 *
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (1 : Fin 2) omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      1 / (q : ℝ) ^ 2 :=
  QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearCoordinateEstimator_crossSquareMoment
    pureLinearFiniteProductIntegralBridge_closed hq

theorem pureLinearSquaredRadius_fourthMoment_closed
    {q : ℕ} (hq : 0 < q) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
            q omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3 :=
  QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius_fourthMoment
    pureLinearFiniteProductIntegralBridge_closed hq

theorem pureLinearScaledBuresRemainderEnvelope_tendsto_zero_closed :
    Tendsto
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope
      atTop (𝓝 0) :=
  QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope_tendsto_zero
    pureLinearFiniteProductIntegralBridge_closed

/-
The remaining paper-facing connector is deliberately not guessed here.  Its
exact required statement is that the concrete scaled expected chart-Bures
remainder

  (2*q) * E[chartBuresSq(estimator) - quadraticLoss(estimator)]

is nonnegative and at most
`pureLinearScaledBuresRemainderEnvelope q`, together with the identity saying
that the scaled expected chart-Bures risk is `1` plus that remainder.  The
retained pointwise theorem `pureLinearChartBuresSq_remainder_bounds` is the
source of the inequality; only its integral-level notation must be connected.
-/

end QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMomentClosed
