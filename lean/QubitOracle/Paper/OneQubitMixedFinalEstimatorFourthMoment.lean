import QubitOracle.Paper.OneQubitMixedLinearEstimatorRisk
import QubitOracle.Paper.OneQubitMixedLocalBuresRadius
import QubitOracle.Paper.OneQubitMixedPilotFrameRiskTransfer
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder
import Mathlib.Probability.Independence.Basic

/-!
# Fourth moments for the conditional mixed-qubit final estimator

For `q > 0`, the experiment measures each column of an arbitrary orthonormal
three-dimensional frame exactly `q` times.  In frame coordinates this is the
explicit `PauliPilotPath q` product mass.  The estimator is the vector of three
signed sample means, reconstructed in the physical Bloch frame.

The exact biased-Rademacher calculation gives, with
`v_j = 1 - z_j^2` and `m4_j = 1 + 2 z_j^2 - 3 z_j^4`,

`E[e_j^4] = (q*m4_j + 3*q*(q-1)*v_j^2)/q^4 <= 3/q^2`.

Distinct coordinate squares factor exactly.  Consequently

`E[||error||^4] <= 15/q^2`,
`E[||error||^3] <= 18/(q*sqrt q)`, and
`P(||error|| > eta) <= 15/(q^2*eta^4)`.

All expectations and event masses are finite sums under the explicit product
mass.  No projection, exact Bures risk, or asymptotic theorem is introduced.
-/

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

namespace QubitOracle.Paper

local instance mixedFinalMomentPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedFinalMomentPathMeasurableSingletonClass (q : ℕ) :
    MeasurableSingletonClass (PauliPilotPath q) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-! ## Finite-space analytic helpers -/

private theorem finite_integrable_of_measurable_mixed
    {Omega : Type*} [MeasurableSpace Omega] [Fintype Omega]
    [MeasurableSingletonClass Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → ℝ} (hf : Measurable f) : Integrable f mu := by
  exact Integrable.of_finite

private theorem integral_mul_powers_of_indep_mixed
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

/-- Convert the project's exact finite rectangle factorization into Mathlib's
finite-family independence interface. -/
private theorem finiteIndependentRealFamily_to_iIndepFun
    {Omega : Type*} [MeasurableSpace Omega] {q : ℕ}
    {mu : Measure Omega} {X : Fin q → Omega → ℝ}
    (hProbability : mu univ = 1)
    (hIndependent : FiniteIndependentRealFamily mu X) :
    iIndepFun X mu := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hSets
  let events : Fin q → Set ℝ := fun i =>
    if i ∈ S then sets i else univ
  have hEvents : ∀ i, MeasurableSet (events i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [events, hi] using hSets i hi
    · simp [events, hi]
  have hFull := hIndependent events hEvents
  have hIntersection :
      (⋂ i : Fin q, X i ⁻¹' events i) =
        ⋂ i ∈ S, X i ⁻¹' sets i := by
    ext omega
    simp [events]
  rw [← hIntersection, hFull]
  calc
    (∏ i : Fin q, mu (X i ⁻¹' events i)) =
        ∏ i ∈ S, mu (X i ⁻¹' events i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i _ hi
      simp [events, hi, hProbability]
    _ = ∏ i ∈ S, mu (X i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [events, hi]

/-- First, second, and fourth moments of a finite sum of independent centered
variables with common second moment `v` and common fourth moment `m4`. -/
private theorem finite_iIndep_centered_sum_fourth
    {Omega Index : Type*} [MeasurableSpace Omega] [Fintype Omega]
    [MeasurableSingletonClass Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Index → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hMeas : ∀ i : Index, Measurable (X i))
    (v m4 : ℝ)
    (hFirst : ∀ i : Index, (∫ omega, X i omega ∂mu) = 0)
    (hSecond : ∀ i : Index, (∫ omega, X i omega ^ 2 ∂mu) = v)
    (hFourth : ∀ i : Index, (∫ omega, X i omega ^ 4 ∂mu) = m4)
    (s : Finset Index) :
    ((∫ omega, (∑ i ∈ s, X i omega) ∂mu) = 0) ∧
      ((∫ omega, (∑ i ∈ s, X i omega) ^ 2 ∂mu) =
        (s.card : ℝ) * v) ∧
      ((∫ omega, (∑ i ∈ s, X i omega) ^ 4 ∂mu) =
        (s.card : ℝ) * m4 +
          3 * (s.card : ℝ) * ((s.card : ℝ) - 1) * v ^ 2) := by
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
        dsimp only [S, Z]
        have hSum :
            (fun omega => ∑ i ∈ s, X i omega) =
              (∑ i ∈ s, X i : Omega → ℝ) := by
          funext omega
          simp
        rw [hSum]
        exact hIndep.indepFun_finsetSum_of_notMem hMeas ha
      have ihFirst : (∫ omega, S omega ∂mu) = 0 := by
        simpa only [S] using ih.1
      have ihSecond :
          (∫ omega, S omega ^ 2 ∂mu) = (s.card : ℝ) * v := by
        simpa only [S] using ih.2.1
      have ihFourth :
          (∫ omega, S omega ^ 4 ∂mu) =
            (s.card : ℝ) * m4 +
              3 * (s.card : ℝ) * ((s.card : ℝ) - 1) * v ^ 2 := by
        simpa only [S] using ih.2.2
      have hS1 : Integrable S mu :=
        finite_integrable_of_measurable_mixed mu hSmeas
      have hZ1 : Integrable Z mu :=
        finite_integrable_of_measurable_mixed mu hZmeas
      have hS2 : Integrable (fun omega => S omega ^ 2) mu :=
        finite_integrable_of_measurable_mixed mu (hSmeas.pow_const 2)
      have hZ2 : Integrable (fun omega => Z omega ^ 2) mu :=
        finite_integrable_of_measurable_mixed mu (hZmeas.pow_const 2)
      have hS4 : Integrable (fun omega => S omega ^ 4) mu :=
        finite_integrable_of_measurable_mixed mu (hSmeas.pow_const 4)
      have hZ4 : Integrable (fun omega => Z omega ^ 4) mu :=
        finite_integrable_of_measurable_mixed mu (hZmeas.pow_const 4)
      have h11 : (∫ omega, S omega * Z omega ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep_mixed
          hSZ hSmeas hZmeas 1 1
        simpa only [pow_one, ihFirst, hFirst a, zero_mul] using h
      have h31 : (∫ omega, S omega ^ 3 * Z omega ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep_mixed
          hSZ hSmeas hZmeas 3 1
        simpa only [Z, pow_one, hFirst a, mul_zero] using h
      have h22 :
          (∫ omega, S omega ^ 2 * Z omega ^ 2 ∂mu) =
            (s.card : ℝ) * v ^ 2 := by
        have h := integral_mul_powers_of_indep_mixed
          hSZ hSmeas hZmeas 2 2
        rw [ihSecond, hSecond a] at h
        nlinarith
      have h13 : (∫ omega, S omega * Z omega ^ 3 ∂mu) = 0 := by
        have h := integral_mul_powers_of_indep_mixed
          hSZ hSmeas hZmeas 1 3
        simpa only [pow_one, ihFirst, zero_mul] using h
      have hTwo11 : Integrable (fun omega => 2 * (S omega * Z omega)) mu :=
        finite_integrable_of_measurable_mixed mu
          (measurable_const.mul (hSmeas.mul hZmeas))
      have hFour31 :
          Integrable (fun omega => 4 * (S omega ^ 3 * Z omega)) mu :=
        finite_integrable_of_measurable_mixed mu
          (measurable_const.mul ((hSmeas.pow_const 3).mul hZmeas))
      have hSix22 :
          Integrable (fun omega => 6 * (S omega ^ 2 * Z omega ^ 2)) mu :=
        finite_integrable_of_measurable_mixed mu
          (measurable_const.mul
            ((hSmeas.pow_const 2).mul (hZmeas.pow_const 2)))
      have hFour13 :
          Integrable (fun omega => 4 * (S omega * Z omega ^ 3)) mu :=
        finite_integrable_of_measurable_mixed mu
          (measurable_const.mul (hSmeas.mul (hZmeas.pow_const 3)))
      have hm1 : (∫ omega, Z omega + S omega ∂mu) = 0 := by
        rw [integral_add hZ1 hS1, hFirst a, ihFirst]
        norm_num
      have hm2 :
          (∫ omega, (Z omega + S omega) ^ 2 ∂mu) =
            ((s.card : ℝ) + 1) * v := by
        calc
          (∫ omega, (Z omega + S omega) ^ 2 ∂mu) =
              ∫ omega,
                S omega ^ 2 + 2 * (S omega * Z omega) + Z omega ^ 2
              ∂mu := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega => by ring
          _ = (∫ omega, S omega ^ 2 ∂mu) +
                2 * (∫ omega, S omega * Z omega ∂mu) +
                (∫ omega, Z omega ^ 2 ∂mu) := by
              calc
                (∫ omega,
                    S omega ^ 2 + 2 * (S omega * Z omega) + Z omega ^ 2
                    ∂mu) =
                    (∫ omega,
                      S omega ^ 2 + 2 * (S omega * Z omega) ∂mu) +
                      (∫ omega, Z omega ^ 2 ∂mu) := by
                  simpa only [Pi.add_apply] using
                    (integral_add (hS2.add hTwo11) hZ2)
                _ = ((∫ omega, S omega ^ 2 ∂mu) +
                      (∫ omega, 2 * (S omega * Z omega) ∂mu)) +
                      (∫ omega, Z omega ^ 2 ∂mu) := by
                  rw [show
                    (∫ omega,
                      S omega ^ 2 + 2 * (S omega * Z omega) ∂mu) =
                        (∫ omega, S omega ^ 2 ∂mu) +
                          (∫ omega, 2 * (S omega * Z omega) ∂mu) by
                    simpa only [Pi.add_apply] using
                      (integral_add hS2 hTwo11)]
                _ = (∫ omega, S omega ^ 2 ∂mu) +
                      2 * (∫ omega, S omega * Z omega ∂mu) +
                      (∫ omega, Z omega ^ 2 ∂mu) := by
                  rw [integral_const_mul]
          _ = ((s.card : ℝ) + 1) * v := by
              rw [ihSecond, h11, hSecond a]
              ring
      have hm4 :
          (∫ omega, (Z omega + S omega) ^ 4 ∂mu) =
            ((s.card : ℝ) + 1) * m4 +
              3 * ((s.card : ℝ) + 1) * (s.card : ℝ) * v ^ 2 := by
        calc
          (∫ omega, (Z omega + S omega) ^ 4 ∂mu) =
              ∫ omega,
                S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                  6 * (S omega ^ 2 * Z omega ^ 2) +
                  4 * (S omega * Z omega ^ 3) + Z omega ^ 4
              ∂mu := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun omega => by ring
          _ = (∫ omega, S omega ^ 4 ∂mu) +
                4 * (∫ omega, S omega ^ 3 * Z omega ∂mu) +
                6 * (∫ omega, S omega ^ 2 * Z omega ^ 2 ∂mu) +
                4 * (∫ omega, S omega * Z omega ^ 3 ∂mu) +
                (∫ omega, Z omega ^ 4 ∂mu) := by
              calc
                (∫ omega,
                    S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                      6 * (S omega ^ 2 * Z omega ^ 2) +
                      4 * (S omega * Z omega ^ 3) + Z omega ^ 4 ∂mu) =
                    (∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                        6 * (S omega ^ 2 * Z omega ^ 2) +
                        4 * (S omega * Z omega ^ 3) ∂mu) +
                      (∫ omega, Z omega ^ 4 ∂mu) := by
                  simpa only [Pi.add_apply] using
                    (integral_add
                      (((hS4.add hFour31).add hSix22).add hFour13) hZ4)
                _ = ((∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                        6 * (S omega ^ 2 * Z omega ^ 2) ∂mu) +
                      (∫ omega, 4 * (S omega * Z omega ^ 3) ∂mu)) +
                      (∫ omega, Z omega ^ 4 ∂mu) := by
                  rw [show
                    (∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                        6 * (S omega ^ 2 * Z omega ^ 2) +
                        4 * (S omega * Z omega ^ 3) ∂mu) =
                        (∫ omega,
                          S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                            6 * (S omega ^ 2 * Z omega ^ 2) ∂mu) +
                          (∫ omega, 4 * (S omega * Z omega ^ 3) ∂mu) by
                    simpa only [Pi.add_apply] using
                      (integral_add ((hS4.add hFour31).add hSix22) hFour13)]
                _ = (((∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) ∂mu) +
                      (∫ omega, 6 * (S omega ^ 2 * Z omega ^ 2) ∂mu)) +
                      (∫ omega, 4 * (S omega * Z omega ^ 3) ∂mu)) +
                      (∫ omega, Z omega ^ 4 ∂mu) := by
                  rw [show
                    (∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) +
                        6 * (S omega ^ 2 * Z omega ^ 2) ∂mu) =
                        (∫ omega,
                          S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) ∂mu) +
                          (∫ omega, 6 * (S omega ^ 2 * Z omega ^ 2) ∂mu) by
                    simpa only [Pi.add_apply] using
                      (integral_add (hS4.add hFour31) hSix22)]
                _ = ((((∫ omega, S omega ^ 4 ∂mu) +
                      (∫ omega, 4 * (S omega ^ 3 * Z omega) ∂mu)) +
                      (∫ omega, 6 * (S omega ^ 2 * Z omega ^ 2) ∂mu)) +
                      (∫ omega, 4 * (S omega * Z omega ^ 3) ∂mu)) +
                      (∫ omega, Z omega ^ 4 ∂mu) := by
                  rw [show
                    (∫ omega,
                      S omega ^ 4 + 4 * (S omega ^ 3 * Z omega) ∂mu) =
                        (∫ omega, S omega ^ 4 ∂mu) +
                          (∫ omega, 4 * (S omega ^ 3 * Z omega) ∂mu) by
                    simpa only [Pi.add_apply] using
                      (integral_add hS4 hFour31)]
                _ = (∫ omega, S omega ^ 4 ∂mu) +
                      4 * (∫ omega, S omega ^ 3 * Z omega ∂mu) +
                      6 * (∫ omega, S omega ^ 2 * Z omega ^ 2 ∂mu) +
                      4 * (∫ omega, S omega * Z omega ^ 3 ∂mu) +
                      (∫ omega, Z omega ^ 4 ∂mu) := by
                  rw [integral_const_mul, integral_const_mul,
                    integral_const_mul]
          _ = ((s.card : ℝ) + 1) * m4 +
                3 * ((s.card : ℝ) + 1) * (s.card : ℝ) * v ^ 2 := by
              rw [ihFourth, h31, h22, h13, hFourth a]
              ring
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Finset.sum_insert ha, S, Z] using hm1
      · simpa only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
          Nat.cast_add, Nat.cast_one, S, Z] using hm2
      · simpa only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
          Nat.cast_add, Nat.cast_one, add_sub_cancel_right, S, Z] using hm4

/-! ## One coordinate: exact biased-Rademacher fourth moment -/

/-- Centered signed observation in one frame coordinate. -/
def mixedCenteredPauliShot
    {q : ℕ} (z : RLSVector 3) (j : Fin 3) (b : Fin q)
    (path : PauliPilotPath q) : ℝ :=
  pauliPilotCoordinateVariable j b path - z j

private theorem mixedCenteredPauliShot_measurable
    {q : ℕ} (z : RLSVector 3) (j : Fin 3) (b : Fin q) :
    Measurable (mixedCenteredPauliShot z j b) :=
  Measurable.of_discrete

private theorem mixedCenteredPauliShot_firstMoment
    {q : ℕ} (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) (b : Fin q) :
    (∫ path, mixedCenteredPauliShot z j b path
      ∂pauliPilotBornProductMeasure z) = 0 := by
  letI : IsProbabilityMeasure (pauliPilotBornProductMeasure (q := q) z) :=
    ⟨pauliPilotBornProductMeasure_univ (q := q) z hphysical⟩
  unfold mixedCenteredPauliShot
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    integral_pauliPilotCoordinateVariable_eq z hphysical j b]
  simp

private theorem mixedCenteredPauliShot_secondMoment
    {q : ℕ} (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) (b : Fin q) :
    (∫ path, mixedCenteredPauliShot z j b path ^ 2
      ∂pauliPilotBornProductMeasure z) = 1 - z j ^ 2 := by
  rw [integral_pauliPilotBornProductMeasure z hphysical]
  change pauliPilotFiniteExpectation z
    (fun path => (pauliOutcomeSign (path b j) - z j) ^ 2) = _
  simpa [pow_two] using
    (pauliPilotCenteredCoordinateProduct_mean z b j b j)

private theorem mixedCenteredPauliShot_fourthMoment
    {q : ℕ} (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) (b : Fin q) :
    (∫ path, mixedCenteredPauliShot z j b path ^ 4
      ∂pauliPilotBornProductMeasure z) =
      1 + 2 * z j ^ 2 - 3 * z j ^ 4 := by
  rw [integral_pauliPilotBornProductMeasure z hphysical]
  change pauliPilotFiniteExpectation z
    (fun path => (pauliOutcomeSign (path b j) - z j) ^ 4) = _
  have hFunction :
      (fun path : PauliPilotPath q =>
        (pauliOutcomeSign (path b j) - z j) ^ 4) =
      (fun path : PauliPilotPath q =>
        (1 + 6 * z j ^ 2 + z j ^ 4) -
          (4 * z j * (1 + z j ^ 2)) *
            pauliOutcomeSign (path b j)) := by
    funext path
    cases h : path b j <;>
      simp [pauliOutcomeSign, h] <;> ring
  rw [hFunction, pauliPilotFiniteExpectation_sub,
    pauliPilotFiniteExpectation_const,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotCoordinateSign_mean]
  ring

private theorem pauliPilotCenteredShots_iIndepFun
    {q : ℕ} (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) :
    iIndepFun (fun b : Fin q => mixedCenteredPauliShot (q := q) z j b)
      (pauliPilotBornProductMeasure (q := q) z) := by
  have hRaw :
      iIndepFun (pauliPilotCoordinateVariable (q := q) j)
        (pauliPilotBornProductMeasure z) :=
    finiteIndependentRealFamily_to_iIndepFun
      (pauliPilotBornProductMeasure_univ (q := q) z hphysical)
      (pauliPilotCoordinateVariable_finiteIndependent z hphysical j)
  have hComp := hRaw.comp
    (fun _b (x : ℝ) => x - z j)
    (fun _b => measurable_id.sub measurable_const)
  change iIndepFun
    (fun b : Fin q => fun path =>
      pauliPilotCoordinateVariable j b path - z j)
    (pauliPilotBornProductMeasure z)
  exact hComp

/-- Exact fourth moment of one centered coordinate sample mean. -/
theorem pauliPilotEstimate_coordinateFourthMoment_exact
    {q : ℕ} (hq : 0 < q) (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path => (pauliPilotEstimate path j - z j) ^ 4) =
      ((q : ℝ) * (1 + 2 * z j ^ 2 - 3 * z j ^ 4) +
        3 * (q : ℝ) * ((q : ℝ) - 1) * (1 - z j ^ 2) ^ 2) /
        (q : ℝ) ^ 4 := by
  let mu := pauliPilotBornProductMeasure (q := q) z
  letI : IsProbabilityMeasure mu :=
    ⟨pauliPilotBornProductMeasure_univ (q := q) z hphysical⟩
  let X : Fin q → PauliPilotPath q → ℝ :=
    fun b => mixedCenteredPauliShot z j b
  have hMoments := finite_iIndep_centered_sum_fourth
    mu X
    (pauliPilotCenteredShots_iIndepFun z hphysical j)
    (fun b => mixedCenteredPauliShot_measurable z j b)
    (1 - z j ^ 2) (1 + 2 * z j ^ 2 - 3 * z j ^ 4)
    (fun b => mixedCenteredPauliShot_firstMoment z hphysical j b)
    (fun b => mixedCenteredPauliShot_secondMoment z hphysical j b)
    (fun b => mixedCenteredPauliShot_fourthMoment z hphysical j b)
    (Finset.univ : Finset (Fin q))
  have hRawFourth :
      (∫ path, (∑ b : Fin q, X b path) ^ 4 ∂mu) =
        (q : ℝ) * (1 + 2 * z j ^ 2 - 3 * z j ^ 4) +
          3 * (q : ℝ) * ((q : ℝ) - 1) * (1 - z j ^ 2) ^ 2 := by
    simpa [X] using hMoments.2.2
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  have hPointwise : ∀ path : PauliPilotPath q,
      (pauliPilotEstimate path j - z j) ^ 4 =
        ((q : ℝ)⁻¹) ^ 4 * (∑ b : Fin q, X b path) ^ 4 := by
    intro path
    rw [pauliPilotEstimate_sub_truth hq path z j]
    simp only [pauliRegressionNoise, X, mixedCenteredPauliShot,
      pauliPilotCoordinateVariable]
    ring
  unfold pauliPilotFiniteExpectation
  rw [← integral_pauliPilotBornProductMeasure (q := q) z hphysical]
  calc
    (∫ path, (pauliPilotEstimate path j - z j) ^ 4 ∂mu) =
        ∫ path, ((q : ℝ)⁻¹) ^ 4 *
          (∑ b : Fin q, X b path) ^ 4 ∂mu := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hPointwise
    _ = ((q : ℝ)⁻¹) ^ 4 *
          (∫ path, (∑ b : Fin q, X b path) ^ 4 ∂mu) := by
            rw [integral_const_mul]
    _ = ((q : ℝ) * (1 + 2 * z j ^ 2 - 3 * z j ^ 4) +
          3 * (q : ℝ) * ((q : ℝ) - 1) * (1 - z j ^ 2) ^ 2) /
          (q : ℝ) ^ 4 := by
            rw [hRawFourth]
            field_simp [hq0]

private theorem physical_coordinate_sq_le_one
    (z : RLSVector 3) (hphysical : PauliPilotPhysicalBloch z)
    (j : Fin 3) : z j ^ 2 ≤ 1 := by
  have hCoordinate : z j ^ 2 ≤ blochNormSq z := by
    unfold blochNormSq
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)
  exact hCoordinate.trans hphysical

/-- Universal sharp-enough coordinate bound `3/q^2`. -/
theorem pauliPilotEstimate_coordinateFourthMoment_le
    {q : ℕ} (hq : 0 < q) (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z) (j : Fin 3) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path => (pauliPilotEstimate path j - z j) ^ 4) ≤
      3 / (q : ℝ) ^ 2 := by
  rw [pauliPilotEstimate_coordinateFourthMoment_exact hq z hphysical j]
  let Q : ℝ := q
  let t : ℝ := z j ^ 2
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact_mod_cast hq
  have hQ0 : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := physical_coordinate_sq_le_one z hphysical j
  have hm4 : 1 + 2 * t - 3 * t ^ 2 ≤ 3 := by nlinarith
  have hv0 : 0 ≤ 1 - t := by linarith
  have hv2 : (1 - t) ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  have hFirst : Q * (1 + 2 * t - 3 * t ^ 2) ≤ Q * 3 :=
    mul_le_mul_of_nonneg_left hm4 hQ0.le
  have hSecond :
      3 * Q * (Q - 1) * (1 - t) ^ 2 ≤ 3 * Q * (Q - 1) := by
    calc
      3 * Q * (Q - 1) * (1 - t) ^ 2 ≤
          3 * Q * (Q - 1) * 1 :=
        mul_le_mul_of_nonneg_left hv2
          (mul_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) hQ0.le)
            (sub_nonneg.mpr hQ))
      _ = 3 * Q * (Q - 1) := by ring
  have hNumerator :
      Q * (1 + 2 * t - 3 * t ^ 2) +
          3 * Q * (Q - 1) * (1 - t) ^ 2 ≤ 3 * Q ^ 2 := by
    nlinarith
  dsimp [Q, t] at hNumerator ⊢
  apply (div_le_div_iff₀ (pow_pos hQ0 4) (pow_pos hQ0 2)).2
  nlinarith

/-! ## Independence between distinct coordinate blocks -/

abbrev MixedPauliAxisPath (q : ℕ) := Fin q → Bool

private def mixedPauliAxisPathMass
    {q : ℕ} (z : RLSVector 3) (j : Fin 3)
    (omega : MixedPauliAxisPath q) : ℝ :=
  ∏ b : Fin q, pauliBornProbability z j (omega b)

private def mixedPauliAxisFiniteExpectation
    {q : ℕ} (z : RLSVector 3) (j : Fin 3)
    (f : MixedPauliAxisPath q → ℝ) : ℝ :=
  ∑ omega : MixedPauliAxisPath q,
    mixedPauliAxisPathMass z j omega * f omega

private theorem mixedPauliAxisPathMass_sum_one
    {q : ℕ} (z : RLSVector 3) (j : Fin 3) :
    ∑ omega : MixedPauliAxisPath q,
      mixedPauliAxisPathMass z j omega = 1 := by
  unfold mixedPauliAxisPathMass
  calc
    (∑ omega : Fin q → Bool,
        ∏ b : Fin q, pauliBornProbability z j (omega b)) =
        ∏ b : Fin q, ∑ outcome : Bool,
          pauliBornProbability z j outcome :=
      (Fintype.prod_sum (fun _b outcome =>
        pauliBornProbability z j outcome)).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro b hb
      simp [pauliBornProbability] <;> ring

private def pauliPathAxisEquiv (q : ℕ) :
    PauliPilotPath q ≃ (Fin 3 → MixedPauliAxisPath q) where
  toFun path j b := path b j
  invFun axes b j := axes j b
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pauliPilotPathMass_axis_product
    {q : ℕ} (z : RLSVector 3)
    (axes : Fin 3 → MixedPauliAxisPath q) :
    pauliPilotPathMass z ((pauliPathAxisEquiv q).symm axes) =
      ∏ j : Fin 3, mixedPauliAxisPathMass z j (axes j) := by
  unfold pauliPilotPathMass pauliPilotBlockMass mixedPauliAxisPathMass
  change (∏ b : Fin q, ∏ j : Fin 3,
      pauliBornProbability z j (axes j b)) =
    ∏ j : Fin 3, ∏ b : Fin q,
      pauliBornProbability z j (axes j b)
  rw [Finset.prod_comm]

private theorem finite_product_expectation_factorization_mixed
    {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (p g : ι → α → ℝ) :
    (∑ x : ι → α,
        (∏ i : ι, p i (x i)) * (∏ i : ι, g i (x i))) =
      ∏ i : ι, ∑ a : α, p i a * g i a := by
  classical
  calc
    (∑ x : ι → α,
        (∏ i : ι, p i (x i)) * (∏ i : ι, g i (x i))) =
      ∑ x : ι → α, ∏ i : ι, p i (x i) * g i (x i) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.prod_mul_distrib]
    _ = ∏ i : ι, ∑ a : α, p i a * g i a := by
      exact (Fintype.prod_sum (fun i a => p i a * g i a)).symm

private theorem finite_prod_single_selector_mixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι) (v : ι → ℝ) :
    (∏ i : ι, if i = a then v i else 1) = v a := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro i _ hia
    simp [hia]
  · simp

private theorem pauliPilotFiniteExpectation_axis_marginal
    {q : ℕ} (z : RLSVector 3) (j : Fin 3)
    (f : MixedPauliAxisPath q → ℝ) :
    pauliPilotFiniteExpectation z
        (fun path => f (fun b => path b j)) =
      mixedPauliAxisFiniteExpectation z j f := by
  classical
  unfold pauliPilotFiniteExpectation
  calc
    (∑ path : PauliPilotPath q,
        pauliPilotPathMass z path * f (fun b => path b j)) =
      ∑ axes : Fin 3 → MixedPauliAxisPath q,
        (∏ i : Fin 3, mixedPauliAxisPathMass z i (axes i)) *
          f (axes j) := by
            apply Fintype.sum_equiv (pauliPathAxisEquiv q) _ _
            intro path
            have hMass :=
              pauliPilotPathMass_axis_product z ((pauliPathAxisEquiv q) path)
            simpa [pauliPathAxisEquiv] using congrArg
              (fun a : ℝ => a * f ((pauliPathAxisEquiv q) path j)) hMass
    _ = ∑ axes : Fin 3 → MixedPauliAxisPath q,
        (∏ i : Fin 3, mixedPauliAxisPathMass z i (axes i)) *
          (∏ i : Fin 3, if i = j then f (axes i) else 1) := by
            apply Finset.sum_congr rfl
            intro axes _
            rw [finite_prod_single_selector_mixed (ι := Fin 3) j]
    _ = ∏ i : Fin 3,
        ∑ omega : MixedPauliAxisPath q,
          mixedPauliAxisPathMass z i omega *
            (if i = j then f omega else 1) :=
      finite_product_expectation_factorization_mixed
        (ι := Fin 3) (α := MixedPauliAxisPath q)
        (fun i omega => mixedPauliAxisPathMass z i omega)
        (fun i omega => if i = j then f omega else 1)
    _ = ∏ i : Fin 3,
        if i = j then mixedPauliAxisFiniteExpectation z j f else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i
        simp [mixedPauliAxisFiniteExpectation]
      · simp [hij, mixedPauliAxisPathMass_sum_one]
    _ = mixedPauliAxisFiniteExpectation z j f := by
      rw [finite_prod_single_selector_mixed (ι := Fin 3) j]

/-- Functions of two distinct complete coordinate blocks factor under the
explicit finite product mass. -/
theorem pauliPilotFiniteExpectation_distinctAxis_mul_factorization
    {q : ℕ} (z : RLSVector 3) (j k : Fin 3) (hjk : j ≠ k)
    (f g : MixedPauliAxisPath q → ℝ) :
    pauliPilotFiniteExpectation z
        (fun path => f (fun b => path b j) * g (fun b => path b k)) =
      pauliPilotFiniteExpectation z (fun path => f (fun b => path b j)) *
      pauliPilotFiniteExpectation z (fun path => g (fun b => path b k)) := by
  classical
  unfold pauliPilotFiniteExpectation
  have hReindex :
      (∑ path : PauliPilotPath q,
        pauliPilotPathMass z path *
          (f (fun b => path b j) * g (fun b => path b k))) =
      ∑ axes : Fin 3 → MixedPauliAxisPath q,
        (∏ i : Fin 3, mixedPauliAxisPathMass z i (axes i)) *
          (f (axes j) * g (axes k)) := by
    apply Fintype.sum_equiv (pauliPathAxisEquiv q) _ _
    intro path
    have hMass :=
      pauliPilotPathMass_axis_product z ((pauliPathAxisEquiv q) path)
    simpa [pauliPathAxisEquiv] using congrArg
      (fun a : ℝ => a *
        (f ((pauliPathAxisEquiv q) path j) *
          g ((pauliPathAxisEquiv q) path k))) hMass
  rw [hReindex]
  calc
    (∑ axes : Fin 3 → MixedPauliAxisPath q,
        (∏ i : Fin 3, mixedPauliAxisPathMass z i (axes i)) *
          (f (axes j) * g (axes k))) =
      ∑ axes : Fin 3 → MixedPauliAxisPath q,
        (∏ i : Fin 3, mixedPauliAxisPathMass z i (axes i)) *
          (∏ i : Fin 3,
            (if i = j then f (axes i) else 1) *
              (if i = k then g (axes i) else 1)) := by
        apply Finset.sum_congr rfl
        intro axes _
        rw [Finset.prod_mul_distrib,
          finite_prod_single_selector_mixed (ι := Fin 3) j,
          finite_prod_single_selector_mixed (ι := Fin 3) k]
    _ = ∏ i : Fin 3,
        ∑ omega : MixedPauliAxisPath q,
          mixedPauliAxisPathMass z i omega *
            ((if i = j then f omega else 1) *
              (if i = k then g omega else 1)) :=
      finite_product_expectation_factorization_mixed
        (ι := Fin 3) (α := MixedPauliAxisPath q)
        (fun i omega => mixedPauliAxisPathMass z i omega)
        (fun i omega =>
          (if i = j then f omega else 1) *
            (if i = k then g omega else 1))
    _ = mixedPauliAxisFiniteExpectation z j f *
        mixedPauliAxisFiniteExpectation z k g := by
      have hProduct :
          (∏ i : Fin 3,
            (if i = j then mixedPauliAxisFiniteExpectation z j f else 1) *
              (if i = k then mixedPauliAxisFiniteExpectation z k g else 1)) =
            mixedPauliAxisFiniteExpectation z j f *
              mixedPauliAxisFiniteExpectation z k g := by
        rw [Finset.prod_mul_distrib,
          finite_prod_single_selector_mixed (ι := Fin 3) j,
          finite_prod_single_selector_mixed (ι := Fin 3) k]
      rw [← hProduct]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i
        simp [hjk, mixedPauliAxisFiniteExpectation]
      · by_cases hik : i = k
        · subst i
          simp [Ne.symm hjk, mixedPauliAxisFiniteExpectation]
        · simp [hij, hik, mixedPauliAxisPathMass_sum_one]
    _ = pauliPilotFiniteExpectation z
          (fun path => f (fun b => path b j)) *
        pauliPilotFiniteExpectation z
          (fun path => g (fun b => path b k)) := by
      rw [pauliPilotFiniteExpectation_axis_marginal,
        pauliPilotFiniteExpectation_axis_marginal]

private def mixedPauliAxisEstimate
    {q : ℕ} (omega : MixedPauliAxisPath q) : ℝ :=
  (q : ℝ)⁻¹ * ∑ b : Fin q, pauliOutcomeSign (omega b)

private theorem pauliPilotEstimate_eq_axisEstimate
    {q : ℕ} (path : PauliPilotPath q) (j : Fin 3) :
    pauliPilotEstimate path j =
      mixedPauliAxisEstimate (fun b => path b j) := rfl

/-- Distinct centered squared coordinate means factor exactly. -/
theorem pauliPilotEstimate_crossSquareMoment_exact
    {q : ℕ} (hq : 0 < q) (z : RLSVector 3)
    (j k : Fin 3) (hjk : j ≠ k) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path =>
          (pauliPilotEstimate path j - z j) ^ 2 *
            (pauliPilotEstimate path k - z k) ^ 2) =
      ((1 - z j ^ 2) * (1 - z k ^ 2)) / (q : ℝ) ^ 2 := by
  let f : MixedPauliAxisPath q → ℝ := fun omega =>
    (mixedPauliAxisEstimate omega - z j) ^ 2
  let g : MixedPauliAxisPath q → ℝ := fun omega =>
    (mixedPauliAxisEstimate omega - z k) ^ 2
  have hFactor :=
    pauliPilotFiniteExpectation_distinctAxis_mul_factorization
      (q := q) z j k hjk f g
  have hFactor' :
      pauliPilotFiniteExpectation (q := q) z
          (fun path =>
            (pauliPilotEstimate path j - z j) ^ 2 *
              (pauliPilotEstimate path k - z k) ^ 2) =
        pauliPilotFiniteExpectation (q := q) z
            (fun path => (pauliPilotEstimate path j - z j) ^ 2) *
          pauliPilotFiniteExpectation (q := q) z
            (fun path => (pauliPilotEstimate path k - z k) ^ 2) := by
    simpa only [f, g, ← pauliPilotEstimate_eq_axisEstimate] using hFactor
  rw [hFactor', pauliPilotEstimate_coordinateVariance hq z j,
    pauliPilotEstimate_coordinateVariance hq z k]
  ring

/-- Under physicality, every distinct cross-square moment is at most `1/q^2`. -/
theorem pauliPilotEstimate_crossSquareMoment_le
    {q : ℕ} (hq : 0 < q) (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z)
    (j k : Fin 3) (hjk : j ≠ k) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path =>
          (pauliPilotEstimate path j - z j) ^ 2 *
            (pauliPilotEstimate path k - z k) ^ 2) ≤
      1 / (q : ℝ) ^ 2 := by
  rw [pauliPilotEstimate_crossSquareMoment_exact hq z j k hjk]
  have hj := physical_coordinate_sq_le_one z hphysical j
  have hk := physical_coordinate_sq_le_one z hphysical k
  have hvj : 0 ≤ 1 - z j ^ 2 := by linarith
  have hvk : 0 ≤ 1 - z k ^ 2 := by linarith
  have hProduct : (1 - z j ^ 2) * (1 - z k ^ 2) ≤ 1 := by
    nlinarith [mul_nonneg hvj hvk]
  exact div_le_div_of_nonneg_right hProduct (sq_nonneg (q : ℝ))

/-! ## Arbitrary orthonormal frame -/

/-- Linear estimator reconstructed from the three frame-coordinate means. -/
def mixedFrameFinalLinearEstimator
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : Fin 3 → ℝ :=
  mixedFrameReconstruct R (pauliPilotEstimate path)

/-- Physical-coordinate error of the frame estimator. -/
def mixedFrameFinalLinearError
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : Fin 3 → ℝ :=
  mixedFrameFinalLinearEstimator R path - theta

/-- Squared Euclidean error. -/
def mixedFrameFinalSquaredError
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  blochNormSq (mixedFrameFinalLinearError theta R path)

/-- Euclidean error norm. -/
def mixedFrameFinalErrorNorm
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  mixedBlochEuclideanNorm (mixedFrameFinalLinearError theta R path)

/-- Orthonormal transport preserves physicality of the truth coordinates. -/
theorem qubitFrameCoordinates_physical
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta) :
    PauliPilotPhysicalBloch (qubitFrameCoordinates R theta) := by
  unfold PauliPilotPhysicalBloch at hphysical ⊢
  change blochNormSq (qubitFrameCoordinates R theta) ≤ 1
  rw [mixedFrameCoordinates_normSq R hR theta]
  exact hphysical

/-- Reconstructed error is the orthogonal image of coordinatewise sample-mean
error. -/
theorem mixedFrameFinalLinearError_eq_reconstruct
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (path : PauliPilotPath q) :
    mixedFrameFinalLinearError theta R path =
      mixedFrameReconstruct R
        (fun j => pauliPilotEstimate path j -
          qubitFrameCoordinates R theta j) := by
  have hTruth := mixedFrameReconstruct_coordinates R hR theta
  rw [mixedFrameFinalLinearError, mixedFrameFinalLinearEstimator]
  ext i
  change mixedFrameReconstruct R (pauliPilotEstimate path) i - theta i = _
  rw [← congrFun hTruth i]
  simp [mixedFrameReconstruct, mul_sub, Finset.sum_sub_distrib]

/-- Frame covariance: physical squared error equals coordinate squared error. -/
theorem mixedFrameFinalSquaredError_eq_coordinates
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (path : PauliPilotPath q) :
    mixedFrameFinalSquaredError theta R path =
      ∑ j : Fin 3,
        (pauliPilotEstimate path j -
          qubitFrameCoordinates R theta j) ^ 2 := by
  rw [mixedFrameFinalSquaredError,
    mixedFrameFinalLinearError_eq_reconstruct theta R hR path,
    mixedFrameReconstruct_normSq R hR]
  rfl

/-- The squared error is nonnegative. -/
theorem mixedFrameFinalSquaredError_nonnegative
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (path : PauliPilotPath q) :
    0 ≤ mixedFrameFinalSquaredError theta R path := by
  unfold mixedFrameFinalSquaredError blochNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- Error norm squared and squared error agree exactly. -/
theorem mixedFrameFinalErrorNorm_sq
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (path : PauliPilotPath q) :
    mixedFrameFinalErrorNorm theta R path ^ 2 =
      mixedFrameFinalSquaredError theta R path := by
  unfold mixedFrameFinalErrorNorm mixedFrameFinalSquaredError
  exact mixedBlochEuclideanNorm_sq _

private theorem pauliPilotFiniteExpectation_mono
    {q : ℕ} (z : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch z)
    {f g : PauliPilotPath q → ℝ}
    (hfg : ∀ path, f path ≤ g path) :
    pauliPilotFiniteExpectation z f ≤ pauliPilotFiniteExpectation z g := by
  unfold pauliPilotFiniteExpectation
  apply Finset.sum_le_sum
  intro path _
  exact mul_le_mul_of_nonneg_left (hfg path)
    (pauliPilotPathMass_nonnegative z hphysical path)

/-- Frame-uniform second squared-error moment, used in the cubic split. -/
theorem mixedFrameFinalSquaredError_expectation_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (mixedFrameFinalSquaredError theta R) ≤ 3 / (q : ℝ) := by
  let z := qubitFrameCoordinates R theta
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hphysical
  have hExpand :
      pauliPilotFiniteExpectation (q := q) z
          (mixedFrameFinalSquaredError (q := q) theta R) =
        ∑ j : Fin 3,
          pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              (pauliPilotEstimate path j - z j) ^ 2) := by
    have hFunction :
        mixedFrameFinalSquaredError (q := q) theta R =
          fun path : PauliPilotPath q =>
            ∑ j : Fin 3, (pauliPilotEstimate path j - z j) ^ 2 := by
      funext path
      simpa [z] using
        mixedFrameFinalSquaredError_eq_coordinates theta R hR path
    rw [hFunction, pauliPilotFiniteExpectation_fintype_sum]
  rw [hExpand]
  simp_rw [pauliPilotEstimate_coordinateVariance hq z]
  have hEach : ∀ j : Fin 3, 1 - z j ^ 2 ≤ 1 := by
    intro j
    nlinarith [sq_nonneg (z j)]
  have hSum : (∑ j : Fin 3, (1 - z j ^ 2)) ≤ 3 := by
    calc
      (∑ j : Fin 3, (1 - z j ^ 2)) ≤ ∑ _j : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => hEach j
      _ = 3 := by norm_num
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  calc
    (∑ j : Fin 3, (1 - z j ^ 2) / (q : ℝ)) =
        (∑ j : Fin 3, (1 - z j ^ 2)) / (q : ℝ) := by
          rw [Finset.sum_div]
    _ ≤ 3 / (q : ℝ) := div_le_div_of_nonneg_right hSum hqReal.le

/-- Universal frame-uniform fourth moment with explicit constant `15`. -/
theorem mixedFrameFinalSquaredError_fourthMoment_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path => mixedFrameFinalSquaredError theta R path ^ 2) ≤
      15 / (q : ℝ) ^ 2 := by
  let z := qubitFrameCoordinates R theta
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hphysical
  let e : PauliPilotPath q → Fin 3 → ℝ := fun path j =>
    pauliPilotEstimate path j - z j
  have hPointwise : ∀ path : PauliPilotPath q,
      mixedFrameFinalSquaredError theta R path ^ 2 =
        e path (0 : Fin 3) ^ 4 + e path (1 : Fin 3) ^ 4 +
          e path (2 : Fin 3) ^ 4 +
          2 * (e path (0 : Fin 3) ^ 2 * e path (1 : Fin 3) ^ 2) +
          2 * (e path (0 : Fin 3) ^ 2 * e path (2 : Fin 3) ^ 2) +
          2 * (e path (1 : Fin 3) ^ 2 * e path (2 : Fin 3) ^ 2) := by
    intro path
    rw [mixedFrameFinalSquaredError_eq_coordinates theta R hR path]
    simp [e, Fin.sum_univ_succ]
    ring
  have hExpectation :
      pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q =>
            mixedFrameFinalSquaredError theta R path ^ 2) =
        pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 0 ^ 4) +
        pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 1 ^ 4) +
        pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 2 ^ 4) +
        2 * pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 0 ^ 2 * e path 1 ^ 2) +
        2 * pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 0 ^ 2 * e path 2 ^ 2) +
        2 * pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q => e path 1 ^ 2 * e path 2 ^ 2) := by
    have hFunctions := funext hPointwise
    rw [hFunctions, pauliPilotFiniteExpectation_add,
      pauliPilotFiniteExpectation_add, pauliPilotFiniteExpectation_add,
      pauliPilotFiniteExpectation_add, pauliPilotFiniteExpectation_add,
      pauliPilotFiniteExpectation_const_mul,
      pauliPilotFiniteExpectation_const_mul,
      pauliPilotFiniteExpectation_const_mul]
  rw [hExpectation]
  have h0 := pauliPilotEstimate_coordinateFourthMoment_le
    hq z hzPhysical (0 : Fin 3)
  have h1 := pauliPilotEstimate_coordinateFourthMoment_le
    hq z hzPhysical (1 : Fin 3)
  have h2 := pauliPilotEstimate_coordinateFourthMoment_le
    hq z hzPhysical (2 : Fin 3)
  have h01 := pauliPilotEstimate_crossSquareMoment_le
    hq z hzPhysical (0 : Fin 3) (1 : Fin 3) (by decide)
  have h02 := pauliPilotEstimate_crossSquareMoment_le
    hq z hzPhysical (0 : Fin 3) (2 : Fin 3) (by decide)
  have h12 := pauliPilotEstimate_crossSquareMoment_le
    hq z hzPhysical (1 : Fin 3) (2 : Fin 3) (by decide)
  dsimp [e] at h0 h1 h2 h01 h02 h12 ⊢
  simp only [div_eq_mul_inv] at h0 h1 h2 h01 h02 h12 ⊢
  linarith

/-- Third norm moment from a pointwise small/large split.  The explicit rate
`18/(q*sqrt q)` is `O(q^(-3/2))`. -/
theorem mixedFrameFinalErrorNorm_thirdMoment_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path => mixedFrameFinalErrorNorm theta R path ^ 3) ≤
      18 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
  let z := qubitFrameCoordinates R theta
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hphysical
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hSqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqReal
  have hSqrtSq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt hqReal.le
  have hPointwise : ∀ path : PauliPilotPath q,
      mixedFrameFinalErrorNorm theta R path ^ 3 ≤
        (Real.sqrt (q : ℝ))⁻¹ *
            mixedFrameFinalSquaredError theta R path +
          Real.sqrt (q : ℝ) *
            mixedFrameFinalSquaredError theta R path ^ 2 := by
    intro path
    let d := mixedFrameFinalErrorNorm theta R path
    have hd : 0 ≤ d := by
      exact mixedBlochEuclideanNorm_nonnegative _
    have hdSq : d ^ 2 = mixedFrameFinalSquaredError theta R path := by
      simpa [d] using mixedFrameFinalErrorNorm_sq theta R path
    by_cases hsmall : d ≤ (Real.sqrt (q : ℝ))⁻¹
    · have hFirst : d ^ 3 ≤ (Real.sqrt (q : ℝ))⁻¹ * d ^ 2 := by
        nlinarith [sq_nonneg d]
      rw [← hdSq]
      nlinarith [mul_nonneg hSqrt.le (sq_nonneg (d ^ 2))]
    · have hlarge : (Real.sqrt (q : ℝ))⁻¹ < d := lt_of_not_ge hsmall
      have honeStrict : 1 < Real.sqrt (q : ℝ) * d := by
        calc
          1 = Real.sqrt (q : ℝ) * (Real.sqrt (q : ℝ))⁻¹ := by
            field_simp [ne_of_gt hSqrt]
          _ < Real.sqrt (q : ℝ) * d :=
            mul_lt_mul_of_pos_left hlarge hSqrt
      have hone : 1 ≤ Real.sqrt (q : ℝ) * d := honeStrict.le
      have hSecond : d ^ 3 ≤ Real.sqrt (q : ℝ) * d ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hone) (pow_nonneg hd 3)]
      rw [← hdSq]
      nlinarith [mul_nonneg (inv_nonneg.mpr hSqrt.le) (sq_nonneg d)]
  have hMono := pauliPilotFiniteExpectation_mono z hzPhysical hPointwise
  rw [pauliPilotFiniteExpectation_add,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const_mul] at hMono
  have hSecond := mixedFrameFinalSquaredError_expectation_le
    hq theta R hR hphysical
  have hFourth := mixedFrameFinalSquaredError_fourthMoment_le
    hq theta R hR hphysical
  calc
    pauliPilotFiniteExpectation z
        (fun path => mixedFrameFinalErrorNorm theta R path ^ 3) ≤
      (Real.sqrt (q : ℝ))⁻¹ *
          pauliPilotFiniteExpectation z (mixedFrameFinalSquaredError theta R) +
        Real.sqrt (q : ℝ) *
          pauliPilotFiniteExpectation z
            (fun path => mixedFrameFinalSquaredError theta R path ^ 2) := hMono
    _ ≤ (Real.sqrt (q : ℝ))⁻¹ * (3 / (q : ℝ)) +
        Real.sqrt (q : ℝ) * (15 / (q : ℝ) ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hSecond (inv_nonneg.mpr hSqrt.le))
        (mul_le_mul_of_nonneg_left hFourth hSqrt.le)
    _ = 18 / ((q : ℝ) * Real.sqrt (q : ℝ)) := by
      field_simp [ne_of_gt hqReal, ne_of_gt hSqrt]
      nlinarith

/-! ## Fourth-moment tail at the local Bures radius -/

/-- Real probability mass of the event that the linear estimator leaves a
specified Euclidean error ball. -/
def mixedFrameFinalErrorTailMass
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (eta : ℝ) : ℝ :=
  ∑ path : PauliPilotPath q,
    if eta < mixedFrameFinalErrorNorm theta R path then
      pauliPilotPathMass (qubitFrameCoordinates R theta) path
    else 0

/-- Fourth-moment Markov bound for any positive radius. -/
theorem mixedFrameFinalErrorTailMass_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta)
    {eta : ℝ} (hEta : 0 < eta) :
    mixedFrameFinalErrorTailMass (q := q) theta R eta ≤
      15 / ((q : ℝ) ^ 2 * eta ^ 4) := by
  let z := qubitFrameCoordinates R theta
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hphysical
  have hWeighted :
      eta ^ 4 * mixedFrameFinalErrorTailMass (q := q) theta R eta ≤
        pauliPilotFiniteExpectation (q := q) z
          (fun path => mixedFrameFinalSquaredError theta R path ^ 2) := by
    unfold mixedFrameFinalErrorTailMass pauliPilotFiniteExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro path _
    by_cases hTail : eta < mixedFrameFinalErrorNorm theta R path
    · simp only [hTail, if_true]
      have hNormNonnegative :
          0 ≤ mixedFrameFinalErrorNorm theta R path :=
        mixedBlochEuclideanNorm_nonnegative _
      have hPow : eta ^ 4 ≤ mixedFrameFinalErrorNorm theta R path ^ 4 := by
        exact pow_le_pow_left₀ hEta.le hTail.le 4
      have hNormFourth :
          mixedFrameFinalErrorNorm theta R path ^ 4 =
            mixedFrameFinalSquaredError theta R path ^ 2 := by
        rw [show mixedFrameFinalErrorNorm theta R path ^ 4 =
          (mixedFrameFinalErrorNorm theta R path ^ 2) ^ 2 by ring,
          mixedFrameFinalErrorNorm_sq]
      rw [← hNormFourth]
      calc
        eta ^ 4 * pauliPilotPathMass z path ≤
            mixedFrameFinalErrorNorm theta R path ^ 4 *
              pauliPilotPathMass z path :=
          mul_le_mul_of_nonneg_right hPow
            (pauliPilotPathMass_nonnegative z hzPhysical path)
        _ = pauliPilotPathMass z path *
              mixedFrameFinalErrorNorm theta R path ^ 4 := by ring
    · simp only [hTail, if_false, mul_zero]
      exact mul_nonneg
        (pauliPilotPathMass_nonnegative z hzPhysical path)
        (sq_nonneg _)
  have hFourth := mixedFrameFinalSquaredError_fourthMoment_le
    hq theta R hR hphysical
  have hCombined := hWeighted.trans hFourth
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  rw [show 15 / ((q : ℝ) ^ 2 * eta ^ 4) =
      (15 / (q : ℝ) ^ 2) / eta ^ 4 by
        field_simp [ne_of_gt hqReal, ne_of_gt hEta]]
  apply (le_div_iff₀ (pow_pos hEta 4)).2
  simpa [mul_comm] using hCombined

/-- The concrete local-Bures radius gives the requested `q^-2` bad-event
bound. -/
theorem mixedFrameFinalError_localBuresTailMass_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : blochNormSq theta < 1) :
    mixedFrameFinalErrorTailMass (q := q) theta R
        (mixedBuresFidelityLocalRadius theta) ≤
      15 / ((q : ℝ) ^ 2 *
        mixedBuresFidelityLocalRadius theta ^ 4) :=
  mixedFrameFinalErrorTailMass_le hq theta R hR hphysical
    (mixedBuresFidelityLocalRadius_pos hInterior)

namespace Label

/-- Paper-facing finite-law fourth-moment package for an arbitrary fixed
orthonormal final frame. -/
theorem lem_SI_mixed_final_estimator_fourth_moment_qubit
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : blochNormSq theta < 1) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path => mixedFrameFinalSquaredError theta R path ^ 2) ≤
        15 / (q : ℝ) ^ 2 ∧
      pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path => mixedFrameFinalErrorNorm theta R path ^ 3) ≤
        18 / ((q : ℝ) * Real.sqrt (q : ℝ)) ∧
      mixedFrameFinalErrorTailMass (q := q) theta R
          (mixedBuresFidelityLocalRadius theta) ≤
        15 / ((q : ℝ) ^ 2 *
          mixedBuresFidelityLocalRadius theta ^ 4) := by
  exact ⟨
    mixedFrameFinalSquaredError_fourthMoment_le
      hq theta R hR hphysical,
    mixedFrameFinalErrorNorm_thirdMoment_le
      hq theta R hR hphysical,
    mixedFrameFinalError_localBuresTailMass_le
      hq theta R hR hphysical hInterior⟩

end Label
end QubitOracle.Paper
