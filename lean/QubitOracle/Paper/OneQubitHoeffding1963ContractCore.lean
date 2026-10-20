import QubitOracle.Paper.OneQubitMixedUniformLocalExactLossAveraging
import QubitOracle.Paper.OneQubitMixedPolynomialInformationConvergence

/-!
# Axiom-free Hoeffding contract transfer

This module contains only the exact universal Hoeffding contract and the
kernel-checked reductions from that contract to the concrete qubit pilot
obligations.  The optional literature axiom is deliberately kept in
`OneQubitHoeffding1963LiteratureTransfer`, so Mathlib-derived concentration
does not import an unused scientific axiom.
-/

namespace QubitOracle.Paper

noncomputable section

open Filter

/-- Exact universal form of Hoeffding (1963), Theorem 2, equation (2.6). -/
def Hoeffding1963UniversalTheorem2Contract : Prop :=
  forall (Omega : Type) (_m : MeasurableSpace Omega) (n : Nat),
    letI : MeasurableSpace Omega := _m
    forall data : HoeffdingTheorem2Data (Ω := Omega) n,
      Hoeffding1963Theorem2Contract data

/-- A universal Hoeffding theorem supplies every positive and negated finite
Born-row contract used by the polynomial information proof. -/
theorem mixedPolynomialFinitePilotHoeffdingContracts_of_hoeffding1963
    (theta : RLSVector 3) (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding1963 : Hoeffding1963UniversalTheorem2Contract) :
    MixedPolynomialFinitePilotHoeffdingContracts theta hPhysical := by
  intro n j
  constructor
  · exact hHoeffding1963 _ _ _
      (pauliPilotBornPositiveHoeffdingData
        (mixedPolynomialQPilot_pos n) theta hPhysical j)
  · exact hHoeffding1963 _ _ _
      (pauliPilotBornNegativeHoeffdingData
        (mixedPolynomialQPilot_pos n) theta hPhysical j)

/-- The same source theorem supplies the countable consistency-pilot
contract for any physical Bloch vector. -/
theorem pauliPilotConsistencyHoeffdingContracts_of_hoeffding1963
    (theta : RLSVector 3) (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding1963 : Hoeffding1963UniversalTheorem2Contract) :
    PauliPilotConsistencyHoeffdingContracts theta hPhysical := by
  intro n j
  constructor
  · exact hHoeffding1963 _ _ _
      (pauliPilotBornPositiveHoeffdingData
        (Nat.zero_lt_succ n) theta hPhysical j)
  · exact hHoeffding1963 _ _ _
      (pauliPilotBornNegativeHoeffdingData
        (Nat.zero_lt_succ n) theta hPhysical j)

/-- Uniform eventual interiority plus a universal Hoeffding theorem supplies
the finite exact-cycle concentration contract. -/
theorem mixedExactCycleUniformFiniteHoeffdingContract_of_hoeffding1963
    (theta : RLSVector 3) (H : Real)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hHoeffding1963 : Hoeffding1963UniversalTheorem2Contract) :
    MixedExactCycleUniformFiniteHoeffdingContract theta H := by
  constructor
  filter_upwards
    [mixedExactCycleLocal_uniform_remainder_margin theta H hInterior] with
      n hMarginN
  intro h hBall
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hPhysical : PauliPilotPhysicalBloch z := by
    simpa [PauliPilotPhysicalBloch, QubitOracle.blochNormSq] using
      le_of_lt hLocalInterior
  exact ⟨hPhysical,
    pauliPilotConsistencyHoeffdingContracts_of_hoeffding1963
      z hPhysical hHoeffding1963⟩

/-- Literature-relative non-LAN endpoint parameterized by the exact universal
Hoeffding contract.  This theorem itself declares no axiom. -/
theorem mixedUniformLocalProbabilityEnvelope_exactCycle_of_hoeffding1963
    (theta b : RLSVector 3) (H : Real)
    (hH : 0 <= H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding1963 : Hoeffding1963UniversalTheorem2Contract) :
    MixedUniformLocalProbabilityEnvelope theta b
      mixedUniformLocalExactCycleN H mixedUniformLocalExactCycleQFinal :=
  mixedUniformLocalProbabilityEnvelope_exactCycle_closed
    theta b H hH hPositive hInterior hSeed
      (mixedExactCycleUniformFiniteHoeffdingContract_of_hoeffding1963
        theta H hInterior hHoeffding1963)

end

end QubitOracle.Paper
