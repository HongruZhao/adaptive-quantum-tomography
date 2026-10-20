import QubitOracle.Paper.MartingaleCLT
import QubitOracle.Paper.SourceFaithfulHallHeydeCor31DeterministicVariance

/-!
# Consolidating the two Hall--Heyde Corollary 3.1 interfaces

The source-faithful deterministic-variance statement permits an arbitrary
finite row length.  The older `MartingaleCLT` atom is its specialization to
row `n` containing exactly the first `n` increments.  This module proves that
specialization inside Lean.

Consequently future consumers of the older signature can use
`hallHeyde1980_corollary3_1_of_deterministicVariance_external`, and only the
source-faithful deterministic-variance declaration is scientifically needed.
The older axiom remains declared in its legacy module, which is not edited
here, but is not used by the theorem below.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- A row-`n` natural-index increment viewed on the finite type `Fin n`. -/
def hallHeydeFinIncrement
    {Omega : Type*} (increment : Nat -> Nat -> Omega -> Real)
    (n : Nat) (k : Fin n) : Omega -> Real :=
  increment n k.1

/-- The conditional-variance version used to instantiate the source-faithful
statement. -/
def hallHeydeFinConditionalVariance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Nat -> Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> Real)
    (n : Nat) (k : Fin n) : Omega -> Real :=
  mu[(fun omega => increment n k.1 omega ^ 2) | filtration n k.1]

/-- The conditional-Lindeberg version used to instantiate the source-faithful
statement. -/
def hallHeydeFinConditionalLindeberg
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Nat -> Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> Real)
    (epsilon : Real) (n : Nat) (k : Fin n) : Omega -> Real :=
  mu[(fun omega =>
    if epsilon < |increment n k.1 omega| then increment n k.1 omega ^ 2 else 0) |
      filtration n k.1]

private theorem increment_eq_partialSum_succ_sub
    {Omega : Type*} (increment : Nat -> Nat -> Omega -> Real)
    (n k : Nat) :
    increment n k =
      fun omega =>
        martingaleArrayPartialSum increment n (k + 1) omega -
          martingaleArrayPartialSum increment n k omega := by
  funext omega
  simp [martingaleArrayPartialSum, Finset.sum_range_succ]

private theorem finConditionalVariance_sum_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Nat -> Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    (∑ k : Fin n,
        hallHeydeFinConditionalVariance mu filtration increment n k omega) =
      hallHeydeArrayConditionalVariance mu filtration increment n omega := by
  simpa [hallHeydeFinConditionalVariance,
    hallHeydeArrayConditionalVariance] using
    (Fin.sum_univ_eq_sum_range
      (fun k =>
        mu[(fun omega => increment n k omega ^ 2) |
          filtration n k] omega) n)

private theorem finConditionalLindeberg_sum_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Nat -> Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> Real)
    (epsilon : Real) (n : Nat) (omega : Omega) :
    (∑ k : Fin n,
        hallHeydeFinConditionalLindeberg mu filtration increment epsilon n k omega) =
      hallHeydeArrayConditionalLindeberg mu filtration increment epsilon n omega := by
  simpa [hallHeydeFinConditionalLindeberg,
    hallHeydeArrayConditionalLindeberg] using
    (Fin.sum_univ_eq_sum_range
      (fun k =>
        mu[(fun omega =>
          if epsilon < |increment n k omega| then increment n k omega ^ 2 else 0) |
            filtration n k] omega) n)

private theorem finRowSum_eq_terminal
    {Omega : Type*} (increment : Nat -> Nat -> Omega -> Real) :
    hallHeydeDeterministicVarianceRowSum (fun n => n)
        (hallHeydeFinIncrement increment) =
      martingaleArrayTerminalSum increment := by
  funext n omega
  simpa [hallHeydeDeterministicVarianceRowSum, hallHeydeFinIncrement,
    martingaleArrayTerminalSum, martingaleArrayPartialSum] using
    (Fin.sum_univ_eq_sum_range (fun k => increment n k omega) n)

/-- The old fixed-row-length Hall--Heyde interface follows from the single
source-faithful deterministic-variance literature atom. -/
theorem hallHeyde1980_corollary3_1_of_deterministicVariance_external
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Nat -> Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> Real)
    (variance : Real) (hvarianceNonnegative : 0 <= variance)
    (hmartingale : forall n,
      Martingale (martingaleArrayPartialSum increment n) (filtration n) mu)
    (hsquareIntegrable : forall n k, MemLp (increment n k) 2 mu)
    (hnested : forall n k, filtration n k <= filtration (n + 1) k)
    (hLindeberg : forall epsilon : Real, 0 < epsilon ->
      TendstoInMeasure mu
        (hallHeydeArrayConditionalLindeberg mu filtration increment epsilon)
        atTop (fun _ => 0))
    (hConditionalVariance :
      TendstoInMeasure mu
        (hallHeydeArrayConditionalVariance mu filtration increment)
        atTop (fun _ => variance)) :
    TendstoInDistribution (martingaleArrayTerminalSum increment) atTop id
      (fun _ => mu) (gaussianReal 0 variance.toNNReal) := by
  let finIncrement : (n : Nat) -> Fin n -> Omega -> Real :=
    hallHeydeFinIncrement increment
  let conditionalVariance : (n : Nat) -> Fin n -> Omega -> Real :=
    hallHeydeFinConditionalVariance mu filtration increment
  let conditionalLindeberg :
      Real -> (n : Nat) -> Fin n -> Omega -> Real :=
    hallHeydeFinConditionalLindeberg mu filtration increment
  have hpremises :
      HallHeyde1980Corollary31DeterministicVariancePremises
        mu (fun n => n) filtration finIncrement conditionalVariance
          conditionalLindeberg variance := by
    refine
      { condition321 := ?_
        increment_measurable := ?_
        increment_integrable := ?_
        increment_square_integrable := ?_
        martingaleDifference := ?_
        conditionalVarianceVersion := ?_
        conditionalLindebergVersion := ?_
        sigmaSq_nonnegative := hvarianceNonnegative
        conditionalVariance_converges := ?_
        conditionalLindeberg_converges := ?_ }
    · intro n k _ _
      exact hnested n k
    · intro n k
      have hm := hmartingale n
      rw [show finIncrement n k = increment n k.1 by rfl,
        increment_eq_partialSum_succ_sub increment n k.1]
      exact ((hm.stronglyAdapted (k.1 + 1)).sub
        (hm.stronglyAdapted.stronglyMeasurable_le
          (Nat.le_succ k.1))).measurable
    · intro n k
      exact (hsquareIntegrable n k.1).integrable (by norm_num)
    · intro n k
      exact (memLp_two_iff_integrable_sq
        (hsquareIntegrable n k.1).1).1 (hsquareIntegrable n k.1)
    · intro n k
      have hm := hmartingale n
      rw [show finIncrement n k = increment n k.1 by rfl,
        increment_eq_partialSum_succ_sub increment n k.1]
      calc
        mu[(fun omega =>
              martingaleArrayPartialSum increment n (k.1 + 1) omega -
                martingaleArrayPartialSum increment n k.1 omega) |
            filtration n k.1] =ᵐ[mu]
            mu[(martingaleArrayPartialSum increment n (k.1 + 1)) |
                filtration n k.1] -
              mu[(martingaleArrayPartialSum increment n k.1) |
                filtration n k.1] :=
          condExp_sub (hm.integrable (k.1 + 1)) (hm.integrable k.1) _
        _ =ᵐ[mu] fun _ : Omega => 0 := by
          have hself :
              mu[(martingaleArrayPartialSum increment n k.1) |
                  filtration n k.1] =
                martingaleArrayPartialSum increment n k.1 :=
            condExp_of_stronglyMeasurable ((filtration n).le k.1)
              (hm.stronglyAdapted k.1) (hm.integrable k.1)
          have hsucc :
              mu[(martingaleArrayPartialSum increment n (k.1 + 1)) |
                  filtration n k.1] =ᵐ[mu]
                martingaleArrayPartialSum increment n k.1 := by
            simpa only [Nat.succ_eq_add_one] using
              hm.condExp_ae_eq (Nat.le_succ k.1)
          filter_upwards [hsucc] with omega hsuccOmega
          simpa only [Pi.sub_apply, hsuccOmega, hself, sub_self]
    · intro n k
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · intro epsilon hepsilon n k
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · unfold HallHeydeScalarConvergesInProbability
      intro epsilon hepsilon
      have hmeasure :=
        (tendstoInMeasure_iff_norm.mp hConditionalVariance) epsilon hepsilon
      simpa only [conditionalVariance, finConditionalVariance_sum_eq,
        Pi.zero_apply, Real.norm_eq_abs] using hmeasure
    · intro epsilon hepsilon
      unfold HallHeydeScalarConvergesInProbability
      intro delta hdelta
      have hmeasure :=
        (tendstoInMeasure_iff_norm.mp (hLindeberg epsilon hepsilon)) delta hdelta
      simpa only [conditionalLindeberg, finConditionalLindeberg_sum_eq,
        Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hmeasure
  have hsource :=
    hallHeyde1980_corollary3_1_deterministicVariance_external
      mu (fun n => n) filtration finIncrement conditionalVariance
        conditionalLindeberg variance hpremises
  simpa only [finIncrement, finRowSum_eq_terminal] using hsource

end

end QubitOracle.Paper
