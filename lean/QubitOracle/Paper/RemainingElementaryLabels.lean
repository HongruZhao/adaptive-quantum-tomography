import QubitOracle.RankOneLosses
import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.PaperProtocolDefinitions
import QubitOracle.Paper.PowerExplorationOrders
import QubitOracle.Paper.SequentialHessian

/-!
# Remaining elementary manuscript labels

This module closes the remaining definition and finite-algebra labels that do
not require a concentration theorem.  In particular, all probability and rate
conclusions below are derived from exact finite identities, positivity, or the
terminal exploration-rate hypothesis.  No scientific axiom is introduced.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open Filter

noncomputable section

/-! ## The rare eigenbasis outcome -/

/-- Total probability in the coordinates orthogonal to the reference ray. -/
def eigenbasisRareProbability {n : Nat}
    (h : QubitOracle.TangentIndex n -> Real) : Real :=
  ∑ k : Fin n, Complex.normSq (QubitOracle.chartState h k.succ)

/-- In the normalized rank-one chart the rare probability is exactly one
quarter of the squared tangent radius. -/
theorem eigenbasisRareProbability_eq {n : Nat}
    (h : QubitOracle.TangentIndex n -> Real) :
    eigenbasisRareProbability h = QubitOracle.tangentRadiusSq h / 4 := by
  unfold eigenbasisRareProbability QubitOracle.tangentRadiusSq
  simp only [QubitOracle.chartState, Fin.cases_succ, Complex.normSq_mk]
  rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
  calc
    (∑ i : Fin n,
          h (Sum.inl i : QubitOracle.TangentIndex n) / 2 *
            (h (Sum.inl i : QubitOracle.TangentIndex n) / 2)) +
        (∑ i : Fin n,
          h (Sum.inr i : QubitOracle.TangentIndex n) / 2 *
            (h (Sum.inr i : QubitOracle.TangentIndex n) / 2)) =
      (∑ i : Fin n, h (Sum.inl i : QubitOracle.TangentIndex n) ^ 2 / 4) +
          ∑ i : Fin n, h (Sum.inr i : QubitOracle.TangentIndex n) ^ 2 / 4 := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = ((∑ i : Fin n,
          h (Sum.inl i : QubitOracle.TangentIndex n) ^ 2) +
        ∑ i : Fin n,
          h (Sum.inr i : QubitOracle.TangentIndex n) ^ 2) / 4 := by
      simp only [div_eq_mul_inv, add_mul, Finset.sum_mul]

/-- Scaling a tangent vector by `1 / sqrt N` scales its squared radius by
`1 / N`. -/
theorem tangentRadiusSq_div_sqrt_nat {n : Nat}
    (t : QubitOracle.TangentIndex n -> Real) (N : Nat) (hN : 0 < N) :
    QubitOracle.tangentRadiusSq
        (fun j => t j / Real.sqrt (N : Real)) =
      QubitOracle.tangentRadiusSq t / (N : Real) := by
  have hNreal : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hNreal)
  have hsquare : Real.sqrt (N : Real) ^ 2 = (N : Real) :=
    Real.sq_sqrt hNreal.le
  unfold QubitOracle.tangentRadiusSq
  calc
    (∑ j, (t j / Real.sqrt (N : Real)) ^ 2) =
        ∑ j, t j ^ 2 / (N : Real) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_pow, hsquare]
    _ = (∑ j, t j ^ 2) / (N : Real) := by
      rw [Finset.sum_div]

/-! ## Mixed-qubit pilot information -/

/-- Quadratic form used to state the real Loewner order without hiding any
matrix-order convention. -/
def realMatrixQuadratic {D : Type*} [Fintype D]
    (A : Matrix D D Real) (x : D -> Real) : Real :=
  dotProduct x (A.mulVec x)

/-- Three pilot axes, encoded by the two elementary consequences of
orthonormality used in the manuscript proof: unit length and Parseval. -/
structure MixedPilotAxes where
  axis : Fin 3 -> Fin 3 -> Real
  unit : ∀ j, QubitOracle.blochNormSq (axis j) = 1
  parseval : ∀ x,
    (∑ j, QubitOracle.blochDot (axis j) x ^ 2) =
      QubitOracle.blochNormSq x

/-- The smallest of the three integer pilot counts. -/
def mixedPilotMinCount (count : Fin 3 -> Nat) : Nat :=
  min (count 0) (min (count 1) (count 2))

theorem mixedPilotMinCount_le (count : Fin 3 -> Nat) (j : Fin 3) :
    mixedPilotMinCount count ≤ count j := by
  fin_cases j <;> simp [mixedPilotMinCount]

/-- Total Fisher information supplied by the three mixed-qubit pilot axes. -/
def mixedPilotInformation (theta : Fin 3 -> Real) (axes : MixedPilotAxes)
    (count : Fin 3 -> Nat) : Matrix (Fin 3) (Fin 3) Real :=
  ∑ j, (count j : Real) • QubitOracle.mixedAxisFisher theta (axes.axis j)

/-- One-axis Fisher information evaluated on a real direction. -/
theorem realMatrixQuadratic_mixedAxisFisher
    (theta u x : Fin 3 -> Real) :
    realMatrixQuadratic (QubitOracle.mixedAxisFisher theta u) x =
      (1 - QubitOracle.blochDot theta u ^ 2)⁻¹ *
        QubitOracle.blochDot u x ^ 2 := by
  unfold realMatrixQuadratic QubitOracle.mixedAxisFisher
    QubitOracle.blochOuter
  change (∑ i, x i * ∑ j,
      ((1 - QubitOracle.blochDot theta u ^ 2)⁻¹ * (u i * u j)) * x j) =
    (1 - QubitOracle.blochDot theta u ^ 2)⁻¹ *
      QubitOracle.blochDot u x ^ 2
  simp only [QubitOracle.blochDot, Fin.sum_univ_succ]
  ring

/-- Quadratic-form expansion of the accumulated pilot information. -/
theorem realMatrixQuadratic_mixedPilotInformation
    (theta : Fin 3 -> Real) (axes : MixedPilotAxes)
    (count : Fin 3 -> Nat) (x : Fin 3 -> Real) :
    realMatrixQuadratic (mixedPilotInformation theta axes count) x =
      ∑ j, (count j : Real) *
        ((1 - QubitOracle.blochDot theta (axes.axis j) ^ 2)⁻¹ *
          QubitOracle.blochDot (axes.axis j) x ^ 2) := by
  unfold mixedPilotInformation realMatrixQuadratic
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ i, x i *
        ((count j : Real) *
          (QubitOracle.mixedAxisFisher theta (axes.axis j)).mulVec x i)) =
        (count j : Real) *
          ∑ i, x i *
            (QubitOracle.mixedAxisFisher theta (axes.axis j)).mulVec x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (count j : Real) *
        realMatrixQuadratic
          (QubitOracle.mixedAxisFisher theta (axes.axis j)) x := rfl
    _ = _ := by rw [realMatrixQuadratic_mixedAxisFisher]

/-- The mixed-pilot Loewner lower bound, stated through all quadratic forms. -/
theorem mixedPilotInformation_lower_bound
    (theta : Fin 3 -> Real) (axes : MixedPilotAxes)
    (count : Fin 3 -> Nat)
    (htheta : QubitOracle.blochNormSq theta < 1) (x : Fin 3 -> Real) :
    (mixedPilotMinCount count : Real) * QubitOracle.blochNormSq x ≤
      realMatrixQuadratic (mixedPilotInformation theta axes count) x := by
  rw [realMatrixQuadratic_mixedPilotInformation, ← axes.parseval x,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hdenPos := QubitOracle.mixedAxisFisher_denominator_pos
    theta (axes.axis j) htheta (axes.unit j)
  have hdenLe : 1 - QubitOracle.blochDot theta (axes.axis j) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (QubitOracle.blochDot theta (axes.axis j))]
  have hinv : 1 ≤ (1 - QubitOracle.blochDot theta (axes.axis j) ^ 2)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hdenPos).2 (by simpa using hdenLe)
  have hcount : (mixedPilotMinCount count : Real) ≤ (count j : Real) := by
    exact_mod_cast mixedPilotMinCount_le count j
  have hcountNonneg : (0 : Real) ≤ count j := Nat.cast_nonneg _
  have hsquare := sq_nonneg (QubitOracle.blochDot (axes.axis j) x)
  calc
    (mixedPilotMinCount count : Real) *
        QubitOracle.blochDot (axes.axis j) x ^ 2 ≤
      (count j : Real) * QubitOracle.blochDot (axes.axis j) x ^ 2 :=
        mul_le_mul_of_nonneg_right hcount hsquare
    _ ≤ (count j : Real) *
        ((1 - QubitOracle.blochDot theta (axes.axis j) ^ 2)⁻¹ *
          QubitOracle.blochDot (axes.axis j) x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hcountNonneg
      simpa using mul_le_mul_of_nonneg_right hinv hsquare

/-! ## Recursive least-squares algebra -/

/-- Sum of the centered regression-noise increments through shot `n`. -/
def paperRegressionNoiseSum
    {M Y D : Type*} [Fintype Y] [DecidableEq Y] [Fintype D]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (outcome : Nat -> Y)
    (thetaStar : D -> Real) (n : Nat) : D -> Real :=
  ∑ i ∈ Finset.Icc 1 n,
    paperRegressionNoise c a setting outcome thetaStar i

/-- The affine response is the unregularized Gram action plus the exact
centered noise sum. -/
theorem paperControllerResponse_decompose
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (outcome : Nat -> Y)
    (thetaStar : D -> Real) (n : Nat) :
    paperControllerResponse c a setting outcome n =
      (∑ i ∈ Finset.Icc 1 n,
        paperSettingGram a (setting i)).mulVec thetaStar +
      paperRegressionNoiseSum c a setting outcome thetaStar n := by
  funext j
  simp only [paperControllerResponse, paperRegressionNoiseSum,
    paperRegressionNoise, paperAffineBornProbability, paperSettingGram,
    Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.mulVec, Matrix.sum_apply,
    Matrix.vecMulVec_apply, Finset.sum_apply, Pi.add_apply, dotProduct,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have hfactor :
      (∑ k, a (setting i) y j * a (setting i) y k * thetaStar k) =
        a (setting i) y j *
          ∑ k, a (setting i) y k * thetaStar k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfactor]
  ring

/-- Exact deterministic RLS error formula.  Invertibility is the sole linear
algebra premise; the response decomposition itself is proved above. -/
theorem paperRecursiveLS_error
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (setting : Nat -> M)
    (outcome : Nat -> Y) (thetaStar : D -> Real) (n : Nat)
    (hinvertible : IsUnit
      (paperControllerGram lambda a setting n).det) :
    paperRecursiveLS lambda c a setting outcome n - thetaStar =
      ((paperControllerGram lambda a setting n)⁻¹).mulVec
        (paperRegressionNoiseSum c a setting outcome thetaStar n -
          lambda • thetaStar) := by
  let V := paperControllerGram lambda a setting n
  let S := paperRegressionNoiseSum c a setting outcome thetaStar n
  have hresponse : paperControllerResponse c a setting outcome n =
      V.mulVec thetaStar + (S - lambda • thetaStar) := by
    rw [paperControllerResponse_decompose]
    funext j
    simp only [V, S, paperControllerGram, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Finset.sum_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold paperRecursiveLS
  change V⁻¹.mulVec (paperControllerResponse c a setting outcome n) -
      thetaStar = V⁻¹.mulVec (S - lambda • thetaStar)
  rw [hresponse, Matrix.mulVec_add]
  have hcancel : V⁻¹.mulVec (V.mulVec thetaStar) = thetaStar := by
    calc
      V⁻¹.mulVec (V.mulVec thetaStar) =
          (V⁻¹ * V).mulVec thetaStar :=
        Matrix.mulVec_mulVec thetaStar V⁻¹ V
      _ = thetaStar := by
        rw [Matrix.nonsing_inv_mul V hinvertible, Matrix.one_mulVec]
  rw [hcancel]
  abel

/-! ## Deterministic terminal-rate consequences -/

/-- The paper's `n^(1/4)` factor, written as `sqrt (sqrt n)`. -/
def natQuarterPower (n : Nat) : Real :=
  Real.sqrt (Real.sqrt (n : Real))

/-- Pointwise algebra behind equation `eq:SI_nquarter`. -/
theorem nquarter_times_sqrt_rate_eq
    (expectedExploration : Nat -> Real) (n : Nat) :
    natQuarterPower n *
        Real.sqrt (Real.log (n : Real) / expectedExploration n) =
      Real.sqrt
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n) := by
  unfold natQuarterPower
  rw [← Real.sqrt_mul (Real.sqrt_nonneg (n : Real))]
  congr 1
  ring

/-- The terminal exploration condition forces the `n^(1/4)` controller scale
to vanish. -/
theorem nquarter_rate_tendsto_zero
    (expectedExploration : Nat -> Real)
    (hterminal : TerminalExplorationRate expectedExploration) :
    Tendsto
      (fun n : Nat => natQuarterPower n *
        Real.sqrt (Real.log (n : Real) / expectedExploration n))
      atTop (nhds 0) := by
  have hsqrt : Tendsto
      (fun n : Nat => Real.sqrt
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n)) atTop (nhds 0) := by
    have hcomp :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hterminal
    change Tendsto
      (fun n : Nat => Real.sqrt
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n)) atTop (nhds (Real.sqrt 0)) at hcomp
    simpa using hcomp
  apply hsqrt.congr'
  filter_upwards [] with n
  exact (nquarter_times_sqrt_rate_eq expectedExploration n).symm

/-- Explicit finite inequalities proving the power-schedule orders used in
`eq:SI_power_orders`. -/
theorem powerExplorationMass_explicit_bounds
    (c : Real) (n0 : Nat) (alpha : Real)
    (hc : 0 < c) (hn0 : 1 ≤ n0) (halpha0 : 0 < alpha)
    (halpha1 : alpha < 1) (n : Nat) :
    min 1 c * ((n : Real) *
        Real.rpow ((n0 : Real) + n) (-alpha)) ≤
        explorationCumulativeMass
          (powerExplorationSchedule c n0 alpha) n ∧
      explorationCumulativeMass
          (powerExplorationSchedule c n0 alpha) n ≤
        c * (Real.rpow ((n0 : Real) + n) (1 - alpha) /
          (1 - alpha)) := by
  have hsandwich := powerExplorationCumulativeMass_sandwich
    c n0 alpha hc hn0 halpha0 n
  have hlower := shiftedNegativeRpowSum_lower n0 alpha hn0 halpha0 n
  have hupper := shiftedNegativeRpowSum_upper
    n0 alpha hn0 halpha0 halpha1 n
  have hmin : (0 : Real) ≤ min 1 c :=
    le_min (by norm_num) hc.le
  constructor
  · exact (mul_le_mul_of_nonneg_left hlower hmin).trans hsandwich.1
  · exact hsandwich.2.trans (mul_le_mul_of_nonneg_left hupper hc.le)

/-- Squared controller error tends to zero at root-sample scale whenever the
primitive controller bound and terminal exploration condition hold. -/
theorem controller_squared_rate_of_controller_bound
    (controllerError expectedExploration : Nat -> Real) (C : Real)
    (hC : 0 ≤ C)
    (herrorNonneg : ∀ᶠ n in atTop, 0 ≤ controllerError n)
    (hbound : ∀ᶠ n in atTop,
      controllerError n ≤
        C * Real.sqrt (Real.log (n : Real) / expectedExploration n))
    (hEpos : ∀ᶠ n in atTop, 0 < expectedExploration n)
    (hterminal : TerminalExplorationRate expectedExploration) :
    Tendsto
      (fun n : Nat =>
        Real.sqrt (n : Real) * controllerError n ^ 2)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : Nat => C ^ 2 *
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n)) atTop (nhds 0) := by
    simpa using hterminal.const_mul (C ^ 2)
  apply squeeze_zero' (herrorNonneg.mono fun n hn =>
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) _ hupper
  filter_upwards [hbound, hEpos, eventually_ge_atTop (1 : Nat),
    herrorNonneg] with n hn hEn hn1 herrNonneg
  have hlog : 0 ≤ Real.log (n : Real) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have hratio : 0 ≤ Real.log (n : Real) / expectedExploration n :=
    div_nonneg hlog hEn.le
  have hsqrtSq :
      Real.sqrt (Real.log (n : Real) / expectedExploration n) ^ 2 =
        Real.log (n : Real) / expectedExploration n :=
    Real.sq_sqrt hratio
  have herrSq : controllerError n ^ 2 ≤
      (C * Real.sqrt
        (Real.log (n : Real) / expectedExploration n)) ^ 2 :=
    by
      have hright : 0 ≤ C * Real.sqrt
          (Real.log (n : Real) / expectedExploration n) :=
        mul_nonneg hC (Real.sqrt_nonneg _)
      nlinarith
  calc
    Real.sqrt (n : Real) * controllerError n ^ 2 ≤
        Real.sqrt (n : Real) *
          (C * Real.sqrt
            (Real.log (n : Real) / expectedExploration n)) ^ 2 :=
      mul_le_mul_of_nonneg_left herrSq (Real.sqrt_nonneg _)
    _ = C ^ 2 *
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n) := by rw [mul_pow, hsqrtSq]; ring

/-! ## Proof-only rank-one regular indicator -/

/-- The proof-only indicator from the adaptive-LAN audit.  Its arguments are
all information available before the outcome on shot `i`. -/
def rankOneRegularIndicator
    (dimension : Nat) (burnIn : Nat -> Nat)
    (exploration : Nat -> Bool)
    (overlapSq : Nat -> Fin dimension -> Real)
    (sampleSize shot : Nat) : Real :=
  if burnIn sampleSize < shot ∧ exploration shot = false ∧
      ∀ k, (2 * (dimension : Real))⁻¹ ≤ overlapSq shot k
    then 1 else 0

namespace Label

/-- Supplement equation `eq:SI_eigenbasis_rare_probability`.  The manuscript
remainder can be chosen identically zero in the normalized chart. -/
theorem eq_SI_eigenbasis_rare_probability {n : Nat}
    (t : QubitOracle.TangentIndex n -> Real) (N : Nat) (hN : 0 < N) :
    eigenbasisRareProbability
        (fun j => t j / Real.sqrt (N : Real)) =
      QubitOracle.tangentRadiusSq t / (4 * (N : Real)) := by
  rw [eigenbasisRareProbability_eq,
    tangentRadiusSq_div_sqrt_nat t N hN]
  ring

/-- Supplement lemma `lem:SI_mixed_pilot`. -/
theorem lem_SI_mixed_pilot
    (theta : Fin 3 -> Real) (axes : MixedPilotAxes)
    (count : Fin 3 -> Nat) (hcount : ∀ j, 1 ≤ count j)
    (htheta : QubitOracle.blochNormSq theta < 1) :
    ∀ x, (mixedPilotMinCount count : Real) *
        QubitOracle.blochNormSq x ≤
      realMatrixQuadratic (mixedPilotInformation theta axes count) x := by
  intro x
  exact mixedPilotInformation_lower_bound theta axes count htheta x

/-- Supplement equation `eq:SI_mixed_pilot_bound`. -/
theorem eq_SI_mixed_pilot_bound
    (theta : Fin 3 -> Real) (axes : MixedPilotAxes)
    (count : Fin 3 -> Nat) (hcount : ∀ j, 1 ≤ count j)
    (htheta : QubitOracle.blochNormSq theta < 1) :
    ∀ x, (mixedPilotMinCount count : Real) *
        QubitOracle.blochNormSq x ≤
      realMatrixQuadratic (mixedPilotInformation theta axes count) x :=
  lem_SI_mixed_pilot theta axes count hcount htheta

/-- Supplement equation `eq:SI_RLS_error`. -/
theorem eq_SI_RLS_error
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (setting : Nat -> M)
    (outcome : Nat -> Y) (thetaStar : D -> Real) (n : Nat)
    (hinvertible : IsUnit
      (paperControllerGram lambda a setting n).det) :
    paperRecursiveLS lambda c a setting outcome n - thetaStar =
      ((paperControllerGram lambda a setting n)⁻¹).mulVec
        (paperRegressionNoiseSum c a setting outcome thetaStar n -
          lambda • thetaStar) :=
  paperRecursiveLS_error lambda c a setting outcome thetaStar n hinvertible

/-- Supplement equation `eq:SI_nquarter`. -/
theorem eq_SI_nquarter
    (expectedExploration : Nat -> Real)
    (hterminal : TerminalExplorationRate expectedExploration) :
    (∀ n, natQuarterPower n *
        Real.sqrt (Real.log (n : Real) / expectedExploration n) =
      Real.sqrt
        (Real.sqrt (n : Real) * Real.log (n : Real) /
          expectedExploration n)) ∧
    Tendsto
      (fun n : Nat => natQuarterPower n *
        Real.sqrt (Real.log (n : Real) / expectedExploration n))
      atTop (nhds 0) :=
  ⟨nquarter_times_sqrt_rate_eq expectedExploration,
    nquarter_rate_tendsto_zero expectedExploration hterminal⟩

/-- Supplement equation `eq:SI_r1_score_moments`, conditional on the revealed
basis.  Positivity and the two differentiated normalization identities are
the primitive fields of `FiniteLogDerivativeModel`. -/
theorem eq_SI_r1_score_moments
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (basis : M) :
    finiteOutcomeExpectation model.outcome theta basis
        (fun y => model.logScore theta basis y) = 0 ∧
      finiteOutcomeExpectation model.outcome theta basis
        (fun y => Matrix.vecMulVec
          (model.logScore theta basis y) (model.logScore theta basis y)) =
        conditionalInformation model.toFiniteScoreModel theta basis ∧
      finiteOutcomeExpectation model.outcome theta basis
        (fun y => model.observedInformation theta basis y) =
        conditionalInformation model.toFiniteScoreModel theta basis := by
  exact ⟨finiteOutcomeExpectation_score_eq_zero
      model.toFiniteScoreModel theta basis,
    finiteOutcomeExpectation_scoreOuter_eq_information
      model.toFiniteScoreModel theta basis,
    finiteOutcomeExpectation_observedInformation_eq_information
      model theta basis⟩

/-- Supplement equation `eq:SI_rank_one_regular_indicator`. -/
theorem eq_SI_rank_one_regular_indicator
    (dimension : Nat) (burnIn : Nat -> Nat)
    (exploration : Nat -> Bool)
    (overlapSq : Nat -> Fin dimension -> Real)
    (sampleSize shot : Nat) :
    rankOneRegularIndicator dimension burnIn exploration overlapSq
        sampleSize shot =
      if burnIn sampleSize < shot ∧ exploration shot = false ∧
          ∀ k, (2 * (dimension : Real))⁻¹ ≤ overlapSq shot k
        then 1 else 0 := rfl

/-- Supplement equation `eq:SI_power_orders`, in the stronger explicit
finite-bound form used to obtain both displayed `asymp` relations. -/
theorem eq_SI_power_orders
    (c : Real) (n0 : Nat) (alpha : Real)
    (hc : 0 < c) (hn0 : 1 ≤ n0) (halpha0 : 0 < alpha)
    (halpha1 : alpha < 1) (q : Nat -> Nat) (n : Nat) :
    (min 1 c * ((n : Real) *
        Real.rpow ((n0 : Real) + n) (-alpha)) ≤
          explorationCumulativeMass
            (powerExplorationSchedule c n0 alpha) n ∧
      explorationCumulativeMass
            (powerExplorationSchedule c n0 alpha) n ≤
        c * (Real.rpow ((n0 : Real) + n) (1 - alpha) /
          (1 - alpha))) ∧
    (min 1 c * ((q n : Real) *
        Real.rpow ((n0 : Real) + q n) (-alpha)) ≤
          explorationCumulativeMass
            (powerExplorationSchedule c n0 alpha) (q n) ∧
      explorationCumulativeMass
            (powerExplorationSchedule c n0 alpha) (q n) ≤
        c * (Real.rpow ((n0 : Real) + q n) (1 - alpha) /
          (1 - alpha))) :=
  ⟨powerExplorationMass_explicit_bounds
      c n0 alpha hc hn0 halpha0 halpha1 n,
    powerExplorationMass_explicit_bounds
      c n0 alpha hc hn0 halpha0 halpha1 (q n)⟩

/-- Supplement equation `eq:SI_controller_squared_rate`. -/
theorem eq_SI_controller_squared_rate
    (controllerError expectedExploration : Nat -> Real) (C : Real)
    (hC : 0 ≤ C)
    (herrorNonneg : ∀ᶠ n in atTop, 0 ≤ controllerError n)
    (hbound : ∀ᶠ n in atTop,
      controllerError n ≤
        C * Real.sqrt (Real.log (n : Real) / expectedExploration n))
    (hEpos : ∀ᶠ n in atTop, 0 < expectedExploration n)
    (hterminal : TerminalExplorationRate expectedExploration) :
    Tendsto
      (fun n : Nat =>
        Real.sqrt (n : Real) * controllerError n ^ 2)
      atTop (nhds 0) :=
  controller_squared_rate_of_controller_bound controllerError
    expectedExploration C hC herrorNonneg hbound hEpos hterminal

end Label

end

end QubitOracle.Paper
