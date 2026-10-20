import QubitOracle.Paper.CanonicalResolvedLabels

/-!
# Exceptional-round estimates in Proposition 1

The exceptional-round condition is encoded as the paper's exact `o(N)`
ratio.  The main lemma proves the quantitative step used in the hybrid
argument: a `C/N` local Bures bound multiplied by a sublinear expected count
vanishes.  No Hellinger or quantum-data-processing theorem is assumed here;
those model-to-distance comparisons remain separate interfaces.
-/

namespace QubitOracle.Paper

open Filter

noncomputable section

/-- The displayed assertion `E[# exceptional rounds] = o(N)`. -/
def ExceptionalCountSublinearInMean (expectedCount : Nat -> Real) : Prop :=
  Tendsto (fun n => expectedCount n / (n : Real)) atTop (nhds 0)

/-- The deterministic hybrid sum is bounded by the local `C/N` estimate
times the number of exceptional rounds. -/
theorem exceptionalRoundHybridSum_le
    {n : Nat} (localMass indicator : Fin n -> Real) (C : Real)
    (hRound : forall t, localMass t <= C / (n : Real) * indicator t) :
    Finset.univ.sum localMass <=
      C / (n : Real) * Finset.univ.sum indicator := by
  calc
    Finset.univ.sum localMass <=
        Finset.univ.sum (fun t => C / (n : Real) * indicator t) :=
      Finset.sum_le_sum (fun t _ => hRound t)
    _ = C / (n : Real) * Finset.univ.sum indicator := by
      rw [Finset.mul_sum]

/-- The exceptional Hellinger/Bures upper bound in Proposition 1 is `o(1)`
whenever the expected exceptional count is `o(N)`. -/
theorem exceptionalBuresMass_tendsto_zero
    (expectedCount : Nat -> Real) (C : Real)
    (hSublinear : ExceptionalCountSublinearInMean expectedCount) :
    Tendsto (fun n : Nat => C / (n : Real) * expectedCount n)
      atTop (nhds 0) := by
  have hRewrite :
      (fun n : Nat => C / (n : Real) * expectedCount n) =
        (fun n : Nat => C * (expectedCount n / (n : Real))) := by
    funext n
    ring
  rw [hRewrite]
  simpa using (tendsto_const_nhds.mul hSublinear)

namespace Label

/-- Main-text `eq:main_exception_count`: exact typed form of the sublinear
mean exceptional-shot assumption. -/
theorem eq_main_exception_count (expectedCount : Nat -> Real) :
    ExceptionalCountSublinearInMean expectedCount <->
      Tendsto (fun n => expectedCount n / (n : Real)) atTop (nhds 0) :=
  Iff.rfl

/-- Kernel-checked numerical consequence used when restoring exceptional
rounds in Proposition 1. -/
theorem eq_main_exception_Hellinger_mass
    (expectedCount : Nat -> Real) (C : Real)
    (hSublinear : ExceptionalCountSublinearInMean expectedCount) :
    Tendsto (fun n : Nat => C / (n : Real) * expectedCount n)
      atTop (nhds 0) :=
  exceptionalBuresMass_tendsto_zero expectedCount C hSublinear

end Label

end

end QubitOracle.Paper
