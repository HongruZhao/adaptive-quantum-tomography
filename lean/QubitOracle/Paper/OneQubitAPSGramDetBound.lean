import QubitOracle.Paper.OneQubitAPSRidgeRateCertificate

namespace QubitOracle.Paper

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Every coordinate of a physical Bloch axis has absolute value at most one. -/
theorem abs_blochCoordinate_le_one
    (u : Fin 3 -> Real) (hPhysical : QubitOracle.blochNormSq u <= 1)
    (i : Fin 3) : |u i| <= 1 := by
  have hsq : (u i) ^ 2 <= QubitOracle.blochNormSq u := by
    unfold QubitOracle.blochNormSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  have habsSq : |u i| ^ 2 <= 1 := by simpa [sq_abs] using hsq.trans hPhysical
  nlinarith [abs_nonneg (u i)]

/-- Coordinate formula for the regularized qubit Gram matrix at lambda one. -/
theorem oneQubitAPSGram_one_entry
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (omega : Omega) (i j : Fin 3) :
    PopularRLSConditions.aps2011Theorem2Gram
      (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega i j =
      (if i = j then 1 else 0) +
        ∑ k ∈ Finset.range n, axis k omega i * axis k omega j := by
  simp [PopularRLSConditions.aps2011Theorem2Gram,
    PopularRLSConditions.aps2011Theorem2Regularizer,
    SourceFaithfulSelfNormalized.regularizedGram,
    SourceFaithfulSelfNormalized.gramProcess,
    SourceFaithfulSelfNormalized.vectorOuterProduct,
    BinaryQubitRLSReducedProbabilityPremises.toSelfNormalizedMartingaleData,
    selfNormalizedMartingaleData_of_boundedCenteredNoise,
    Matrix.one_apply, Matrix.sum_apply]

/-- Every entry of the lambda-one qubit Gram matrix is bounded by n+1. -/
theorem abs_oneQubitAPSGram_one_entry_le
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (omega : Omega) (i j : Fin 3) :
    |PopularRLSConditions.aps2011Theorem2Gram
      (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega i j| <=
      (n : Real) + 1 := by
  rw [oneQubitAPSGram_one_entry protocol hTheta n omega i j]
  have hTerm : forall k, k ∈ Finset.range n ->
      |axis k omega i * axis k omega j| <= 1 := by
    intro k hk
    rw [abs_mul]
    have hi := abs_blochCoordinate_le_one (axis k omega)
      (protocol.physicalAxis k omega) i
    have hj := abs_blochCoordinate_le_one (axis k omega)
      (protocol.physicalAxis k omega) j
    nlinarith [abs_nonneg (axis k omega i), abs_nonneg (axis k omega j)]
  calc
    |(if i = j then 1 else 0) +
        ∑ k ∈ Finset.range n, axis k omega i * axis k omega j| <=
      |(if i = j then (1 : Real) else 0)| +
        |∑ k ∈ Finset.range n, axis k omega i * axis k omega j| :=
      abs_add_le _ _
    _ <= 1 + ∑ k ∈ Finset.range n,
        |axis k omega i * axis k omega j| := by
      gcongr
      · split_ifs <;> norm_num
      · exact Finset.abs_sum_le_sum_abs _ _
    _ <= 1 + ∑ _k ∈ Finset.range n, (1 : Real) := by
      gcongr with k hk
      exact hTerm k hk
    _ = (n : Real) + 1 := by simp [add_comm]

/-- Determinant bound obtained directly from the six Leibniz terms in
three dimensions. -/
theorem abs_oneQubitAPSGram_one_det_le
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (omega : Omega) :
    |(PopularRLSConditions.aps2011Theorem2Gram
      (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega).det| <=
      6 * ((n : Real) + 1) ^ 3 := by
  let A := PopularRLSConditions.aps2011Theorem2Gram
    (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega
  have hEntry : forall i j, |A i j| <= (n : Real) + 1 := by
    intro i j
    exact abs_oneQubitAPSGram_one_entry_le protocol hTheta n omega i j
  have hN : 0 <= (n : Real) + 1 := by positivity
  rw [Matrix.det_apply']
  calc
    |∑ sigma : Equiv.Perm (Fin 3),
        (((Equiv.Perm.sign sigma : ℤˣ) : ℤ) : Real) * ∏ i, A (sigma i) i| <=
      ∑ sigma : Equiv.Perm (Fin 3),
        |(((Equiv.Perm.sign sigma : ℤˣ) : ℤ) : Real) * ∏ i, A (sigma i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _sigma : Equiv.Perm (Fin 3), ((n : Real) + 1) ^ 3 := by
      gcongr with sigma
      have hSign : |(((Equiv.Perm.sign sigma : ℤˣ) : ℤ) : Real)| = 1 := by
        norm_cast
        exact Equiv.Perm.sign_abs sigma
      rw [abs_mul, hSign, one_mul]
      have hAbsProd : |∏ i : Fin 3, A (sigma i) i| =
          ∏ i : Fin 3, |A (sigma i) i| := by
        simpa using Finset.abs_prod (Finset.univ : Finset (Fin 3))
          (fun i => A (sigma i) i)
      rw [hAbsProd]
      have hProd : (∏ i : Fin 3, |A (sigma i) i|) <=
          ∏ _i : Fin 3, ((n : Real) + 1) := by
        exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hEntry _ _)
      simpa [Fin.prod_univ_succ, pow_succ] using hProd
    _ = 6 * ((n : Real) + 1) ^ 3 := by
      norm_num [Fintype.card_perm, Nat.factorial]

end

end QubitOracle.Paper
