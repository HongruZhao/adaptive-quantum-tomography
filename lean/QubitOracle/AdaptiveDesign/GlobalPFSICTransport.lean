import QubitOracle.AdaptiveDesign.GlobalPFSICFisher
import QubitOracle.Paper.RankOneStageContinuity
import QubitOracle.FiniteGillMassar
import QubitOracle.AdaptiveDesign.CompactFiberContinuity

/-! Actual transported effects and their fixed-truth Fisher information.
The controller unitary is an explicit argument throughout. -/
namespace QubitOracle.AdaptiveDesign.GlobalPFSIC
open QubitOracle.Paper Filter
open scoped BigOperators Topology ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def transportedEffect {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) (o : Outcome d) :=
  U * effect o * U.conjTranspose

theorem transportedEffect_positive {d : Nat} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) (o : Outcome d) :
    (transportedEffect U o).PosSemidef :=
  (effect_posSemidef hd o).mul_mul_conjTranspose_same U

theorem transportedEffect_complete {d : Nat} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex) :
    (∑ o, transportedEffect U o) = 1 := by
  simp only [transportedEffect, ← Matrix.sum_mul, ← Matrix.mul_sum, effect_sum hd,
    Matrix.mul_one]
  exact Matrix.mem_unitaryGroup_iff.mp hU

def transportedPOVM {d : Nat} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex) :
    FinitePOVM (Fin (d+1)) (Outcome d) where
  effect := transportedEffect U
  positive := transportedEffect_positive hd U
  complete := transportedEffect_complete hd U hU

theorem projector_mulVec {d : Nat}
    (Q : Matrix (Fin d) (Fin d) Complex) (v : Fin d → Complex) :
    projector (Q.mulVec v) = Q * projector v * Q.conjTranspose := by
  rw [projector, projector, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec]

theorem transportedEffect_projector {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) (o : Outcome d) :
    transportedEffect U o = effectWeight d • projector (U.mulVec (measurementVector o)) := by
  rw [projector_mulVec, transportedEffect, effect, Matrix.mul_smul, Matrix.smul_mul]

def transportedMass {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) (o : Outcome d) : Real :=
  (transportedEffect U o 0 0).re

def transportedGradient {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) (o : Outcome d) : TangentIndex d → Real
  | .inl j => (transportedEffect U o 0 j.succ).re
  | .inr j => -(transportedEffect U o 0 j.succ).im

def transportedFisher {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) :
    Matrix (TangentIndex d) (TangentIndex d) Real :=
  fun x y => ∑ o, safeRatio (transportedMass U o)
    (transportedGradient U o x * transportedGradient U o y)

theorem transportedFisher_eq_reference {d : Nat} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex) :
    transportedFisher U = referenceFisher (transportedPOVM hd U hU) := rfl

theorem transportedMass_continuous {d : Nat} (o : Outcome d) :
    Continuous (fun U : Matrix (Fin (d+1)) (Fin (d+1)) Complex => transportedMass U o) := by
  unfold transportedMass transportedEffect
  fun_prop

theorem transportedGradient_continuous {d : Nat} (o : Outcome d) (x : TangentIndex d) :
    Continuous (fun U : Matrix (Fin (d+1)) (Fin (d+1)) Complex =>
      transportedGradient U o x) := by
  rcases x with j | j <;> simp only [transportedGradient, transportedEffect] <;> fun_prop

theorem transportedFisher_continuousAt {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hmass : ∀ o : Outcome d, transportedMass U o ≠ 0) :
    ContinuousAt transportedFisher U := by
  apply continuousAt_pi.2
  intro x
  apply continuousAt_pi.2
  intro y
  have hterm : ∀ o : Outcome d, ContinuousAt (fun V =>
      safeRatio (transportedMass V o)
        (transportedGradient V o x * transportedGradient V o y)) U := by
    intro o
    have hm := transportedMass_continuous o
    have hg := (transportedGradient_continuous o x).mul (transportedGradient_continuous o y)
    have he : ∀ᶠ V in nhds U, transportedMass V o ≠ 0 :=
      hm.continuousAt.eventually_ne (hmass o)
    apply (hg.continuousAt.div hm.continuousAt (hmass o)).congr_of_eventuallyEq
    filter_upwards [he] with V hV
    simp only [safeRatio, if_neg hV]
    rfl
  unfold transportedFisher
  fun_prop

theorem transported_head_of_overlap_one {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1) (o : Outcome d) :
    U.mulVec (measurementVector o) 0 = U 0 0 * Real.sqrt (latitude d o.1) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    measurementVector, liftVector, Fin.cases_zero, Fin.cases_succ]
  have hz : ∀ j : Fin d, U 0 j.succ = 0 := fun j =>
    unitary_firstRow_eq_zero_of_overlap_one U hU hoverlap j.succ (Fin.succ_ne_zero j)
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero]

theorem transportedMass_of_overlap_one {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1) (o : Outcome d) :
    transportedMass U o = effectWeight d * latitude d o.1 := by
  unfold transportedMass
  rw [transportedEffect_projector]
  simp only [Matrix.smul_apply, projector_apply, Complex.real_smul,
    transported_head_of_overlap_one U hU hoverlap]
  have hn : Complex.normSq (U 0 0) = 1 := hoverlap
  have hnorm : Complex.normSq (U 0 0 * (Real.sqrt (latitude d o.1) : Complex)) =
      latitude d o.1 := by
    rw [map_mul, hn, one_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (latitude_pos d o.1).le]
  have hc := congrArg Complex.re (Complex.mul_conj
    (U 0 0 * (Real.sqrt (latitude d o.1) : Complex)))
  simp only [Complex.ofReal_re] at hc
  change (U 0 0 * (Real.sqrt (latitude d o.1) : Complex) *
    star (U 0 0 * (Real.sqrt (latitude d o.1) : Complex))).re =
    Complex.normSq (U 0 0 * (Real.sqrt (latitude d o.1) : Complex)) at hc
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using congrArg (fun x : Real => effectWeight d * x) (hc.trans hnorm)


theorem transformed_library_tight {d : Nat}
    (Q : Matrix (Fin d) (Fin d) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) Complex) :
    (∑ v : LibraryIndex d, projector (Q.mulVec (libraryVector v))) =
      (4*(d:Complex)+1) • (1 : Matrix (Fin d) (Fin d) Complex) := by
  simp_rw [projector_mulVec]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, library_projector_sum,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [show Q * Q.conjTranspose = 1 from Matrix.mem_unitaryGroup_iff.mp hQ]

 theorem transported_lift_head {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (alpha beta : Real) (s : Fin 4) (v : Fin d → Complex) :
    U.mulVec (liftVector alpha beta s v) 0 = U 0 0 * alpha := by
  have hz : ∀ j : Fin d, U 0 j.succ = 0 := fun j =>
    unitary_firstRow_eq_zero_of_overlap_one U hU hoverlap j.succ (Fin.succ_ne_zero j)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, liftVector,
    Fin.cases_zero, Fin.cases_succ, hz, zero_mul, Finset.sum_const_zero, add_zero]

 theorem transported_lift_tail {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (alpha beta : Real) (s : Fin 4) (v : Fin d → Complex) (j : Fin d) :
    U.mulVec (liftVector alpha beta s v) j.succ =
      phase4 s * (beta : Complex) * ∑ k : Fin d, U j.succ k.succ * v k := by
  have hz := unitary_firstColumn_eq_zero_of_overlap_one U hU hoverlap j.succ
    (Fin.succ_ne_zero j)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, liftVector,
    Fin.cases_zero, Fin.cases_succ, hz, zero_mul, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

 theorem transported_lift_cross {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1)
    (alpha beta : Real) (s : Fin 4) (v : Fin d → Complex) (j : Fin d) :
    star (U.mulVec (liftVector alpha beta s v) 0) *
      U.mulVec (liftVector alpha beta s v) j.succ =
      (alpha * beta : Real) * phase4 s * (fiberComplement U).mulVec v j := by
  rw [transported_lift_head U hU hoverlap, transported_lift_tail U hU hoverlap]
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul,
    Matrix.mulVec, dotProduct, fiberComplement, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

 theorem transportedGradient_of_overlap_one {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1) (o : Outcome d) (x : TangentIndex d) :
    transportedGradient U o x =
      effectWeight d * Real.sqrt (latitude d o.1) * Real.sqrt (1-latitude d o.1) *
        phaseCoordinate o.2.1 ((fiberComplement U).mulVec (libraryVector o.2.2)) x := by
  have hc (j : Fin d) := transported_lift_cross U hU hoverlap
    (Real.sqrt (latitude d o.1)) (Real.sqrt (1-latitude d o.1))
    o.2.1 (libraryVector o.2.2) j
  have hconj (j : Fin d) :
      (U.mulVec (measurementVector o)) 0 * star ((U.mulVec (measurementVector o)) j.succ) =
      star ((Real.sqrt (latitude d o.1) * Real.sqrt (1-latitude d o.1) : Real) *
        phase4 o.2.1 * (fiberComplement U).mulVec (libraryVector o.2.2) j) := by
    simpa only [star_mul', star_star, measurementVector] using congrArg star (hc j)
  rcases x with j | j
  · have hr := congrArg Complex.re (hc j)
    change (star (U.mulVec (measurementVector o) 0) *
      U.mulVec (measurementVector o) j.succ).re = _ at hr
    simp only [transportedGradient, transportedEffect_projector, Matrix.smul_apply,
      projector_apply, Complex.real_smul, phaseCoordinate]
    simp [Complex.mul_re, Complex.mul_im] at hr ⊢
    linear_combination effectWeight d * hr
  · have hi := congrArg Complex.im (hc j)
    change (star (U.mulVec (measurementVector o) 0) *
      U.mulVec (measurementVector o) j.succ).im = _ at hi
    simp only [transportedGradient, transportedEffect_projector, Matrix.smul_apply,
      projector_apply, Complex.real_smul, phaseCoordinate]
    simp [Complex.mul_re, Complex.mul_im] at hi ⊢
    linear_combination effectWeight d * hi

 theorem transportedFisher_of_overlap_one {d : Nat} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : controllerTrueOverlapSq U = 1) :
    transportedFisher U =
      (1/2 : Real) • (1 : Matrix (TangentIndex d) (TangentIndex d) Real) := by
  have hQ := fiberComplement_mem_unitary U hU hoverlap
  have hcov := phaseCoordinate_family_covariance
    (fun v : LibraryIndex d => (fiberComplement U).mulVec (libraryVector v))
    (4*(d:Real)+1) (by simpa using transformed_library_tight (fiberComplement U) hQ)
  have hterm (o : Outcome d) (x y : TangentIndex d) :
      safeRatio (transportedMass U o)
        (transportedGradient U o x * transportedGradient U o y) =
      effectWeight d * (1-latitude d o.1) *
        (phaseCoordinate o.2.1 ((fiberComplement U).mulVec (libraryVector o.2.2)) x *
         phaseCoordinate o.2.1 ((fiberComplement U).mulVec (libraryVector o.2.2)) y) := by
    rw [transportedMass_of_overlap_one U hU hoverlap,
      transportedGradient_of_overlap_one U hU hoverlap,
      transportedGradient_of_overlap_one U hU hoverlap]
    exact fisher_ratio_cancel _ _ _ _ (effectWeight_pos d hd) (latitude_pos d o.1)
      (latitude_lt_one d hd o.1).le
  ext x y
  simp only [transportedFisher, hterm, Fintype.sum_prod_type, ← Finset.mul_sum,
    hcov, Matrix.smul_apply, smul_eq_mul, Fintype.sum_bool]
  have hn := tail_normalization d hd
  linear_combination (1/2 : Real) * (1 : Matrix (TangentIndex d) (TangentIndex d) Real) x y * hn


/-- The entire fixed-truth Fisher matrix converges from ray consistency alone.
The chosen complex phase and tangent complement do not have to converge. -/
theorem transportedFisher_tendsto {d : Nat} (hd : 0 < d)
    (controller : Nat → Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hunitary : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : Tendsto (fun n => controllerTrueOverlapSq (controller n))
      atTop (nhds 1)) :
    Tendsto (fun n => transportedFisher (controller n)) atTop
      (nhds ((1/2 : Real) • (1 : Matrix (TangentIndex d) (TangentIndex d) Real))) := by
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (d+1)) (Fin (d+1)) Complex |
      U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex}
    isCompact_unitaryMatrices controller hunitary
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 hoverlap
    transportedFisher ((1/2 : Real) • (1 : Matrix (TangentIndex d) (TangentIndex d) Real)) ?_
  intro U hU hOverlap
  refine ⟨transportedFisher_continuousAt U ?_, transportedFisher_of_overlap_one hd U hU hOverlap⟩
  intro o
  rw [transportedMass_of_overlap_one U hU hOverlap]
  exact (mul_pos (effectWeight_pos d hd) (latitude_pos d o.1)).ne'

 theorem transportedFisher_average_tendsto {d : Nat} (hd : 0 < d)
    (controller : Nat → Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hunitary : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hoverlap : Tendsto (fun n => controllerTrueOverlapSq (controller n))
      atTop (nhds 1)) :
    ∀ x y : TangentIndex d, Tendsto (fun N : Nat => (N : Real)⁻¹ *
      ∑ n ∈ Finset.range N, transportedFisher (controller n) x y) atTop
      (nhds (((1/2 : Real) • (1 : Matrix (TangentIndex d) (TangentIndex d) Real)) x y)) := by
  intro x y
  exact ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1
    (transportedFisher_tendsto hd controller hunitary hoverlap) x) y).cesaro_smul)


/-- The controller ray in laboratory matrix coordinates. -/
def frameProjector {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) :
    Matrix (Fin (d+1)) (Fin (d+1)) Complex := projector (fun i => U i 0)

theorem frameProjector_mul {d : Nat}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) :
    frameProjector (T * U) = T * frameProjector U * T.conjTranspose := by
  exact projector_mulVec T (fun i => U i 0)

 theorem frameProjector_zero_entry {d : Nat}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) :
    (frameProjector U 0 0).re = controllerTrueOverlapSq U := by
  have h := congrArg Complex.re (Complex.mul_conj (U 0 0))
  exact h

/-- Projector consistency in the laboratory implies overlap convergence in
any fixed true frame, including all phase choices for that true frame. -/
theorem relative_overlap_tendsto {d : Nat}
    (T : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (controller : Nat → Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hprojector : Tendsto (fun n => frameProjector (controller n)) atTop
      (nhds (frameProjector T))) :
    Tendsto (fun n => controllerTrueOverlapSq (T.conjTranspose * controller n))
      atTop (nhds 1) := by
  have hmap : Continuous (fun P : Matrix (Fin (d+1)) (Fin (d+1)) Complex =>
      ((T.conjTranspose * P * T) 0 0).re) := by
    fun_prop
  have hh := hmap.continuousAt.tendsto.comp hprojector
  have hprod : T.conjTranspose * T = 1 := Matrix.mem_unitaryGroup_iff'.mp hT
  have heq (U : Matrix (Fin (d+1)) (Fin (d+1)) Complex) :
      ((T.conjTranspose * frameProjector U * T) 0 0).re =
        controllerTrueOverlapSq (T.conjTranspose * U) := by
    have hp := frameProjector_mul T.conjTranspose U
    simp only [Matrix.conjTranspose_conjTranspose] at hp
    rw [← hp]
    exact frameProjector_zero_entry _
  simpa [Function.comp_def, heq, hprod, controllerTrueOverlapSq] using hh

 theorem relative_unitary {d : Nat}
    (T U : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex) :
    T.conjTranspose * U ∈ Matrix.unitaryGroup (Fin (d+1)) Complex := by
  apply (Matrix.unitaryGroup (Fin (d+1)) Complex).mul_mem _ hU
  apply Matrix.mem_unitaryGroup_iff.mpr
  change T.conjTranspose * T.conjTranspose.conjTranspose = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp hT

/-- Design convergence for every true ray represented by a true unitary frame.
The probability model and estimator supply laboratory projector consistency. -/
theorem transportedFisher_generalTruth_tendsto {d : Nat} (hd : 0 < d)
    (T : Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hT : T ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (controller : Nat → Matrix (Fin (d+1)) (Fin (d+1)) Complex)
    (hunitary : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) Complex)
    (hprojector : Tendsto (fun n => frameProjector (controller n)) atTop
      (nhds (frameProjector T))) :
    Tendsto (fun n => transportedFisher (T.conjTranspose * controller n)) atTop
      (nhds ((1/2 : Real) • (1 : Matrix (TangentIndex d) (TangentIndex d) Real))) :=
  transportedFisher_tendsto hd _ (fun n => relative_unitary T (controller n) hT (hunitary n))
    (relative_overlap_tendsto T hT controller hprojector)

end
end QubitOracle.AdaptiveDesign.GlobalPFSIC
