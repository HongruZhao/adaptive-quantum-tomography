import QubitOracle.AdaptiveDesign.LibraryTangentFrame

/-! Operator convergence follows from consistency of the fitted ray;
no convergence of the chosen complementary basis is assumed. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian TangentGLS
open PureMatrixController FiniteFrameCoercivity Filter
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def frameAt {d : ℕ} (hd : 0 < d) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  gramCLM (fun o : Outcome d => conjugationLinear U (effectVector hd o)) (fun _ => 1)

lemma frameAt_continuous {d : ℕ} (hd : 0 < d) : Continuous (frameAt hd) := by
  have he := (toMatrixLinear (d+1)).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr toMatrix_injective)
  have hc (o : Outcome d) : Continuous (fun U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ =>
      conjugationLinear U (effectVector hd o)) := by
    apply he.isEmbedding.isInducing.continuous_iff.mpr
    change Continuous (fun U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => U*effect o*U.conjTranspose)
    fun_prop
  unfold frameAt gramCLM rankOneCLM
  fun_prop

lemma frameAt_transport {d : ℕ} (hd : 0 < d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (A : HermitianSpace (d+1)) :
    frameAt hd U A = conjugationIsometry U hU
      (frameOperator (effectVector hd) ((conjugationIsometry U hU).symm A)) := by
  change gramCLM (fun o : Outcome d => conjugationIsometry U hU (effectVector hd o))
    (fun _ => 1) A = _
  simp only [gramCLM_apply, one_mul, frameOperator_apply, map_sum, map_smul,
    transported_measurement]

lemma frameProjector_reference (d : ℕ) :
    frameProjector (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) =
      rankOneDensity (knownReference d).val := by
  ext i j
  simp [frameProjector, projector, knownReference, rankOneDensity,
    Pi.single_apply, Matrix.vecMulVec, Matrix.one_apply]

lemma conjugate_reference {d : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    conjugateMatrix U (rankOneDensity (knownReference d).val) = frameProjector U := by
  rw [← frameProjector_reference]
  exact (frameProjector_mul U 1).symm.trans (by rw [Matrix.mul_one])

lemma frameAt_aligned {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hray : frameProjector U = rankOneDensity truth.val) :
    (tangentProjector truth).comp (frameAt hd U) = gramConstant d • tangentProjector truth := by
  have htransport := tangentProjector_transport (knownReference d) truth U hU
    ((conjugate_reference U).trans hray)
  ext A
  change tangentProjector truth (frameAt hd U A) =
    gramConstant d • tangentProjector truth A
  rw [frameAt_transport hd U hU A, ← htransport, referenceFrame_projection, map_smul, htransport]
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem projected_frame_limit {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (U : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => frameProjector (U n)) atTop (𝓝 (rankOneDensity truth.val))) :
    Tendsto (fun n => (tangentProjector truth).comp (frameAt hd (U n))) atTop
      (𝓝 (gramConstant d • tangentProjector truth)) := by
  refine tendsto_of_compact_identified_fiber _ isCompact_unitaryMatrices U hU
    frameProjector (by unfold frameProjector projector; fun_prop) _ h
    (fun V => (tangentProjector truth).comp (frameAt hd V)) _ ?_
  intro V hV hv
  refine ⟨?_, frameAt_aligned hd truth V hV hv⟩
  exact ((ContinuousLinearMap.compL ℝ _ _ _ (tangentProjector truth)).continuous.comp
    (frameAt_continuous hd)).continuousAt

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
