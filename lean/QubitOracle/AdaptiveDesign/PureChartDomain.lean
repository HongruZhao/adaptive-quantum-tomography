import QubitOracle.AdaptiveDesign.PureChartDifferential

/-! The chart takes the open radius-two ball to pure states, with exact
inverse coordinates; consequently every D at least two has infinitely
many pure projectors. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def trueChartPureVector {d : ℕ} (truth : PureVector d)
    (u : EuclideanSpace ℝ (TangentIndex d)) (hu : tangentRadiusSq u ≤ 4) : PureVector d :=
  ⟨(trueFrame d truth).mulVec (chartState u), by
    change pureStateNormSq ((trueFrame d truth).mulVec (chartState u))=1
    rw [pureStateNormSq_unitary_mulVec _ (trueFrame_unitary d truth)]
    exact chartState_normalized u hu⟩

theorem trueChart_is_pure {d : ℕ} (truth : PureVector d)
    (u : EuclideanSpace ℝ (TangentIndex d)) (hu : tangentRadiusSq u ≤ 4) :
    trueChartMatrix truth u = (pureParameter d (trueChartPureVector truth u hu)).val := by
  apply toMatrix_injective
  change (trueFrame d truth)*GlobalPFSIC.projector (chartState u)*(trueFrame d truth).conjTranspose =
    GlobalPFSIC.projector ((trueFrame d truth).mulVec (chartState u))
  exact (GlobalPFSIC.projector_mulVec _ _).symm

theorem tangentRadiusSq_lt_four_of_ball {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d))
    (hu : u ∈ Metric.ball 0 2) : tangentRadiusSq u < 4 := by
  have he : tangentRadiusSq u = ‖u‖^2 := (EuclideanSpace.real_norm_sq_eq u).symm
  rw [he]
  have hh : ‖u‖ < 2 := by simpa using hu
  nlinarith [norm_nonneg u]

theorem trueChart_injectiveOn_ball {d : ℕ} (truth : PureVector d) :
    Set.InjOn (trueChartMatrix truth) (Metric.ball 0 2) := by
  intro u hu v hv huv
  have hh := congrArg (amplitudeCoordinates truth) huv
  simpa only [amplitudeCoordinates_chart truth u (tangentRadiusSq_lt_four_of_ball u hu),
    amplitudeCoordinates_chart truth v (tangentRadiusSq_lt_four_of_ball v hv)] using hh

theorem pureProjectors_infinite (d : ℕ) (hd : 0 < d) :
    Set.Infinite (Set.range (fun h : PureVector d => (pureParameter d h).val)) := by
  letI : Nonempty (TangentIndex d) := ⟨Sum.inl ⟨0,hd⟩⟩
  have hinf : Set.Infinite (Metric.ball (0 : EuclideanSpace ℝ (TangentIndex d)) 2) :=
    infinite_of_mem_nhds 0 (Metric.ball_mem_nhds _ (by norm_num))
  apply (hinf.image (trueChart_injectiveOn_ball (knownReference d))).mono
  rintro A ⟨u,hu,rfl⟩
  exact ⟨trueChartPureVector (knownReference d) u (tangentRadiusSq_lt_four_of_ball u hu).le,
    (trueChart_is_pure _ u _).symm⟩

end
end QubitOracle.AdaptiveDesign.TangentGLS
