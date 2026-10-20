import MainPaperAudit
import Supplement
import Lean

/-! Audit supplementary endpoints and every retained mathematical declaration. -/
set_option maxHeartbeats 0
open Lean Elab Command Meta in
elab "#audit_clean_release" : command => do
  let env ← getEnv
  let names : List Name := [`QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding.exp_chord,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding.mgf_partialSum_le,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding.partialSum_subGaussian,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.finite_coordinates,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.logarithmic_rate_ae,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.logarithmic_rate_of_ae_bounded,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.logarithmic_tail,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.strong_law,
    `QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate.strong_law_of_ae_bounded,
    `QubitOracle.AdaptiveDesign.BoundedVarianceMGF.vector_real_moments,
    `QubitOracle.AdaptiveDesign.BoundedVarianceMGF.vector_uniformMoment,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.assumptions_implementable,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.complete_born_law,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.effect_formula,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.identifying,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.paired_fisher,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.paired_probability_lower,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.paired_probability_lower_attained,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.paired_reference_floor,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.probability_lower,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.probability_lower_attained,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.rankOne,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.reference_probability,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.regular,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.rotated_effect_formula,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.rotation_reference_component,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.rotation_reference_row,
    `QubitOracle.AdaptiveDesign.ElementaryReferencePOVM.weight_positive,
    `QubitOracle.AdaptiveDesign.GlobalPFSIC.effect_reference_probability_minimum,
    `QubitOracle.AdaptiveDesign.GlobalPFSIC.effect_reference_probability_value,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.constants_positive,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.effect_decomposition,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.gradient_product,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.gram_at_alignment,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.gram_continuous,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.gram_scalar,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.mean_at_alignment,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.mean_continuous,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.moment_at_alignment,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.moment_continuous,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.moment_limits,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.noise_scalar,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.phaseCoordinate_sum,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.referenceCoordinate_effect,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.referenceCoordinate_effect_phase_sum,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.referenceFrame_coordinate,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.referenceFrame_projection,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.reference_gram,
    `QubitOracle.AdaptiveDesign.LibraryUnweighted.variance_ratio,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.condExp_finite_linear_sum,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.inner_sq_expansion,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.normalizedSum_charFun,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.normalizedSum_measurable,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.normalized_characteristic_tendsto,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.projected_variance_eq,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.quadratic_expansion,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.scalar_clt,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.vector_clt,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.vector_clt_of_ae_bounded_covariance,
    `QubitOracle.AdaptiveDesign.MartingaleCharacteristic.vector_clt_of_covariance,
    `QubitOracle.AdaptiveDesign.MultinomialGLSIdentity.covariance_identity,
    `QubitOracle.AdaptiveDesign.P1Weighted.bures_inverseGram_moments,
    `QubitOracle.AdaptiveDesign.P1Weighted.controller_real_moments,
    `QubitOracle.AdaptiveDesign.P1Weighted.controller_uniformMoment,
    `QubitOracle.AdaptiveDesign.P1Weighted.frobenius_inverseGram_moments,
    `QubitOracle.AdaptiveDesign.P1Weighted.inverseGramNorm_measurable,
    `QubitOracle.AdaptiveDesign.P1Weighted.inverseGramNorm_of_lower,
    `QubitOracle.AdaptiveDesign.P1Weighted.inverseGram_moments_of_envelope,
    `QubitOracle.AdaptiveDesign.P1Weighted.inverseGram_nonempty,
    `QubitOracle.AdaptiveDesign.P1Weighted.inverseGram_real_moments,
    `QubitOracle.AdaptiveDesign.P1Weighted.normalizedError_inverseGram_bound,
    `QubitOracle.AdaptiveDesign.P1Weighted.raw_real_moments,
    `QubitOracle.AdaptiveDesign.P1Weighted.raw_uniformMoment,
    `QubitOracle.AdaptiveDesign.POVMEstimatorMoments.corrected_uniformMoment,
    `QubitOracle.AdaptiveDesign.POVMEstimatorMoments.correction_uniformMoment,
    `QubitOracle.AdaptiveDesign.POVMEstimatorMoments.preliminary_uniformMoment,
    `QubitOracle.AdaptiveDesign.POVMEstimatorMoments.raw_uniformMoment,
    `QubitOracle.AdaptiveDesign.POVMEstimatorMoments.score_uniformMoment,
    `QubitOracle.AdaptiveDesign.PureMatrixController.matrixCommutator_norm_le,
    `QubitOracle.AdaptiveDesign.PureMatrixController.nearestProjector_commutes,
    `QubitOracle.AdaptiveDesign.PureMatrixController.nearestProjector_expansion,
    `QubitOracle.AdaptiveDesign.PureMatrixController.nearestProjector_tangent_remainder,
    `QubitOracle.AdaptiveDesign.PureMatrixController.tangentProjector_doubleCommutator,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.batchBoundary_strictMono,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.batchBoundary_succ,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.batchRefresh_at_boundary,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.batchRefresh_iff,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.batchRefresh_lastRefresh_tendsto,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.consistent_estimate_at_batch_refresh,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.lastRefresh_at_refresh,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.lastRefresh_le,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.lastRefresh_monotone,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.lastRefresh_tendsto_of_cofinal,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.le_batchBoundary,
    `QubitOracle.AdaptiveDesign.SequentialRidgeController.unitBatch_refresh,
    `QubitOracle.AdaptiveDesign.SupplementProbability.gaussian_tail,
    `QubitOracle.AdaptiveDesign.SupplementProbability.real_moments,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualCancellationError_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualCancellationError_secondOrder,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualPreliminaryError_rootTight,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualProjectorError_norm_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualSecondOrderForcing_tight,
    `QubitOracle.AdaptiveDesign.TangentGLS.actualWeightRemainder_tight,
    `QubitOracle.AdaptiveDesign.TangentGLS.amplitudeCoordinates_chart,
    `QubitOracle.AdaptiveDesign.TangentGLS.amplitude_clt_of_projector_clt,
    `QubitOracle.AdaptiveDesign.TangentGLS.amplitude_factor_continuousAt,
    `QubitOracle.AdaptiveDesign.TangentGLS.preliminaryError_norm_le_two,
    `QubitOracle.AdaptiveDesign.TangentGLS.preliminaryError_normal_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.preliminaryError_normal_norm,
    `QubitOracle.AdaptiveDesign.TangentGLS.preliminaryError_normal_norm_sq,
    `QubitOracle.AdaptiveDesign.TangentGLS.preliminaryTangentError_norm_le,
    `QubitOracle.AdaptiveDesign.TangentGLS.projector_real_smul,
    `QubitOracle.AdaptiveDesign.TangentGLS.pureParameter_norm,
    `QubitOracle.AdaptiveDesign.TangentGLS.pureProjector_norm,
    `QubitOracle.AdaptiveDesign.TangentGLS.referenceChart_coordinate,
    `QubitOracle.AdaptiveDesign.TangentGLS.referenceChart_overlap,
    `QubitOracle.AdaptiveDesign.TangentGLS.referenceCoordinate_reference,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentProjector_apply,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentProjector_difference_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentProjector_lipschitz,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentProjector_norm_le,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentProjector_norm_sq,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangentVector_norm_le,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangent_norm_sq,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangent_numerator,
    `QubitOracle.AdaptiveDesign.TangentGLS.tangent_trace_zero,
    `QubitOracle.AdaptiveDesign.TangentGLS.toMatrix_norm,
    `QubitOracle.AdaptiveDesign.TangentGLS.trueFrame_referenceParameter,
    `QubitOracle.AdaptiveDesign.TangentGLS.unnormalizedVector_eq_mulVec,
    `QubitOracle.AdaptiveDesign.TangentGLS.unnormalized_projector,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_displacement_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_displacement_le,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_displacement_sq,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_exact_remainder,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_matrix_formula,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_overlap,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_remainder_bound,
    `QubitOracle.AdaptiveDesign.TangentGLS.updatedState_remainder_bound_global]
  for n in names do
    let some c := env.find? n | throwError "Missing supplementary endpoint: {n}"
    let st ← liftTermElabM <| withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true |>.set `pp.maxSteps (200000 : Nat)) <| ppExpr c.type
    logInfo m!"SUPPLEMENT_STATEMENT_BEGIN {n}\n{st}\nSUPPLEMENT_STATEMENT_END"
    let ax ← Lean.collectAxioms n
    logInfo m!"SUPPLEMENT_AXIOM_RECEIPT {n} {ax.toList}"
    unless ax.toList.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Unsupported supplementary axiom dependency: {n}"
  let mut pending : List Name := []
  let mut projectCount : Nat := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if mod.toString.startsWith "QubitOracle" || mod == `MainPaperTheorem31 then
      pending := n :: pending
      projectCount := projectCount + 1
  let mut seen : NameHashSet := {}
  let mut axioms : NameHashSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    match c with
    | .axiomInfo _ => axioms := axioms.insert n
    | _ => pure ()
    pending := c.type.getUsedConstants.toList ++ ((c.value? true).map (·.getUsedConstants.toList)).getD [] ++ pending
  logInfo m!"WHOLE_RELEASE_PROJECT_DECLARATIONS {projectCount}"
  logInfo m!"WHOLE_RELEASE_REACHABLE_DECLARATIONS {seen.size}"
  logInfo m!"WHOLE_RELEASE_AXIOMS {axioms.toList}"
  unless axioms.toList.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
    throwError "The retained release contains unsupported axioms."
#audit_clean_release
