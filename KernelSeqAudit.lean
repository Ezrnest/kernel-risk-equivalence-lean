import KernelSeq
import Mathlib.Util.AssertNoSorry

/-!
# Transitive foundation audit

Every declaration in the `KernelSeq` namespace must depend only on the three
standard foundations below. An unfinished proof or new mathematical axiom
fails this build, including when it occurs in a transitive dependency.
This checks proof dependencies, not correspondence with the manuscript.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if (`KernelSeq).isPrefixOf name then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        checked := checked + 1
      | _ => pure ()
  logInfo m!"Audited {checked} KernelSeq declarations: only propext, Classical.choice, Quot.sound allowed."

#print axioms KernelSeq.scalar_quadratic_risk_transfer_uniform
#print axioms KernelSeq.bias_relative_risk_bound
#print axioms KernelSeq.deterministic_bias_transfer
#print axioms KernelSeq.quantitative_variance_comparison
#print axioms KernelSeq.localizationCutoff_limits
#print axioms KernelSeq.risk_ratio_tendstoInMeasure_one
#print axioms KernelSeq.tendstoInMeasure_zero_of_good_events
#print axioms KernelSeq.relative_quadratic_form_comparison
#print axioms KernelSeq.abstract_risk_equivalence_inMeasure
#print axioms KernelSeq.abstract_risk_equivalence_of_rates
#print axioms KernelSeq.probabilistic_bias_transfer_on_good_events
#print axioms KernelSeq.probabilistic_variance_transfer_on_good_events
#print axioms KernelSeq.empiricalCovariance_isPositive
#print axioms KernelSeq.populationCovariance_eq_integral
#print axioms KernelSeq.ResidualFilter.Contract.shrinkage_lipschitz
#print axioms KernelSeq.regularized_covariance_loewner_comparison_complex
#print axioms KernelSeq.regularized_inverse_norm_le_real
#print axioms KernelSeq.rkhsFeature_stronglyMeasurable
#print axioms KernelSeq.rkhsEmbedding_ae
#print axioms KernelSeq.populationCovariance_feature_isCompact
#print axioms KernelSeq.fixed_design_prediction_risk
#print axioms KernelSeq.ResidualFilter.Contract.auxiliary_contract
#print axioms KernelSeq.ResidualFilter.Contract.auxiliary_inverse_lipschitz
#print axioms KernelSeq.integral_norm_sq_average_of_indep
#print axioms KernelSeq.rkhsEmbedding_isCompact
#print axioms KernelSeq.rkhsPredictionCovariance_isCompact
#print axioms KernelSeq.tsum_residualWeight_coefficients_le_residual_order
#print axioms KernelSeq.compactEigenbasis_eigen
#print axioms KernelSeq.compactRegularizedInvSqrt_normalizes
#print axioms KernelSeq.compact_regularized_loewner_comparison_real
#print axioms KernelSeq.population_residual_filter_identity
#print axioms KernelSeq.compactResidualWeightOperator_norm_sq_le
#print axioms KernelSeq.observation_pair_conditional_noise_moments_of_positive_variance
#print axioms KernelSeq.observation_pair_conditional_risk
#print axioms KernelSeq.integral_rhsFluctuation_sq_le
#print axioms KernelSeq.rhsFluctuation_div_residual_tendstoInMeasure
#print axioms KernelSeq.normalizedRHS_div_residual_tendstoInMeasure
#print axioms KernelSeq.spectral_normalizedRHS_div_residual_tendstoInMeasure
#print axioms KernelSeq.rectangularSylvester_multiplier_of_gap
#print axioms KernelSeq.positiveSpectralIndex_countable
#print axioms KernelSeq.compactResidualWeightOperator_norm_sq_le_positive
#print axioms KernelSeq.hilbertSchmidtOperator_injective
#print axioms KernelSeq.hilbertSchmidtOperator_basis_energy
#print axioms KernelSeq.hilbertSchmidtOperator_isCompact
#print axioms KernelSeq.hilbertSchmidtProduct_trace_basis_independent
#print axioms KernelSeq.positive_basisTrace_mono
#print axioms KernelSeq.integral_normalizedLeverage_eq_featureEffectiveDimension
#print axioms KernelSeq.featureFilterDimension_le_retention
#print axioms KernelSeq.integral_normalizedHSCovarianceFluctuation_sq_le
#print axioms KernelSeq.integral_centeredRankOne_square_le
#print axioms KernelSeq.stronglyMeasurable_compactSpectralMultiplier
#print axioms KernelSeq.stronglyMeasurable_empiricalSpectralEstimator
#print axioms KernelSeq.empirical_spectral_conditional_risk
#print axioms KernelSeq.empiricalVariance_eq_scaled_hs_norm
#print axioms KernelSeq.hsSchattenNorm_le_opNorm_mul_hsNorm
#print axioms KernelSeq.schatten_logarithmic_endpoint_inf
#print axioms KernelSeq.measure_logarithmicRate_exceedance_le
#print axioms KernelSeq.lpRepresentative_toLp
#print axioms KernelSeq.rkhs_conditional_prediction_risk_basisTrace
#print axioms KernelSeq.predictionSingularBasis_hasSum
#print axioms KernelSeq.sequenceBenchmark_eq_population
#print axioms KernelSeq.empirical_variance_trace_abs_sub_le
#print axioms KernelSeq.manuscriptMixedColumns_norm_le
#print axioms KernelSeq.exists_hs_compactShrinkageDifference
#print axioms KernelSeq.hs_two_sided_compression_tendsto
#print axioms KernelSeq.finite_covariance_sum_tail_featureTrace
#print axioms KernelSeq.measure_empiricalEffectiveDimension_ge_le
#print axioms KernelSeq.actual_variance_comparison_polynomial
#print axioms KernelSeq.actualShrinkageDifferenceColumns_norm_le_eta
#print axioms KernelSeq.separatedSpectralBlocks_multiplier
#print axioms KernelSeq.feature_variance_compatibility_scale_limits
#print axioms KernelSeq.positive_compact_compression_norm_eventually_eq
#print axioms KernelSeq.measure_hs_norm_gt_le_of_compression_tails
#print axioms KernelSeq.subspaceCompression_square_le
#print axioms KernelSeq.sum_integral_subspaceCompression_square_le
#print axioms KernelSeq.finiteCovarianceCompression_population_trace_le_integral
#print axioms KernelSeq.infinite_covariance_sum_tail
#print axioms KernelSeq.intrinsicBernstein_expression_le
#print axioms KernelSeq.tendstoInMeasure_zero_of_exponential_thresholds
#print axioms KernelSeq.actual_variance_relative_tendstoInMeasure
#print axioms KernelSeq.featureGaussianSequenceError_risk_eq_population
#print axioms KernelSeq.normalized_covariance_bernstein_tail
#print axioms KernelSeq.variance_compatibility_covariance_limits_of_threshold_tails
#print axioms KernelSeq.actual_variance_relative_of_compatibility
#print axioms KernelSeq.spectral_estimator_error_decomposition
#print axioms KernelSeq.actual_localized_separated_multiplier
#print axioms KernelSeq.localizedDimensionless_contract
#print axioms KernelSeq.gaussianProductLaw_iIndepFun
#print axioms KernelSeq.canonicalGaussianSequenceError_risk
#print axioms KernelSeq.canonicalGaussianSequenceError_coordinates_ae
#print axioms KernelSeq.actual_filtered_rhsFluctuation_bound
#print axioms KernelSeq.actual_common_bias_transfer
#print axioms KernelSeq.actualAuxiliaryMultiplier_norm_le
#print axioms KernelSeq.actualAuxiliaryMultiplier_perturbation_identity
#print axioms KernelSeq.hsSchurMultiplier_represents
#print axioms KernelSeq.compactBirmanSolomyakDOI_represents
#print axioms KernelSeq.compactShrinkageDOI_represents
#print axioms KernelSeq.localized_low_low_interaction_bound
#print axioms KernelSeq.rkhs_conditional_prediction_risk_energy
#print axioms KernelSeq.rkhs_variance_relative_of_compatibility
#print axioms KernelSeq.hsSchattenNorm_compression_le
#print axioms KernelSeq.hsSchattenNorm_le_of_pointwise_tendsto
#print axioms KernelSeq.actual_weighted_schatten_endpoint_of_compatibility
#print axioms KernelSeq.prediction_interaction_norm_eq
#print axioms KernelSeq.localized_high_low_interaction_bound
#print axioms KernelSeq.actualCovarianceDeviation_le_manuscriptMixedEndpoint
#print axioms KernelSeq.auxiliary_prediction_difference_bound
#print axioms KernelSeq.localized_interaction_of_auxiliary_bound
#print axioms KernelSeq.actual_bias_transfer_from_original_scales
#print axioms KernelSeq.hsSchur_schatten_bound_of_finite
#print axioms KernelSeq.infiniteHMS_bound
#print axioms KernelSeq.hsSchattenNorm_add_le
#print axioms KernelSeq.hsSchattenNorm_twoSidedComposition_le
#print axioms KernelSeq.hsSchattenNorm_integral_le
#print axioms KernelSeq.logarithmicInteractionKernel_factorization
#print axioms KernelSeq.fourierRepresentedGrid_schatten_le
#print axioms KernelSeq.localized_prediction_of_auxiliary_bound
#print axioms KernelSeq.interactionTheta_real_density_integral
#print axioms KernelSeq.interactionTheta_grid_schatten_le
#print axioms KernelSeq.logInteractionResidualProfile_lipschitz
#print axioms KernelSeq.factorizedInteraction_schatten_le
#print axioms KernelSeq.interactionChi_hms
#print axioms KernelSeq.actualLogInteractionGrid_schatten_le
#print axioms KernelSeq.actual_embedded_prediction_of_schur_bound
#print axioms KernelSeq.compact_embedded_interaction_bound
#print axioms KernelSeq.rkhs_conditional_risk_from_original_scales
#print axioms KernelSeq.normalizedLeverage_ae_le_essentialSup
#print axioms KernelSeq.localized_interaction_of_finite_analytic
#print axioms KernelSeq.actual_localized_interaction_from_finite_analytic
#print axioms KernelSeq.dividedDifference_hms
#print axioms KernelSeq.finiteLipschitzSchur_of_finiteHMS
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_hms_bernstein
#print axioms KernelSeq.finiteBasisTrace_integral
#print axioms KernelSeq.finiteBasisTrace_mul_nonneg
#print axioms KernelSeq.integral_operator_exp_le_exp_majorant
#print axioms KernelSeq.integral_operator_exp_le_bernstein_majorant
#print axioms KernelSeq.bernstein_mgf_optimized_exponent
#print axioms KernelSeq.triangularSchur_cotlar
#print axioms KernelSeq.finiteOperatorColumns_mul_norm_le_four
#print axioms KernelSeq.triangularSchur_four_le
#print axioms KernelSeq.lie_trotter_product_formula
#print axioms KernelSeq.finiteBasisTrace_fourth_product_le
#print axioms KernelSeq.finiteBasisTrace_exp_add_le
#print axioms KernelSeq.finiteSchatten_positive_mono
#print axioms KernelSeq.matrixLaplace_norm_tail
#print axioms KernelSeq.matrixLaplace_bernstein_of_trace_moment
#print axioms KernelSeq.mgf_finset_recurrence_exp
#print axioms KernelSeq.finiteBasisTrace_weighted_le_norm
#print axioms KernelSeq.integral_trace_exp_add_le_one_step_actual
#print axioms KernelSeq.finite_commonVariance_bernstein
#print axioms KernelSeq.finiteUniformIntrinsicBernstein_proved
#print axioms KernelSeq.finiteSpectralBernstein_proved
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_hms
#print axioms KernelSeq.finiteSingularValue_mul_le
#print axioms KernelSeq.finiteBasisTrace_positive_holder
#print axioms KernelSeq.finiteSchatten_mul_le_dyadic
#print axioms KernelSeq.triangularSchurHS_dyadic_le
#print axioms KernelSeq.hsSchattenNorm_antitone_exponent
#print axioms KernelSeq.le_mul_hsSchattenEndpoint_of_dyadic
#print axioms KernelSeq.finiteRectangularThresholdStep_dyadic_le
#print axioms KernelSeq.interactionChi_deriv_norm_integral_eq_one
#print axioms KernelSeq.finite_chiOffDiagonal_dyadic_le
#print axioms KernelSeq.infinite_chiOffDiagonal_dyadic_le
#print axioms KernelSeq.finite_factorizedInteraction_schatten_le_of_chiBound
#print axioms KernelSeq.actualLogInteractionGrid_dyadic_from_lipschitz
#print axioms KernelSeq.compact_embedded_interaction_bound_from_lipschitz
#print axioms KernelSeq.actual_localized_interaction_from_lipschitz
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_lipschitz
#print axioms KernelSeq.lipschitzEvenSymbol_contDiffOn
#print axioms KernelSeq.graphLatticeMultiplier_tendsto
#print axioms KernelSeq.realGraphSchur_le_of_lattice
#print axioms KernelSeq.FiniteLipschitzSchur.toDyadic
#print axioms KernelSeq.finiteDyadicLipschitz_grid_le_of_integer
#print axioms KernelSeq.finiteMatrixSchurColumns_eq_rectangular_compression
#print axioms KernelSeq.integerFixedEvenSchurColumns_dyadic_le
#print axioms KernelSeq.finiteDyadicLipschitzSchur_of_fixedEvenFourier
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_dyadic_lipschitz
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_fixed_even_fourier
#print axioms KernelSeq.integral_schatten_two_sq_walsh_transform
#print axioms KernelSeq.operator_prefix_sum_gram
#print axioms KernelSeq.finiteBasisTrace_adjoint_mul_holder
#print axioms KernelSeq.cuculescuCutoff_idempotent
#print axioms KernelSeq.cuculescuCutoff_compression_upper
#print axioms KernelSeq.cuculescuDrop_trace_bound
#print axioms KernelSeq.integral_trace_cuculescuWalsh_tail_bound
#print axioms KernelSeq.finiteSchattenNormingOperator_schatten
#print axioms KernelSeq.exists_finiteSchatten_norming
#print axioms KernelSeq.finiteSchatten_eq_sSup_tracePairing
#print axioms KernelSeq.finiteSingularValue_add_le
#print axioms KernelSeq.finiteSingularCount_add_le
#print axioms KernelSeq.finiteSchatten_rpow_eq_lintegral_count
#print axioms KernelSeq.finiteSingularMask_rpow
#print axioms KernelSeq.finiteSingularHigh_rpow
#print axioms KernelSeq.finiteSingularLow_rpow
#print axioms KernelSeq.realHeatPolynomial_heat_equation
#print axioms KernelSeq.realRieszPolynomial_eq_integral_neg_hessian
#print axioms KernelSeq.walshStoppedField_supermartingale
#print axioms KernelSeq.walshGoodMartingale_martingale
#print axioms KernelSeq.integral_hs_walshGood_energy_le
#print axioms KernelSeq.finiteMarcinkiewicz_rpow_le
#print axioms KernelSeq.lipschitzAngularProfile_contDiff
#print axioms KernelSeq.hasSum_angularRieszProfile
#print axioms KernelSeq.angularRieszCoefficient_lower
#print axioms KernelSeq.integerFixedEvenSchurColumns_dyadic_le_of_lp
#print axioms KernelSeq.finiteDyadicLipschitzSchur_of_fixedEvenFourierLp
#print axioms KernelSeq.rkhs_conditional_risk_equivalence_from_fixed_even_fourier_lp
#print axioms KernelSeq.finiteFieldMarcinkiewicz_moment_le
#print axioms KernelSeq.finiteFieldMarcinkiewicz_norm_le
#print axioms KernelSeq.finiteFieldSchattenNorm_dual_transfer
#print axioms KernelSeq.integral_walshPrefixTransform_weak_one_positive
#print axioms KernelSeq.rieszWalkTransform_endpoint_average
#print axioms KernelSeq.walkRiesz_iterated_limits
#print axioms KernelSeq.rieszWalkMean_eq_walshPrefixAverage_zero
#print axioms KernelSeq.angularCosMoment_cubic_deriv
#print axioms KernelSeq.lipschitzAngularMoments_decay
#print axioms KernelSeq.lipschitzAngularRieszMomentWeights_summable
#print axioms KernelSeq.integral_walshPrefixTransform_weak_one
#print axioms KernelSeq.walshPrefixTransformLinearMap_trace_selfadjoint
#print axioms KernelSeq.walshPrefixTransformLinearMap_moment_two_le
#print axioms KernelSeq.walshPrefixTransformLinearMap_dyadic_norm_le
#print axioms KernelSeq.angularRieszProfile_sin_average
#print axioms KernelSeq.angularCircleMap_hasSum_fourier
#print axioms KernelSeq.lipschitzAngularCosMoment_eq_zero
#print axioms KernelSeq.lipschitzEvenSymbol_eq_angular
#print axioms KernelSeq.rotatedAnisotropicRieszSymbol_eq_angular
#print axioms KernelSeq.weightedTrigPolynomial_schattenMoment_tendsto
#print axioms KernelSeq.hsSchattenNorm_angular_average_rpow_le
#print axioms KernelSeq.hsSchattenLpNorm_sum_le_of_bound
#print axioms KernelSeq.anisotropicRiesz_schattenMoment_le_of_walsh
#print axioms KernelSeq.finiteWalshLpTransformBound_proved
#print axioms KernelSeq.hasSum_fixedSymbol_rotation_Riesz
#print axioms KernelSeq.hasSum_fixedPlanarRiesz
#print axioms KernelSeq.weightedTrigColumns_angular_norm_le
#print axioms KernelSeq.rotatedRiesz_schattenLpNorm_le
#print axioms KernelSeq.fixedPlanarRieszAverage_schattenLpNorm_le
#print axioms KernelSeq.fixedEvenFourierLpBound_proved
#print axioms KernelSeq.finiteDyadicLipschitzSchur_proved
#print axioms KernelSeq.rkhs_conditional_risk_equivalence
#print axioms KernelSeq.expectation_scale_global_envelope_tail_of_square_bound
#print axioms KernelSeq.risk_expectation_from_good_bad_integrals
#print axioms KernelSeq.integral_bias_relative_risk_le
#print axioms KernelSeq.integral_actualBiasRHSAmplitude_sq_le
#print axioms KernelSeq.lambda_sq_mul_featureFilterDimension_le_sq_bound
#print axioms KernelSeq.rkhs_prediction_loss_global_le
#print axioms KernelSeq.rkhs_conditional_risk_global_le_ae
#print axioms KernelSeq.integral_sample_lpRepresentative_sq_on_rest
#print axioms KernelSeq.integral_sample_target_sq_bad_le
#print axioms KernelSeq.rkhsExpectationPredictionRisk_eq_integral_conditional
#print axioms KernelSeq.integral_rkhs_conditional_risk_bad_le
#print axioms KernelSeq.actual_bad_design_subset_leaveOneOut_ae
#print axioms KernelSeq.measurableSet_otherPairs_leaveOneOutCovarianceBad
#print axioms KernelSeq.indepFun_pair_leaveOneOutCovariance
#print axioms KernelSeq.actualCovarianceDeviation_global_ae_le
#print axioms KernelSeq.variance_compatibility_inverse_sample_le
#print axioms KernelSeq.feature_variance_compatibility_eventually_covariance_small
#print axioms KernelSeq.actual_bad_design_exponential_tail
#print axioms KernelSeq.leaveOneOutCovarianceBad_exponential_tail
#print axioms KernelSeq.normalize_bad_risk_envelope_le
#print axioms KernelSeq.rkhs_bad_risk_from_original_expectation_scale
#print axioms KernelSeq.feature_bad_design_probability_of_original_compatibility
#print axioms KernelSeq.setIntegral_empiricalEffectiveDimension_sq_le
#print axioms KernelSeq.integral_sq_le_of_linear_exponential_tail
#print axioms KernelSeq.memLp_actualCovarianceDeviation
#print axioms KernelSeq.integral_actualCovarianceDeviation_sq_le_original_scale_eventually
#print axioms KernelSeq.setIntegral_actual_variance_relative_le_covariance_moment
#print axioms KernelSeq.actual_good_variance_relative_L1_of_compatibility
#print axioms KernelSeq.fractional_second_moment_holder
#print axioms KernelSeq.integral_mixedMomentAmplitude_sq_le_originalBiasGamma
#print axioms KernelSeq.manuscriptMixedEndpoint_le_actualMixedEndpointEnvelope
#print axioms KernelSeq.actualMixedEndpointEnvelope_memLp
#print axioms KernelSeq.integral_actualMixedEndpointEnvelope_sq_le_original_scale_eventually
#print axioms KernelSeq.memLp_actualMeanPrediction
#print axioms KernelSeq.aestronglyMeasurable_actualBiasError
#print axioms KernelSeq.integral_bias_affine_coefficient_sq_le
#print axioms KernelSeq.integral_bias_source_coefficient_sq
#print axioms KernelSeq.original_expectation_bias_cutoff_limits
#print axioms KernelSeq.setIntegral_actual_good_bias_relative_le
#print axioms KernelSeq.actual_good_bias_relative_L1_of_original_scales
#print axioms KernelSeq.integrable_variance_of_risk_bias_identity
#print axioms KernelSeq.good_risk_relative_L1_of_bias_variance
#print axioms KernelSeq.rkhsExpectationPredictionRisk_eq_integral_conditional_of_integrable
#print axioms KernelSeq.rkhs_expectation_risk_equivalence
#print axioms KernelSeq.TriangularRiskModel.conditionalRisk_energy
#print axioms KernelSeq.TriangularRiskModel.expectationRisk_eq_integral
#print axioms KernelSeq.triangular_variance_scale_limits
#print axioms KernelSeq.triangular_cutoff_limits
#print axioms KernelSeq.triangular_bad_probability_tendsto_zero
#print axioms KernelSeq.triangular_expectation_polynomial_tail
#print axioms KernelSeq.norm_sq_le_source_energy
#print axioms KernelSeq.feature_target_norm_sq_le_balance_polynomial
#print axioms KernelSeq.rkhs_uniform_bad_risk_quantitative
#print axioms KernelSeq.integral_actualCovarianceDeviation_sq_le_uniform_row
#print axioms KernelSeq.setIntegral_actual_good_bias_uniform_row
#print axioms KernelSeq.setIntegral_actual_good_variance_uniform_row
#print axioms KernelSeq.eventually_uniformFamilyFilter_iff
#print axioms KernelSeq.uniformRiskInProbability_iff_product
#print axioms KernelSeq.risk_ratio_probability_of_good_bad_L1
#print axioms KernelSeq.risk_expectation_from_good_bad_rows
#print axioms KernelSeq.TriangularRiskModel.goodRiskIntegral_bound
#print axioms KernelSeq.TriangularRiskModel.badRiskIntegral_bound
#print axioms KernelSeq.triangular_good_envelope_tendsto_zero
#print axioms KernelSeq.triangular_bad_envelope_tendsto_zero
#print axioms KernelSeq.triangular_conditional_risk_equivalence
#print axioms KernelSeq.triangular_expectation_risk_equivalence
#print axioms KernelSeq.uniform_conditional_risk_equivalence
#print axioms KernelSeq.uniform_expectation_risk_equivalence
#print axioms KernelSeq.uniform_risk_equivalence_diagonal
#print axioms KernelSeq.uniform_expectation_risk_equivalence_diagonal
#print axioms KernelSeq.ResidualFilter.iteratedRidge_contract
#print axioms KernelSeq.ResidualFilter.iteratedRidge_spectralFilter
#print axioms KernelSeq.ResidualFilter.clipping_contract
#print axioms KernelSeq.ResidualFilter.clipping_spectralFilter
#print axioms KernelSeq.predictionSourceBall_eq_ellipsoid
#print axioms KernelSeq.featureSequenceSourceEnergy_le_sourceBall
#print axioms KernelSeq.ResidualFilter.Contract.resolved_shrinkage_ge_half
#print axioms KernelSeq.quarter_mul_featureSpectralCount_le_filterDimension
#print axioms KernelSeq.featureEffectiveDimension_le_fractional_moment
#print axioms KernelSeq.moment_le_polynomial_constant
#print axioms KernelSeq.ResidualFilter.contract_of_smooth_condition
#print axioms KernelSeq.ResidualFilter.contract_of_smooth_condition_nonnegative_interval
#print axioms KernelSeq.ResidualFilter.generalizedRidge_contract
#print axioms KernelSeq.ResidualFilter.powerResidualInverse_contract
#print axioms KernelSeq.ResidualFilter.pinsker_contract
#print axioms KernelSeq.ResidualFilter.smoothedCutoff_contract
#print axioms KernelSeq.ResidualFilter.gradientFlow_contract
#print axioms KernelSeq.ResidualFilter.stableGradientDescent_contract_global
#print axioms KernelSeq.featureSourceWorstBias_eq
#print axioms KernelSeq.featureSourceWorstBias_eq_populationBiasSup
#print axioms KernelSeq.featureSourceWorstBias_ridge_saturation
#print axioms KernelSeq.featureSourceWorstBias_le_of_qualification
#print axioms KernelSeq.featureEffectiveDimension_le_polynomial
#print axioms KernelSeq.featureFilterDimension_ge_polynomial_threshold
#print axioms KernelSeq.polynomial_asymptotics_iff_threshold
#print axioms KernelSeq.exponential_asymptotics_iff_threshold
#print axioms KernelSeq.TriangularRiskModel.scaleModel_compatibility
#print axioms KernelSeq.exists_favourable_polynomial_moment_exponent
#print axioms KernelSeq.original_three_scales_of_power_bounds
#print axioms KernelSeq.polynomial_sourceBall_original_scales_of_spectral_threshold
#print axioms KernelSeq.polynomial_universal_sourceBall_original_scales_of_spectral_threshold
#print axioms KernelSeq.summable_stretchedExponential
#print axioms KernelSeq.exponential_sourceBall_original_scales
#print axioms KernelSeq.polynomial_sourceBall_risk_equivalence
#print axioms KernelSeq.polynomial_universal_sourceBall_risk_equivalence
#print axioms KernelSeq.exponential_sourceBall_risk_equivalence
#print axioms KernelSeq.uniform_polynomial_sourceBall_risk_equivalence
#print axioms KernelSeq.uniform_polynomial_universal_sourceBall_risk_equivalence
#print axioms KernelSeq.uniform_exponential_sourceBall_risk_equivalence

#print axioms KernelSeq.featureSourceWorstBias_pinsker_eq
#print axioms KernelSeq.featureSequenceBias_pinsker_attained
#print axioms KernelSeq.featureSourceWorstBias_iteratedRidge_saturation
#print axioms KernelSeq.triangular_conditionalRisk_resolved_lower_tail
#print axioms KernelSeq.weighted_ac_integrable_and_integral
#print axioms KernelSeq.spectral_sum_eq_counting_integral
#print axioms KernelSeq.feature_pinsker_spectral_sum
#print axioms KernelSeq.exact_counting_moments_and_effective_dimension
#print axioms KernelSeq.exact_counting_universal_sourceBall_original_scales
#print axioms KernelSeq.featureFilterDimension_pinsker_tendsto
#print axioms KernelSeq.pinskerOracleScale_objective
#print axioms KernelSeq.pinskerOracleScale_global_min
#print axioms KernelSeq.pinskerLeadingObjective_deriv_eq_zero_iff

#print axioms KernelSeq.sphereRotation_measurePreserving
#print axioms KernelSeq.featureSymmetry_apply
#print axioms KernelSeq.normalizedLeverage_featureSymmetry
#print axioms KernelSeq.zonalSphere_leverageEssentialSup_eq_effectiveDimension
#print axioms KernelSeq.squarefreeSphereMoment_eq_inverse_product
#print axioms KernelSeq.squarefreeSphereBlock_finrank
#print axioms KernelSeq.squarefreeSphereBlock_tensor_energy_lower
#print axioms KernelSeq.finrank_le_featureSpectralCount_of_prediction_subspace
#print axioms KernelSeq.featureAdjoint_powerSeries_energy_lower

#print axioms KernelSeq.sphericalScaleModel_inverse_filter_dimension_bound
#print axioms KernelSeq.spherical_sourceBall_original_scales
#print axioms KernelSeq.spherical_sourceBall_risk_equivalence
#print axioms KernelSeq.uniform_spherical_sourceBall_risk_equivalence

#print axioms KernelSeq.uniform_sup_risk_ratio_tendsto
#print axioms KernelSeq.fixed_pinsker_sourceBall_sup_risk_transfer
#print axioms KernelSeq.pinskerWorstSequenceBenchmark_normalized_limit
#print axioms KernelSeq.pinsker_sourceBall_upper_bound
#print axioms KernelSeq.CanonicalGaussianRegression.riskModel
#print axioms KernelSeq.featureSpectrumEnumeration_of_exact_counting
#print axioms KernelSeq.canonical_gaussian_pinsker_sourceBall_upper_bound

#print axioms KernelSeq.GaussianLinearBayes.residual_covariance_eq
#print axioms KernelSeq.GaussianLinearBayes.posteriorResidual_independent_observation
#print axioms KernelSeq.GaussianLinearBayes.trace_le_decisionRisk
#print axioms KernelSeq.GaussianLinearBayes.designCoefficientBayesRisk_eq_expected_trace
#print axioms KernelSeq.GaussianLinearBayes.posDef_inverse_diagonal_ge_variational
#print axioms KernelSeq.actual_prediction_gaussian_sequence_bayes_lower
#print axioms KernelSeq.finiteSynthesis_mem_sourceBall_iff_energy
#print axioms KernelSeq.featureSourceBall_norm_le
#print axioms KernelSeq.clipHilbertBall_sq_loss_le
#print axioms KernelSeq.predictionBayesRisk_prior_shaving
#print axioms KernelSeq.predictionBayesRisk_le_minimax_add_tail
#print axioms KernelSeq.multivariateGaussian_diagonal_eq_map_pi
#print axioms KernelSeq.gaussianRegressionSampleEquiv_measurePreserving
#print axioms KernelSeq.gaussianSpectralDecision_risk_eq_expectationRisk

#print axioms KernelSeq.integral_exp_mul_sq_standardGaussian
#print axioms KernelSeq.gaussianQuadratic_relative_tail
#print axioms KernelSeq.gaussianPriorEnergy_relative_tail
#print axioms KernelSeq.gaussianPriorEnergy_outside_moment_le
#print axioms KernelSeq.feature_pinsker_prior_energy_sum
#print axioms KernelSeq.pinskerShavedOracleScale_eq_mul
#print axioms KernelSeq.featurePinskerPriorSourceEnergy_shaved_tendsto
#print axioms KernelSeq.featurePinskerPriorSequenceRisk_shaved_normalized_limit
#print axioms KernelSeq.pinskerGaussianPrior_shaved_exponential_bounds
#print axioms KernelSeq.pinskerGaussianPrior_shaved_outside_power_tendsto_zero
#print axioms KernelSeq.finiteGaussianRegression_bayes_ge_sequence

#print axioms KernelSeq.gaussianRangeMinimaxRisk_sourceBall_lt_top
#print axioms KernelSeq.pinsker_minimax_normalized_upper
#print axioms KernelSeq.finiteGaussian_minimax_sourceBall_lower
#print axioms KernelSeq.pinsker_minimax_normalized_shaved_lower
#print axioms KernelSeq.tendsto_of_pinsker_shaved_bounds
#print axioms KernelSeq.rkhs_gaussian_pinsker_upper_bound
#print axioms KernelSeq.pinsker_minimax_constant
#print axioms KernelSeq.pinsker_minimax_attainment
#print axioms KernelSeq.rkhs_gaussian_pinsker_minimax
#check KernelSeq.rkhs_gaussian_pinsker_minimax

/- The complete main statement must not reintroduce one of the named
analytic proof interfaces as a public assumption. Source correspondence and
other possible hypotheses still require the separate statement review. -/
open Lean Elab Command in
run_cmd do
  let prohibited : Array Name := #[``KernelSeq.FiniteHMS, ``KernelSeq.FiniteLipschitzSchur,
    ``KernelSeq.FiniteDyadicLipschitzSchur, ``KernelSeq.FiniteIntrinsicBernstein,
    ``KernelSeq.FiniteUniformIntrinsicBernstein, ``KernelSeq.FiniteSpectralBernstein,
    ``KernelSeq.FixedEvenFourierL2Bound, ``KernelSeq.FixedEvenFourierLpBound,
    ``KernelSeq.FiniteWalshLpTransformBound]
  for mainName in #[``KernelSeq.rkhs_conditional_risk_equivalence,
      ``KernelSeq.rkhs_expectation_risk_equivalence,
      ``KernelSeq.triangular_conditional_risk_equivalence,
      ``KernelSeq.triangular_expectation_risk_equivalence,
      ``KernelSeq.uniform_conditional_risk_equivalence,
      ``KernelSeq.uniform_expectation_risk_equivalence,
      ``KernelSeq.uniform_risk_equivalence_diagonal,
      ``KernelSeq.uniform_expectation_risk_equivalence_diagonal] do
    let info ← getConstInfo mainName
    for name in prohibited do
      if (info.type.find? (fun e => e.isConstOf name)).isSome then
        throwError "External analytic interface {name} occurs in {mainName}"
    logInfo m!"Complete main statement {mainName} has no named external analytic proof interface."

/- The changing-model and uniform conditional statements retain just the
two original scales. The extra expectation scale belongs only to the
expectation statements. This syntactic guard supplements source review. -/
open Lean Elab Command in
run_cmd do
  for mainName in #[``KernelSeq.triangular_conditional_risk_equivalence,
      ``KernelSeq.uniform_conditional_risk_equivalence,
      ``KernelSeq.uniform_risk_equivalence_diagonal] do
    let info ← getConstInfo mainName
    if (info.type.find? (fun e =>
        e.isConstOf ``KernelSeq.TriangularRiskModel.expectationScale)).isSome then
      throwError "Extra expectation scale occurs in conditional statement {mainName}"
    logInfo m!"Conditional statement {mainName} has no extra expectation scale."

/- Concrete applications must derive the three scale and dimension estimates
from their primitive spectrum/source assumptions. The regularization IsTheta
assumption is original; a direct Big-O or scale hypothesis is not an application
input. This guard checks explicit binder domains and supplements source review. -/
open Lean Elab Command in
run_cmd do
  let prohibited : Array Name := #[``Asymptotics.IsBigO,
    ``KernelSeq.SpectralScaleModel.compatibility, ``KernelSeq.SpectralScaleModel.sourceBalance,
    ``KernelSeq.SpectralScaleModel.expectationScale,
    ``KernelSeq.TriangularRiskModel.compatibility, ``KernelSeq.TriangularRiskModel.sourceBalance,
    ``KernelSeq.TriangularRiskModel.expectationScale]
  for mainName in #[``KernelSeq.rkhs_gaussian_pinsker_minimax,
      ``KernelSeq.rkhs_gaussian_pinsker_upper_bound,
      ``KernelSeq.pinsker_minimax_constant,
      ``KernelSeq.pinsker_minimax_attainment,
      ``KernelSeq.pinsker_sourceBall_upper_bound,
      ``KernelSeq.canonical_gaussian_pinsker_sourceBall_upper_bound,
      ``KernelSeq.spherical_sourceBall_original_scales,
      ``KernelSeq.spherical_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_spherical_sourceBall_risk_equivalence,
      ``KernelSeq.spherical_retained_sourceBall_original_scales,
      ``KernelSeq.spherical_retained_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_spherical_retained_sourceBall_risk_equivalence,
      ``KernelSeq.spherical_highDimensionalRidge_original_scales,
      ``KernelSeq.spherical_phaseCutoff_expected_limit,
      ``KernelSeq.rkhs_spherical_minimax_normalized_lower,
      ``KernelSeq.rkhs_spherical_highDimensional_pinsker,
      ``KernelSeq.rkhs_spherical_highDimensional_pinsker_halfLine,
      ``KernelSeq.rkhs_spherical_highDimensional_krr,
      ``KernelSeq.exact_counting_universal_sourceBall_original_scales,
      ``KernelSeq.polynomial_sourceBall_original_scales_of_spectral_threshold,
      ``KernelSeq.polynomial_universal_sourceBall_original_scales_of_spectral_threshold,
      ``KernelSeq.exponential_sourceBall_original_scales,
      ``KernelSeq.polynomial_sourceBall_risk_equivalence,
      ``KernelSeq.polynomial_universal_sourceBall_risk_equivalence,
      ``KernelSeq.exponential_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_polynomial_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_polynomial_universal_sourceBall_risk_equivalence,
      ``KernelSeq.uniform_exponential_sourceBall_risk_equivalence] do
    let info ← getConstInfo mainName
    let mut current := info.type
    while current.isForall do
      let domain := current.bindingDomain!
      for name in prohibited do
        if (domain.find? (fun e => e.isConstOf name)).isSome then
          throwError "Extra analytic or scale input {name} in application {mainName}"
      current := current.bindingBody!
    logInfo m!"Concrete application {mainName} has no explicit Big-O or scale input."


#print axioms KernelSeq.zonalSpherePredictionBasis_eigen
#print axioms KernelSeq.hasSum_zonalSphere_filterDimension
#print axioms KernelSeq.spherical_phaseCutoff_expected_limit
#print axioms KernelSeq.rkhs_spherical_minimax_normalized_lower
#print axioms KernelSeq.rkhs_spherical_highDimensional_pinsker_halfLine
#print axioms KernelSeq.rkhs_spherical_highDimensional_krr
