import Lean
import QuaternaryQuadraticForms

run_cmd do
  let environment ← Lean.getEnv
  let names : List Lean.Name := [
    `QuaternaryQuadraticForms.weighted_ray_sum,
    `QuaternaryQuadraticForms.primitiveAddChar_units_sum,
    `QuaternaryQuadraticForms.stdAddChar_units_sum,
    `QuaternaryQuadraticForms.projectiveRayVector_injective,
    `QuaternaryQuadraticForms.projectiveRayVector_surjective,
    `QuaternaryQuadraticForms.invariant_rep_mk,
    `QuaternaryQuadraticForms.cone_rep_mk,
    `QuaternaryQuadraticForms.sum_cone_weighted_eq_sum_projective,
    `QuaternaryQuadraticForms.homogeneous_eval_smul,
    `QuaternaryQuadraticForms.homogeneous_reduce_mod,
    `QuaternaryQuadraticForms.polynomialCharacterWeight_properties,
    `QuaternaryQuadraticForms.mem_projectiveQuadric_mk,
    `QuaternaryQuadraticForms.projectiveWeight_rep_mk,
    `QuaternaryQuadraticForms.hyperplane_rep_mk,
    `QuaternaryQuadraticForms.fourierSum_ray_identity,
    `QuaternaryQuadraticForms.fourierSum_zero,
    `QuaternaryQuadraticForms.reduceFrequency_eq_zero_iff,
    `QuaternaryQuadraticForms.integralFourierSum_ray_identity,
    `QuaternaryQuadraticForms.integralFourierSum_of_dvd,
    `QuaternaryQuadraticForms.complexQuadraticChar_apply,
    `QuaternaryQuadraticForms.complexQuadraticChar_isQuadratic,
    `QuaternaryQuadraticForms.complexQuadraticChar_sq,
    `QuaternaryQuadraticForms.complexQuadraticChar_ne_one,
    `QuaternaryQuadraticForms.complexQuadraticChar_intCast,
    `QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_homogeneous,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree_le,
    `QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial_quadraticValue,
    `QuaternaryQuadraticForms.quadraticZeroIndicator_eval,
    `QuaternaryQuadraticForms.quadraticCharacterPolynomial_sum_zero,
    `QuaternaryQuadraticForms.affineQuadraticCharacterSum_dvd,
    `QuaternaryQuadraticForms.quadraticTraceWeight_rep_mk,
    `QuaternaryQuadraticForms.affineQuadraticTrace_complex,
    `QuaternaryQuadraticForms.projectiveQuadraticTrace_complex,
    `QuaternaryQuadraticForms.affineQuadraticTrace_eq,
    `QuaternaryQuadraticForms.affineQuadraticTrace_dvd,
    `QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd,
    `QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd,
    `QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd,
    `QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd,
    `QuaternaryQuadraticForms.binaryVector_eq_vec,
    `QuaternaryQuadraticForms.projectiveLinePoint_injective,
    `QuaternaryQuadraticForms.projectiveLinePoint_surjective,
    `QuaternaryQuadraticForms.projectiveLinePoint_weight,
    `QuaternaryQuadraticForms.sum_projectiveLine,
    `QuaternaryQuadraticForms.projectiveLinePoint_predicate,
    `QuaternaryQuadraticForms.binaryDehom_eval,
    `QuaternaryQuadraticForms.binaryDehom_map,
    `QuaternaryQuadraticForms.binaryDehom_homogenize,
    `QuaternaryQuadraticForms.binaryDehom_ne_zero,
    `QuaternaryQuadraticForms.binaryDehom_natDegree_le,
    `QuaternaryQuadraticForms.homogenize_eval_infinity,
    `QuaternaryQuadraticForms.binaryDehom_coeff_top,
    `QuaternaryQuadraticForms.binaryDehom_natDegree_eq_iff,
    `QuaternaryQuadraticForms.binaryDehom_natDegree_lt_of_infinity_zero,
    `QuaternaryQuadraticForms.rootSet_card_le_natDegree,
    `QuaternaryQuadraticForms.geometricRootCount_eq_natDegree_iff,
    `QuaternaryQuadraticForms.geometricRootCount_eq_natDegree,
    `QuaternaryQuadraticForms.homogeneous_binary_zero_units_smul,
    `QuaternaryQuadraticForms.binaryProjectiveZeros_card,
    `QuaternaryQuadraticForms.binaryDehom_degree_and_rootCount,
    `QuaternaryQuadraticForms.binaryDehom_geometric_data,
    `QuaternaryQuadraticForms.binaryDehom_geometric_separable,
    `QuaternaryQuadraticForms.weil_bound,
    `QuaternaryQuadraticForms.weil_bound_of_separable,
    `QuaternaryQuadraticForms.projectiveLineCharacterSum_chart,
    `QuaternaryQuadraticForms.projectiveLineCharacterSum_bound_of_affine_roots,
    `QuaternaryQuadraticForms.projective_weil_bound,
    `QuaternaryQuadraticForms.pderiv_aeval_chain_rule,
    `QuaternaryQuadraticForms.eval_aeval_polynomial,
    `QuaternaryQuadraticForms.eval_pderiv_aeval_chain_rule,
    `QuaternaryQuadraticForms.mem_planeSubspace,
    `QuaternaryQuadraticForms.matrixBilin_isSymm,
    `QuaternaryQuadraticForms.matrix_mulVec_adjugate,
    `QuaternaryQuadraticForms.adjugate_bilin_self,
    `QuaternaryQuadraticForms.planeSubspace_eq_orthogonal,
    `QuaternaryQuadraticForms.plane_bilin_nondegenerate,
    `QuaternaryQuadraticForms.planeFunctional_ne_zero,
    `QuaternaryQuadraticForms.planeSubspace_finrank,
    `QuaternaryQuadraticForms.eval_planePolynomial,
    `QuaternaryQuadraticForms.planePolynomial_totalDegree_le,
    `QuaternaryQuadraticForms.plane_exists_isotropic,
    `QuaternaryQuadraticForms.exists_hyperbolic_partner,
    `QuaternaryQuadraticForms.exists_common_orthogonal,
    `QuaternaryQuadraticForms.hyperbolic_triple_linearIndependent,
    `QuaternaryQuadraticForms.exists_ternary_hyperbolic_coordinates,
    `QuaternaryQuadraticForms.plane_exists_hyperbolic_coordinates,
    `QuaternaryQuadraticForms.extendCoordinateMap_apply_map,
    `QuaternaryQuadraticForms.extendCoordinateMap_comp,
    `QuaternaryQuadraticForms.extendCoordinateMap_id,
    `QuaternaryQuadraticForms.extendCoordinateMap_injective,
    `QuaternaryQuadraticForms.eval_coordinatePolynomial,
    `QuaternaryQuadraticForms.coordinatePolynomial_homogeneous,
    `QuaternaryQuadraticForms.coordinatePolynomial_map,
    `QuaternaryQuadraticForms.extendCoordinateMap_mem_plane,
    `QuaternaryQuadraticForms.planeSubspace_finrank_of_ne_zero,
    `QuaternaryQuadraticForms.extendCoordinateMap_range_plane,
    `QuaternaryQuadraticForms.map_aeval_polynomial,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_map,
    `QuaternaryQuadraticForms.extendCoordinateMap_quadratic,
    `QuaternaryQuadraticForms.canonicalConicVector_smul,
    `QuaternaryQuadraticForms.canonicalConicVector_ne_zero,
    `QuaternaryQuadraticForms.canonicalConicValue_vector,
    `QuaternaryQuadraticForms.canonicalConicValue_smul,
    `QuaternaryQuadraticForms.canonicalConicValue_units_zero_iff,
    `QuaternaryQuadraticForms.canonicalConicProjective_mk,
    `QuaternaryQuadraticForms.canonicalConicPoint_injective,
    `QuaternaryQuadraticForms.canonicalConicVector_surjective_projective,
    `QuaternaryQuadraticForms.canonicalConicPoint_surjective,
    `QuaternaryQuadraticForms.canonicalConic_derivatives_independent,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_eval,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_homogeneous,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_partial_s,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_partial_t,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_partials_independent,
    `QuaternaryQuadraticForms.canonicalConicPolynomials_map,
    `QuaternaryQuadraticForms.BinaryNonsingular.ne_zero,
    `QuaternaryQuadraticForms.binaryDehom_derivative,
    `QuaternaryQuadraticForms.binary_euler_eval,
    `QuaternaryQuadraticForms.binaryDehom_euler,
    `QuaternaryQuadraticForms.binaryDehom_derivative_ne_zero,
    `QuaternaryQuadraticForms.binaryDehom_separable_of_nonsingular,
    `QuaternaryQuadraticForms.coeff_X_mul_derivative,
    `QuaternaryQuadraticForms.binaryDehom_degree_of_nonsingular_infinity,
    `QuaternaryQuadraticForms.binaryProjectiveZeros_card_of_nonsingular,
    `QuaternaryQuadraticForms.binary_nonsingular_geometric_roots,
    `QuaternaryQuadraticForms.independent_three_two_dot_impossible,
    `QuaternaryQuadraticForms.pderiv_planePolynomial,
    `QuaternaryQuadraticForms.polynomialGradient_plane,
    `QuaternaryQuadraticForms.eval_pderiv_pullback,
    `QuaternaryQuadraticForms.transverse_pullback_nonsingular,
    `QuaternaryQuadraticForms.rank_three_iff_linearIndependent,
    `QuaternaryQuadraticForms.planeTransverseRank_iff,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_eval,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_homogeneous,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_map,
    `QuaternaryQuadraticForms.coordinatePolynomial_pderiv,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_partial,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_partials_independent,
    `QuaternaryQuadraticForms.eval_canonicalConicPolynomial,
    `QuaternaryQuadraticForms.canonicalConicPolynomial_homogeneous,
    `QuaternaryQuadraticForms.coordinateQuadratic_pullback,
    `QuaternaryQuadraticForms.canonicalConicPolynomial_substitution,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_quadric_identity,
    `QuaternaryQuadraticForms.coordinatePlane_pullback,
    `QuaternaryQuadraticForms.embeddedConicPolynomials_plane_identity,
    `QuaternaryQuadraticForms.planeConic_units_iff,
    `QuaternaryQuadraticForms.embeddedCanonicalConicPoint_injective,
    `QuaternaryQuadraticForms.embeddedCanonicalConicPoint_surjective,
    `QuaternaryQuadraticForms.embeddedConicEquiv_mk,
    `QuaternaryQuadraticForms.goodPrime_ne_two,
    `QuaternaryQuadraticForms.goodPrime_reduced_det_ne_zero,
    `QuaternaryQuadraticForms.reduceQuadraticMatrix_symmetric,
    `QuaternaryQuadraticForms.reduceQuadraticMatrix_adjugate,
    `QuaternaryQuadraticForms.primeField_two_ne_zero,
    `QuaternaryQuadraticForms.conic_parametrization_prime_field,
    `QuaternaryQuadraticForms.conic_parametrization,
    `QuaternaryQuadraticForms.projectiveSectionTrace_eq_sum_conic,
    `QuaternaryQuadraticForms.projectiveSectionTrace_eq_projectiveLine,
    `QuaternaryQuadraticForms.plane_section_bound_of_parametrization,
    `QuaternaryQuadraticForms.plane_section_bound_prime_field,
    `QuaternaryQuadraticForms.plane_section_bound,
    `QuaternaryQuadraticForms.rank_two_iff_linearIndependent,
    `QuaternaryQuadraticForms.projectiveIntersectionTransverseRank_iff,
    `QuaternaryQuadraticForms.mem_badReductionPrimes,
    `QuaternaryQuadraticForms.prime_dvd_primeRadical_iff,
    `QuaternaryQuadraticForms.primeRadical_pos,
    `QuaternaryQuadraticForms.quadraticBadPrimeModulus_ne_zero,
    `QuaternaryQuadraticForms.polynomialBadPrimeModulus_pos,
    `QuaternaryQuadraticForms.prime_dvd_product_primes_iff,
    `QuaternaryQuadraticForms.not_dvd_polynomialBadPrimeModulus_iff,
    `QuaternaryQuadraticForms.badReductionPrimes_subset_primeFactors_of_common_divisor,
    `QuaternaryQuadraticForms.badReductionPrimes_finite_of_common_divisor,
    `QuaternaryQuadraticForms.badReductionPrimeProduct_dvd_common_divisor,
    `QuaternaryQuadraticForms.polynomialBadPrimeModulus_le_of_common_divisor,
    `QuaternaryQuadraticForms.eval_pderiv_matrixQuadraticPolynomial,
    `QuaternaryQuadraticForms.polynomialGradient_matrixQuadraticPolynomial,
    `QuaternaryQuadraticForms.matrixQuadratic_gradient_ne_zero,
    `QuaternaryQuadraticForms.matrixQuadratic_projective_smooth,
    `QuaternaryQuadraticForms.matrixQuadratic_projective_smooth_map,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_ne_zero,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree,
    `QuaternaryQuadraticForms.eval_pderiv_eq_of_totalDegree_le_one,
    `QuaternaryQuadraticForms.polynomialGradient_eq_of_totalDegree_le_one,
    `QuaternaryQuadraticForms.matrixQuadratic_not_mul_affine,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible_map,
    `QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_coeff,
    `QuaternaryQuadraticForms.surfaceChernRelation_coefficients,
    `QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_of_relation,
    `QuaternaryQuadraticForms.quadricChernPolynomial_relation,
    `QuaternaryQuadraticForms.quadric_surfaceSectionEulerCoefficient,
    `QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_quadric_of_relation,
    `QuaternaryQuadraticForms.norm_sum_le_card_mul,
    `QuaternaryQuadraticForms.mem_projectiveHypersurfacePoints_mk,
    `QuaternaryQuadraticForms.projectiveHypersurfacePoints_matrix,
    `QuaternaryQuadraticForms.projectiveHypersurfaceTrace_matrix,
    `QuaternaryQuadraticForms.transverse_polynomial_ne_zero,
    `QuaternaryQuadraticForms.quadric_transverse_polynomial_ne_zero,
    `QuaternaryQuadraticForms.katz_quadric_bound_prime_field,
    `QuaternaryQuadraticForms.katz_quadric_bound,
    `QuaternaryQuadraticForms.projectiveQuadraticTrace_abs_le,
    `QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd_bound,
    `QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_abs_le,
    `QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound,
    `QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd_bound_of_modulus,
    `QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus,
    `QuaternaryQuadraticForms.homogeneousForm_isHomogeneous,
    `QuaternaryQuadraticForms.homogeneousForm_coeff,
    `QuaternaryQuadraticForms.homogeneousForm_coeff_eq_zero_of_degree_ne,
    `QuaternaryQuadraticForms.homogeneousForm_coeff_formula,
    `QuaternaryQuadraticForms.homogeneousForm_coefficients,
    `QuaternaryQuadraticForms.homogeneousForm_map,
    `QuaternaryQuadraticForms.homogeneousSystem_parameter_coefficients,
    `QuaternaryQuadraticForms.homogeneous_parameter_resultants,
    `QuaternaryQuadraticForms.rank_two_ne_iff_minors_zero,
    `QuaternaryQuadraticForms.rank_two_iff_exists_minor_ne_zero,
    `QuaternaryQuadraticForms.card_badReductionIndex,
    `QuaternaryQuadraticForms.gradientMinor_homogeneous,
    `QuaternaryQuadraticForms.badReductionSystem_homogeneous,
    `QuaternaryQuadraticForms.badReductionSystemDegree_pos,
    `QuaternaryQuadraticForms.matrixQuadraticPolynomial_map_ring,
    `QuaternaryQuadraticForms.gradientMinor_map,
    `QuaternaryQuadraticForms.badReductionSystem_map,
    `QuaternaryQuadraticForms.eval_badReductionSystem_map,
    `QuaternaryQuadraticForms.eval_badReductionSystem_map_point,
    `QuaternaryQuadraticForms.eval_gradientMinor,
    `QuaternaryQuadraticForms.badReductionSystem_zero_iff,
    `QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff,
    `QuaternaryQuadraticForms.exists_badReductionSystem_eval,
    `QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff_not_goodReductionAt,
    `QuaternaryQuadraticForms.exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt,
    `QuaternaryQuadraticForms.two_le_polynomialCoefficientHeight,
    `QuaternaryQuadraticForms.natAbs_coeff_le_polynomialCoefficientHeight,
    `QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow,
    `QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow_of_forall,
    `QuaternaryQuadraticForms.finite_polynomial_family_eval_bound,
    `QuaternaryQuadraticForms.finite_polynomial_family_eval_bound_of_height,
    `QuaternaryQuadraticForms.finite_polynomial_family_coeff_eval_bound,
    `QuaternaryQuadraticForms.genericDegreeForm_homogeneous,
    `QuaternaryQuadraticForms.genericBadReductionSystem_homogeneous,
    `QuaternaryQuadraticForms.genericQuadricMatrix_map_eval,
    `QuaternaryQuadraticForms.genericDegreeForm_map_eval,
    `QuaternaryQuadraticForms.genericBadReductionSystem_map_eval,
    `QuaternaryQuadraticForms.genericBadReductionSystem_specialize,
    `QuaternaryQuadraticForms.genericBadReductionSystem_specialize_integral,
    `QuaternaryQuadraticForms.genericBadReductionSystem_specialize_map,
    `QuaternaryQuadraticForms.genericBadReductionSystem_specialize_intCast,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_map_intCast_iff,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_iff,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_rat_iff,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_zmod_iff,
    `QuaternaryQuadraticForms.badReduction_resultants_over_fields,
    `QuaternaryQuadraticForms.badReduction_resultant_family,
    `QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor,
    `QuaternaryQuadraticForms.badReductionPrimes_finite_of_smooth,
    `QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor_height_bound,
    `QuaternaryQuadraticForms.polynomialBadPrimeModulus_height_bound,
    `QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound,
    `QuaternaryQuadraticForms.quadratic_projective_trace_integer,
    `QuaternaryQuadraticForms.quadratic_projective_trace,
    `QuaternaryQuadraticForms.rowTripleMinor_eq_det,
    `QuaternaryQuadraticForms.rowTripleMinor_map,
    `QuaternaryQuadraticForms.rank_three_ne_iff_minors_zero,
    `QuaternaryQuadraticForms.rank_three_iff_exists_minor_ne_zero,
    `QuaternaryQuadraticForms.planeEquationPolynomial_eq_planePolynomial,
    `QuaternaryQuadraticForms.eval_planeEquationPolynomial,
    `QuaternaryQuadraticForms.planeEquationPolynomial_homogeneous,
    `QuaternaryQuadraticForms.planeEquationPolynomial_map,
    `QuaternaryQuadraticForms.gradientPlaneMinor_homogeneous,
    `QuaternaryQuadraticForms.gradientPlaneMinor_map,
    `QuaternaryQuadraticForms.eval_gradientPlaneMinor,
    `QuaternaryQuadraticForms.card_planeReductionIndex,
    `QuaternaryQuadraticForms.planeReductionSystem_homogeneous,
    `QuaternaryQuadraticForms.planeReductionSystemDegree_pos,
    `QuaternaryQuadraticForms.planeReductionSystem_map,
    `QuaternaryQuadraticForms.eval_planeReductionSystem_map,
    `QuaternaryQuadraticForms.planeReductionSystem_zero_iff,
    `QuaternaryQuadraticForms.exists_planeReductionSystem_zero_iff,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_planeReductionSystem_iff,
    `QuaternaryQuadraticForms.genericPlaneDegreeForm_homogeneous,
    `QuaternaryQuadraticForms.genericPlaneReductionSystem_homogeneous,
    `QuaternaryQuadraticForms.genericPlaneQuadricMatrix_map_eval,
    `QuaternaryQuadraticForms.genericPlaneDegreeForm_map_eval,
    `QuaternaryQuadraticForms.genericPlaneNormal_eval,
    `QuaternaryQuadraticForms.genericPlaneReductionSystem_map_eval,
    `QuaternaryQuadraticForms.genericPlaneReductionSystem_specialize,
    `QuaternaryQuadraticForms.exceptionalPlane_resultants_over_fields,
    `QuaternaryQuadraticForms.exceptionalPlane_resultant_family,
    `QuaternaryQuadraticForms.eval_specializePlaneResultant,
    `QuaternaryQuadraticForms.exceptionalPlane_specialized_resultant_family,
    `QuaternaryQuadraticForms.hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed,
    `QuaternaryQuadraticForms.specializePlaneResultant_map,
    `QuaternaryQuadraticForms.exceptionalPlane_resultants_over_algClosed_fields,
    `QuaternaryQuadraticForms.exceptionalPlane_resultants_nonzero_of_transverse_witness,
    `QuaternaryQuadraticForms.rank_three_of_rank_two_of_tangent,
    `QuaternaryQuadraticForms.exists_transverse_plane_of_smooth_intersection,
    `QuaternaryQuadraticForms.totalDegree_eval,
    `QuaternaryQuadraticForms.totalDegree_specializePlaneResultant_le,
    `QuaternaryQuadraticForms.exceptionalPlane_bounded_resultant_family,
    `QuaternaryQuadraticForms.exceptional_plane_polynomial_over_fields,
    `QuaternaryQuadraticForms.exceptional_plane_polynomial,
    `QuaternaryQuadraticForms.plane_exists_nonzero_quadratic_value,
    `QuaternaryQuadraticForms.eval_planeRestrictionPolynomial,
    `QuaternaryQuadraticForms.planeRestrictionPolynomial_homogeneous,
    `QuaternaryQuadraticForms.planeRestrictionPolynomial_totalDegree_le,
    `QuaternaryQuadraticForms.planeRestrictionPolynomial_ne_zero,
    `QuaternaryQuadraticForms.exists_plane_quadratic_restriction,
    `QuaternaryQuadraticForms.ternary_polynomial_zero_card_le,
    `QuaternaryQuadraticForms.planeSection_affine_card_eq,
    `QuaternaryQuadraticForms.planeSection_affine_card_le,
    `QuaternaryQuadraticForms.planeSection_card_le,
    `QuaternaryQuadraticForms.projectiveSectionTrace_norm_le,
    `QuaternaryQuadraticForms.fourier_generic_constant_bound,
    `QuaternaryQuadraticForms.fourier_exceptional_constant_bound,
    `QuaternaryQuadraticForms.fourier_zero_constant_bound,
    `QuaternaryQuadraticForms.rpow_three_halves_eq_mul_sqrt,
    `QuaternaryQuadraticForms.fourierSum_norm_le_section_and_trace,
    `QuaternaryQuadraticForms.fourierSum_zero_norm,
    `QuaternaryQuadraticForms.fourierSum_generic_bound,
    `QuaternaryQuadraticForms.fourierSum_zero_bound,
    `QuaternaryQuadraticForms.fourierSum_nonzero_bound,
    `QuaternaryQuadraticForms.fourierSum_bound_prime_field,
    `QuaternaryQuadraticForms.fourier_bound,
    `QuaternaryQuadraticForms.uniform_polynomial_fourier_bound,
    `QuaternaryQuadraticForms.diagonalQuadraticPolynomial_eq_sum,
    `QuaternaryQuadraticForms.diagonalPairProduct_map,
    `QuaternaryQuadraticForms.diagonalPairProduct_ne_zero_iff,
    `QuaternaryQuadraticForms.diagonal_pair_difference_ne_zero,
    `QuaternaryQuadraticForms.diagonalQuadraticPolynomial_map,
    `QuaternaryQuadraticForms.diagonal_coefficients_ne_zero,
    `QuaternaryQuadraticForms.quadraticBadPrimeModulus_diagonal,
    `QuaternaryQuadraticForms.diagonal_bad_modulus_product,
    `QuaternaryQuadraticForms.eval_diagonalQuadraticPolynomial,
    `QuaternaryQuadraticForms.polynomialGradient_diagonalQuadraticPolynomial,
    `QuaternaryQuadraticForms.diagonal_gradient_minor,
    `QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank,
    `QuaternaryQuadraticForms.exists_diagonal_rank_failure_of_pair_eq_zero,
    `QuaternaryQuadraticForms.not_diagonal_projectiveIntersectionTransverseRank_of_pair_eq_zero,
    `QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff,
    `QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff_pairProduct_ne_zero,
    `QuaternaryQuadraticForms.diagonal_smooth_characteristicZero,
    `QuaternaryQuadraticForms.diagonal_badReductionAt_iff,
    `QuaternaryQuadraticForms.badReductionPrimes_finite_of_iff_dvd,
    `QuaternaryQuadraticForms.badReductionPrimes_toFinset_eq_primeFactors_sdiff,
    `QuaternaryQuadraticForms.polynomialBadPrimeModulus_eq_primeRadical_of_bad_iff,
    `QuaternaryQuadraticForms.diagonal_badReductionPrimes_finite,
    `QuaternaryQuadraticForms.diagonal_badPrimeModulus,
    `QuaternaryQuadraticForms.diagonal_bad_primes,
    `QuaternaryQuadraticForms.nonseparable_cubic_factorization,
    `QuaternaryQuadraticForms.quadraticChar_repeated_cubic_sum,
    `QuaternaryQuadraticForms.quadraticChar_nonseparable_cubic_sum_norm_le_one,
    `QuaternaryQuadraticForms.quadraticChar_cubic_sum_norm_le,
    `QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_norm_le,
    `QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_four_norm_le,
    `QuaternaryQuadraticForms.eval_diagonalPencilPhi,
    `QuaternaryQuadraticForms.diagonalPencilCoeff_map,
    `QuaternaryQuadraticForms.diagonalKappa_map,
    `QuaternaryQuadraticForms.diagonalPencilPhi_map,
    `QuaternaryQuadraticForms.diagonalPencilNu_map,
    `QuaternaryQuadraticForms.diagonalPencilCoeff_eq_zero_iff,
    `QuaternaryQuadraticForms.diagonalPencilCoeff_at_own_root,
    `QuaternaryQuadraticForms.diagonalPencilCoeff_at_root,
    `QuaternaryQuadraticForms.diagonalPencilCoeff_at_root_ne_zero,
    `QuaternaryQuadraticForms.diagonalPencilRoot_injective,
    `QuaternaryQuadraticForms.five_le_of_diagonalPencil_roots,
    `QuaternaryQuadraticForms.diagonalPencilDelta_ne_zero,
    `QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_ne_zero,
    `QuaternaryQuadraticForms.diagonalPencilPhi_div_delta,
    `QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_eq,
    `QuaternaryQuadraticForms.neg_diagonalPencilDeltaAtRoot_eq,
    `QuaternaryQuadraticForms.diagonalKappa_ne_zero,
    `QuaternaryQuadraticForms.diagonalPencilW_eq,
    `QuaternaryQuadraticForms.diagonal_projectiveTrace_eq,
    `QuaternaryQuadraticForms.diagonal_projectiveQuadraticTrace_eq,
    `QuaternaryQuadraticForms.diagonal_fourier_generic_bound_sqrt,
    `QuaternaryQuadraticForms.diagonal_fourier_generic_bound,
    `QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_le,
    `QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three,
    `QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three_eq_eval,
    `QuaternaryQuadraticForms.eval_diagonalPencilPhi_eq_dual,
    `QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_eq_three,
    `QuaternaryQuadraticForms.diagonalPencilRawSum_regular,
    `QuaternaryQuadraticForms.diagonalPencilRawSum_singular,
    `QuaternaryQuadraticForms.mem_diagonalPencilRoots,
    `QuaternaryQuadraticForms.diagonalPencilRoots_card_le,
    `QuaternaryQuadraticForms.diagonalPencil_sum_split,
    `QuaternaryQuadraticForms.diagonal_fourier_pencil_formula,
    `QuaternaryQuadraticForms.diagonalPencil_reduced_data,
    `QuaternaryQuadraticForms.diagonalPencil_dual_map,
    `QuaternaryQuadraticForms.diagonalPencil_generic_reduction,
    `QuaternaryQuadraticForms.integral_diagonal_fourier_pencil_formula,
    `QuaternaryQuadraticForms.integral_diagonal_projectiveTrace_eq,
    `QuaternaryQuadraticForms.integral_diagonal_fourier_bound,
    `QuaternaryQuadraticForms.diagonal_pencil,
    `QuaternaryQuadraticForms.primeQuadraticGauss_phase_expansion,
    `QuaternaryQuadraticForms.fourierSum_quadraticGauss_expansion,
    `QuaternaryQuadraticForms.diagonal_fourier_pencil_expansion,
    `QuaternaryQuadraticForms.stdAddChar_orthogonality,
    `QuaternaryQuadraticForms.fourierSum_additive_expansion,
    `QuaternaryQuadraticForms.stdAddChar_sum,
    `QuaternaryQuadraticForms.diagonal_exponential_sum_factorization,
    `QuaternaryQuadraticForms.complexQuadraticChar_sq_apply,
    `QuaternaryQuadraticForms.primeQuadraticGauss_ne_zero,
    `QuaternaryQuadraticForms.primeQuadraticGauss_sq,
    `QuaternaryQuadraticForms.primeQuadraticGauss_fourth,
    `QuaternaryQuadraticForms.primeQuadraticGauss_inversion,
    `QuaternaryQuadraticForms.primeQuadraticGauss_units_inversion,
    `QuaternaryQuadraticForms.primeQuadraticGauss_units_div_inversion,
    `QuaternaryQuadraticForms.primeQuadraticExponentialSum_zero,
    `QuaternaryQuadraticForms.primeQuadraticExponentialSum_unshifted,
    `QuaternaryQuadraticForms.primeQuadraticExponentialSum_of_ne_zero,
    `QuaternaryQuadraticForms.primeRamanujan_eq,
    `QuaternaryQuadraticForms.primeRamanujan_mul,
    `QuaternaryQuadraticForms.primeRamanujan_inverse_sum,
    `QuaternaryQuadraticForms.primeRamanujan_reciprocal_phase,
    `QuaternaryQuadraticForms.scaledChineseRemainder_fst,
    `QuaternaryQuadraticForms.scaledChineseRemainder_snd,
    `QuaternaryQuadraticForms.scaledChineseRemainder_intCast,
    `QuaternaryQuadraticForms.scaledChineseRemainder_apply,
    `QuaternaryQuadraticForms.scaledChineseRemainderUnits_coe,
    `QuaternaryQuadraticForms.scaledChineseRemainderUnits_apply,
    `QuaternaryQuadraticForms.scaledChineseRemainderVector_apply,
    `QuaternaryQuadraticForms.stdAddChar_scaledChineseRemainder,
    `QuaternaryQuadraticForms.stdAddChar_mul_modulus,
    `QuaternaryQuadraticForms.stdAddChar_crt_split,
    `QuaternaryQuadraticForms.stdAddChar_modulus_one,
    `QuaternaryQuadraticForms.residueLift_cast,
    `QuaternaryQuadraticForms.integralQuadraticValue_eq_eval,
    `QuaternaryQuadraticForms.matrixQuadraticValue_map,
    `QuaternaryQuadraticForms.matrixQuadraticValue_mul,
    `QuaternaryQuadraticForms.integralQuadraticValue_mul,
    `QuaternaryQuadraticForms.integralQuadraticValue_congr_mod,
    `QuaternaryQuadraticForms.integralQuadraticValue_dvd_congr,
    `QuaternaryQuadraticForms.dotProduct_intCast,
    `QuaternaryQuadraticForms.dotProduct_congr_mod,
    `QuaternaryQuadraticForms.mixedIntegerSummand_crt,
    `QuaternaryQuadraticForms.mixedCompleteSum_crt,
    `QuaternaryQuadraticForms.unweightedCompleteSum_mul,
    `QuaternaryQuadraticForms.constrainedFourierSum_mul,
    `QuaternaryQuadraticForms.constrainedFourierSum_primeFactors,
    `QuaternaryQuadraticForms.mixedIntegerSummand_inverse_scale,
    `QuaternaryQuadraticForms.mixedCompleteSum_isUnit_frequency,
    `QuaternaryQuadraticForms.mixedCompleteSum_unit_frequency,
    `QuaternaryQuadraticForms.mixedCompleteSum_one_left,
    `QuaternaryQuadraticForms.mixedCompleteSum_one_right,
    `QuaternaryQuadraticForms.unweightedCompleteSum_one,
    `QuaternaryQuadraticForms.constrainedFourierSum_one,
    `QuaternaryQuadraticForms.mixedCompleteSum_one_one,
    `QuaternaryQuadraticForms.constrainedFourierSum_prime,
    `QuaternaryQuadraticForms.constrainedFourierSum_eq_integralFourierSum,
    `QuaternaryQuadraticForms.constrainedFourierSum_polynomial_character,
    `QuaternaryQuadraticForms.complete_sum_crt,
    `QuaternaryQuadraticForms.source_mixedCompleteSum_crt,
    `QuaternaryQuadraticForms.source_mixedCompleteSum_unit_frequency,
    `QuaternaryQuadraticForms.source_complete_sum_crt,
    `QuaternaryQuadraticForms.mixedIntegerSummand_a_congr,
    `QuaternaryQuadraticForms.mixedIntegerSummand_x_congr,
    `QuaternaryQuadraticForms.mixedIntegerSummand_congr,
    `QuaternaryQuadraticForms.compositeWeight_one,
    `QuaternaryQuadraticForms.compositeWeight_prime,
    `QuaternaryQuadraticForms.compositeWeight_congr,
    `QuaternaryQuadraticForms.compositeWeight_congr_of_dvd_sub,
    `QuaternaryQuadraticForms.compositeWeight_add_modulus,
    `QuaternaryQuadraticForms.compositeWeight_congr_mod,
    `QuaternaryQuadraticForms.compositeWeight_mul,
    `QuaternaryQuadraticForms.compositeWeight_smul_of_nonzero,
    `QuaternaryQuadraticForms.compositeWeight_smul,
    `QuaternaryQuadraticForms.compositeWeight_smul_of_isUnit,
    `QuaternaryQuadraticForms.compositeWeight_mod_one,
    `QuaternaryQuadraticForms.compositeWeight_mod_eq_of_lift,
    `QuaternaryQuadraticForms.compositeWeight_mod_intCast,
    `QuaternaryQuadraticForms.compositeWeight_mod_prime,
    `QuaternaryQuadraticForms.compositeWeight_mod_cast,
    `QuaternaryQuadraticForms.compositeWeight_mod_units_smul,
    `QuaternaryQuadraticForms.mixedPhase_intCast_lift_independent,
    `QuaternaryQuadraticForms.mixedPhase_lift_independent,
    `QuaternaryQuadraticForms.mixedPhase_crt_intCast,
    `QuaternaryQuadraticForms.mixedPhase_crt,
    `QuaternaryQuadraticForms.extendPrimeWeights_apply,
    `QuaternaryQuadraticForms.primeWeightsInvariant_extend,
    `QuaternaryQuadraticForms.compositeWeight_extend,
    `QuaternaryQuadraticForms.quadraticGaussSum_reciprocal_phase_sum,
    `QuaternaryQuadraticForms.sum_quadraticGaussSum_of_constant,
    `QuaternaryQuadraticForms.unweightedCompleteSum_of_constant_gauss,
    `QuaternaryQuadraticForms.quadraticGaussSum_prime_zero_frequency,
    `QuaternaryQuadraticForms.quadraticGaussSum_prime_all_scalars,
    `QuaternaryQuadraticForms.adjugateQuadraticValue_intCast,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_shift,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_shift_prime_power,
    `QuaternaryQuadraticForms.integralQuadraticValue_residueLift,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_eq_lift_sum,
    `QuaternaryQuadraticForms.quadraticGaussSum_zero,
    `QuaternaryQuadraticForms.quadraticGaussSum_modulus_one,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_modulus_one,
    `QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_quadraticGaussSum,
    `QuaternaryQuadraticForms.matrix_quadratic_square_completion,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power_pure,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power,
    `QuaternaryQuadraticForms.quadraticGaussSum_prime_power_units_pure,
    `QuaternaryQuadraticForms.stdAddChar_vector_orthogonality,
    `QuaternaryQuadraticForms.matrix_bilinear_character_sum,
    `QuaternaryQuadraticForms.primeSquare_digit_phase_intCast,
    `QuaternaryQuadraticForms.primeSquare_digit_phase,
    `QuaternaryQuadraticForms.primeSquare_digit_orthogonality,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_primeSquare_mul,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_primePower_recurrence,
    `QuaternaryQuadraticForms.prime_power_gauss,
    `QuaternaryQuadraticForms.residueDigitsEquiv_val,
    `QuaternaryQuadraticForms.residueDigitsEquiv_apply,
    `QuaternaryQuadraticForms.residueDigitsVectorEquiv_apply,
    `QuaternaryQuadraticForms.sum_residueLift_digits,
    `QuaternaryQuadraticForms.sum_residueLift_three_digits,
    `QuaternaryQuadraticForms.intCast_isUnit_prime_pow,
    `QuaternaryQuadraticForms.goodPrime_not_dvd_det,
    `QuaternaryQuadraticForms.goodPrime_two_isUnit_prime_pow,
    `QuaternaryQuadraticForms.goodPrime_det_isUnit_prime_pow,
    `QuaternaryQuadraticForms.quadraticGaussSum_shift_of_inverse,
    `QuaternaryQuadraticForms.quadraticGaussSum_shift,
    `QuaternaryQuadraticForms.quadraticGaussSum_shift_of_units,
    `QuaternaryQuadraticForms.affineQuadric_card_additive,
    `QuaternaryQuadraticForms.affineQuadric_card_projective,
    `QuaternaryQuadraticForms.affineQuadric_card_complex,
    `QuaternaryQuadraticForms.affineQuadric_card,
    `QuaternaryQuadraticForms.projectiveQuadric_card_complex,
    `QuaternaryQuadraticForms.projectiveQuadric_card,
    `QuaternaryQuadraticForms.integral_projectiveQuadric_card,
    `QuaternaryQuadraticForms.integralRamanujanSum_eq_lift_sum,
    `QuaternaryQuadraticForms.residueRamanujanSum_prime,
    `QuaternaryQuadraticForms.residueRamanujanSum_modulus_one,
    `QuaternaryQuadraticForms.integralRamanujanSum_modulus_one,
    `QuaternaryQuadraticForms.residueRamanujanSum_units_mul,
    `QuaternaryQuadraticForms.residueRamanujanSum_mul,
    `QuaternaryQuadraticForms.residueRamanujanSum_inverse_sum,
    `QuaternaryQuadraticForms.residueRamanujanSum_reciprocal_phase,
    `QuaternaryQuadraticForms.unweightedCompleteSum_prime_power,
    `QuaternaryQuadraticForms.stdAddChar_residue_vector_orthogonality,
    `QuaternaryQuadraticForms.quadraticGaussSum_mul_conj_eq_kernel_sum,
    `QuaternaryQuadraticForms.quadraticGaussSum_norm_sq_le_kernel_card,
    `QuaternaryQuadraticForms.mem_matrixResidueKernel,
    `QuaternaryQuadraticForms.matrixResidueKernel_card_le_det,
    `QuaternaryQuadraticForms.quaternary_det_two_smul,
    `QuaternaryQuadraticForms.quaternary_det_two_smul_natAbs,
    `QuaternaryQuadraticForms.gauss_norm_le_of_sq_le,
    `QuaternaryQuadraticForms.zmod_card_units_le,
    `QuaternaryQuadraticForms.reduceQuadraticMatrix_two_smul,
    `QuaternaryQuadraticForms.matrixResidueKernel_two_smul,
    `QuaternaryQuadraticForms.unweightedCompleteSum_norm_le_of_gauss_bound,
    `QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_sq_le,
    `QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_le,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_norm_le,
    `QuaternaryQuadraticForms.unweightedCompleteSum_norm_le,
    `QuaternaryQuadraticForms.bad_prime_bound,
    `QuaternaryQuadraticForms.residueUnitDigitsEquiv_val,
    `QuaternaryQuadraticForms.sum_units_residueLift_digits,
    `QuaternaryQuadraticForms.ramified_complete_sum,
    `QuaternaryQuadraticForms.source_ramified_complete_sum,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_lift,
    `QuaternaryQuadraticForms.source_not_dvd_quadraticBadPrimeModulus,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_of_gauss_factor,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_factor,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power,
    `QuaternaryQuadraticForms.stationary_weight_eq_adjugate,
    `QuaternaryQuadraticForms.weightedIntegralGaussSum_mul_extract,
    `QuaternaryQuadraticForms.weightedIntegralGaussSum_prime_power_extract,
    `QuaternaryQuadraticForms.weightedGauss_digit_phase,
    `QuaternaryQuadraticForms.weightedIntegralGaussSum_stationary_expansion,
    `QuaternaryQuadraticForms.weightedIntegralGaussSum_one,
    `QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_integralQuadraticGaussSum,
    `QuaternaryQuadraticForms.primeWeightedCompleteSum_one,
    `QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_dual_cone,
    `QuaternaryQuadraticForms.mixedCompleteSum_dual_cone,
    `QuaternaryQuadraticForms.globalQuadraticChar_one,
    `QuaternaryQuadraticForms.globalQuadraticChar_mul,
    `QuaternaryQuadraticForms.globalQuadraticChar_prime,
    `QuaternaryQuadraticForms.globalQuadraticChar_prime_power,
    `QuaternaryQuadraticForms.globalQuadraticChar_sq,
    `QuaternaryQuadraticForms.monoidHom_eq_globalQuadraticChar,
    `QuaternaryQuadraticForms.globalQuadraticChar_eq_dirichletCharacter,
    `QuaternaryQuadraticForms.mixedCompleteSum_good_modulus,
    `QuaternaryQuadraticForms.source_mixedCompleteSum_good_modulus,
    `QuaternaryQuadraticForms.source_mixedCompleteSum_dual_cone,
    `QuaternaryQuadraticForms.source_good_global_complete_sum,
    `QuaternaryQuadraticForms.unweightedCompleteSum_good_modulus,
    `QuaternaryQuadraticForms.exists_modulus_prime_split,
    `QuaternaryQuadraticForms.coprime_of_prime_dvd_support,
    `QuaternaryQuadraticForms.gcd_eq_good_part_of_prime_support,
    `QuaternaryQuadraticForms.integralRamanujanSum_mul,
    `QuaternaryQuadraticForms.integralRamanujanSum_zero,
    `QuaternaryQuadraticForms.totient_mul_of_dvd,
    `QuaternaryQuadraticForms.mixedCompleteSum_shared_support,
    `QuaternaryQuadraticForms.compositeWeight_extend_eq_source,
    `QuaternaryQuadraticForms.source_coprime_quadraticBadPrimeModulus,
    `QuaternaryQuadraticForms.squarefree_gcd_factors,
    `QuaternaryQuadraticForms.gcd_mul_blocks_coprime,
    `QuaternaryQuadraticForms.squarefree_shared_gcd_factors,
    `QuaternaryQuadraticForms.squarefree_dvd_prime_pow_eq_one_or_prime,
    `QuaternaryQuadraticForms.divisors_card_le_rpow,
    `QuaternaryQuadraticForms.sum_le_product_of_factorization,
    `QuaternaryQuadraticForms.sum_divisor_multiples_div_le_harmonic,
    `QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_harmonic,
    `QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_log,
    `QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_not_dvd,
    `QuaternaryQuadraticForms.modulusNormSum_le_divisor_log,
    `QuaternaryQuadraticForms.modulusNormSum_le_rpow,
    `QuaternaryQuadraticForms.source_generic_modulus_bound,
    `QuaternaryQuadraticForms.one_add_log_pow_le_rpow,
    `QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd,
    `QuaternaryQuadraticForms.mixedCompleteSum_eq_zero_of_gcd_not_dvd,
    `QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_of_prime_split,
    `QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_indicator_of_prime_split,
    `QuaternaryQuadraticForms.globalQuadraticChar_norm_le,
    `QuaternaryQuadraticForms.compositeWeight_norm_le,
    `QuaternaryQuadraticForms.primeWeightsNorm_le_extend,
    `QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_norm_le,
    `QuaternaryQuadraticForms.mixedCompleteSum_eq_bad_mul_good,
    `QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_of_prime_split,
    `QuaternaryQuadraticForms.mem_gcdModuliUpTo,
    `QuaternaryQuadraticForms.normalizedMixedCompleteSum_of_neZero,
    `QuaternaryQuadraticForms.normalizedMixedCompleteSum_nonneg,
    `QuaternaryQuadraticForms.modulusNormSum_nonneg,
    `QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_vanishing,
    `QuaternaryQuadraticForms.mem_primeSupportModuliUpTo,
    `QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le,
    `QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log,
    `QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log_normalized,
    `QuaternaryQuadraticForms.integralRamanujanSum_prime_power_norm_le_gcd,
    `QuaternaryQuadraticForms.integralRamanujanSum_norm_le_gcd,
    `QuaternaryQuadraticForms.integralRamanujanSum_mul_norm_le,
    `QuaternaryQuadraticForms.integralRamanujanSum_eq_zero_of_prime_sq_dvd,
    `QuaternaryQuadraticForms.integralRamanujanSum_shared_eq_zero,
    `QuaternaryQuadraticForms.integralRamanujanSum_shared_norm_le,
    `QuaternaryQuadraticForms.integralRamanujanSum_prime_eq,
    `QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_eq_zero,
    `QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_mul,
    `QuaternaryQuadraticForms.integralRamanujanSum_prime_power_eq,
    `QuaternaryQuadraticForms.periodic_cubic_sum_norm_le,
    `QuaternaryQuadraticForms.periodic_cubic_sum_floor_norm_le,
    `QuaternaryQuadraticForms.good_modulus_sum_norm_le_harmonic,
    `QuaternaryQuadraticForms.unweightedModulusSum_le_divisor_log,
    `QuaternaryQuadraticForms.unweightedCompleteSum_on_dual_cone,
    `QuaternaryQuadraticForms.good_modulus_sum_eq_quadratic_totient,
    `QuaternaryQuadraticForms.unweightedModulusSum_le_rpow,
    `QuaternaryQuadraticForms.source_cone_modulus_bound,
    `QuaternaryQuadraticForms.sum_gcd_totient_eq_moebius,
    `QuaternaryQuadraticForms.sum_Icc_dvd_eq_sum_div,
    `QuaternaryQuadraticForms.coprime_indicator_eq_moebius_sum,
    `QuaternaryQuadraticForms.sum_coprime_eq_sum_moebius_multiples,
    `QuaternaryQuadraticForms.moebius_complex_norm_le_one,
    `QuaternaryQuadraticForms.coprime_cubic_sum_norm_le,
    `QuaternaryQuadraticForms.sum_Icc_divisors_eq_sum_mul,
    `QuaternaryQuadraticForms.sum_gcdModuliUpTo_eq_sum_coprime,
    `QuaternaryQuadraticForms.sum_coprime_divisors_eq_sum_mul,
    `QuaternaryQuadraticForms.modulus_prime_split_unique,
    `QuaternaryQuadraticForms.sum_gcdModuli_eq_sum_prime_split,
    `QuaternaryQuadraticForms.unweightedCompleteSumValue_of_neZero,
    `QuaternaryQuadraticForms.unweightedModulusSum_prime_split,
    `QuaternaryQuadraticForms.periodic_sum_range_norm_le,
    `QuaternaryQuadraticForms.exists_good_jacobiSym_neg_one,
    `QuaternaryQuadraticForms.goodQuadraticDirichletChar_ne_one,
    `QuaternaryQuadraticForms.goodQuadraticChar_sum_period_eq_zero,
    `QuaternaryQuadraticForms.goodQuadraticChar_one,
    `QuaternaryQuadraticForms.goodQuadraticChar_zero,
    `QuaternaryQuadraticForms.goodQuadraticChar_of_coprime,
    `QuaternaryQuadraticForms.goodQuadraticChar_of_not_coprime,
    `QuaternaryQuadraticForms.goodQuadraticChar_mul,
    `QuaternaryQuadraticForms.goodQuadraticChar_norm_le_one,
    `QuaternaryQuadraticForms.goodQuadraticChar_coprime_four_iff,
    `QuaternaryQuadraticForms.goodQuadraticChar_mod,
    `QuaternaryQuadraticForms.goodQuadraticChar_periodic,
    `QuaternaryQuadraticForms.goodQuadraticDirichletChar_natCast,
    `QuaternaryQuadraticForms.exists_jacobiSym_neg_one_mod_eight_of_squarefree,
    `QuaternaryQuadraticForms.sum_gcd_totient_norm_le_harmonic,
    `QuaternaryQuadraticForms.sum_gcd_totient_floor_norm_le_log,
    `QuaternaryQuadraticForms.totient_eq_sum_moebius,
    `QuaternaryQuadraticForms.totient_mul_eq_sum_moebius,
    `QuaternaryQuadraticForms.localQuadraticDensity_eq_tsum_re,
    `QuaternaryQuadraticForms.tendsto_normalizedPrimePowerZeroCount,
    `QuaternaryQuadraticForms.hasSum_localDensityTerm,
    `QuaternaryQuadraticForms.localQuadraticDensity_nonneg,
    `QuaternaryQuadraticForms.primePowerZeroCount_additive,
    `QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_fullGauss,
    `QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_recurrence,
    `QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_zero,
    `QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_sum,
    `QuaternaryQuadraticForms.localQuadraticDensity_goodPrime,
    `QuaternaryQuadraticForms.source_localQuadraticDensity_goodPrime,
    `QuaternaryQuadraticForms.correctedLocalDensityFactor_goodPrime,
    `QuaternaryQuadraticForms.correctedLocalDensityFactor_sub_one_norm_le,
    `QuaternaryQuadraticForms.eventually_prime_not_dvd_quadraticBadPrimeModulus,
    `QuaternaryQuadraticForms.summable_norm_correctedLocalDensityFactor_sub_one,
    `QuaternaryQuadraticForms.multipliable_correctedLocalDensityFactor,
    `QuaternaryQuadraticForms.multipliable_norm_correctedLocalDensityFactor,
    `QuaternaryQuadraticForms.integralQuadraticGaussSum_scaled_modulus,
    `QuaternaryQuadraticForms.primePower_fullGauss_recurrence,
    `QuaternaryQuadraticForms.localDensityTerm_zero,
    `QuaternaryQuadraticForms.legendreSym_complex_norm_le_one,
    `QuaternaryQuadraticForms.localDensity_goodPrime_ratio_norm_lt_one,
    `QuaternaryQuadraticForms.localDensityTerm_goodPrime_succ,
    `QuaternaryQuadraticForms.localDensityTerm_hasSum_goodPrime,
    `QuaternaryQuadraticForms.localDensityTerm_norm_le,
    `QuaternaryQuadraticForms.summable_norm_localDensityTerm,
    `QuaternaryQuadraticForms.summable_localDensityTerm,
    `QuaternaryQuadraticForms.local_density,
    `QuaternaryQuadraticForms.source_local_density,
    `QuaternaryQuadraticForms.sum_primePower_scalars,
    `QuaternaryQuadraticForms.orderedCoeffSum_eq_Icc_one,
    `QuaternaryQuadraticForms.orderedDirichletPartial_four,
    `QuaternaryQuadraticForms.norm_orderedDirichlet_integrand_le,
    `QuaternaryQuadraticForms.orderedDirichlet_integrable,
    `QuaternaryQuadraticForms.orderedDirichlet_integral_norm_le,
    `QuaternaryQuadraticForms.tendsto_orderedDirichletPartial,
    `QuaternaryQuadraticForms.orderedDirichletPartial_eq_boundary_add_integral,
    `QuaternaryQuadraticForms.orderedDirichletValue_sub_partial,
    `QuaternaryQuadraticForms.norm_orderedDirichletValue_sub_partial_le,
    `QuaternaryQuadraticForms.continuousWithinAt_orderedDirichletValue_four,
    `QuaternaryQuadraticForms.shiftedLocalDensity_damping_norm_le_one,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_norm_le,
    `QuaternaryQuadraticForms.summable_norm_shiftedLocalDensityTerm,
    `QuaternaryQuadraticForms.summable_shiftedLocalDensityTerm,
    `QuaternaryQuadraticForms.continuous_shiftedLocalDensityTerm,
    `QuaternaryQuadraticForms.continuousOn_shiftedLocalDensity,
    `QuaternaryQuadraticForms.shiftedLocalDensity_zero,
    `QuaternaryQuadraticForms.tendsto_shiftedLocalDensity_zero,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_exponent,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_shift,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_eq_primePower,
    `QuaternaryQuadraticForms.div_natCast_rpow_nat_add,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ratio_norm_lt_one,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_div_norm_lt_one,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_den_ne_zero,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_goodPrime_succ,
    `QuaternaryQuadraticForms.shiftedLocalDensityTerm_hasSum_goodPrime,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_num_ne_zero,
    `QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ne_zero,
    `QuaternaryQuadraticForms.source_shiftedLocalDensity_goodPrime,
    `QuaternaryQuadraticForms.coprimeCompleteSumValue_one,
    `QuaternaryQuadraticForms.coprimeCompleteSumValue_mul,
    `QuaternaryQuadraticForms.coprimeCompleteSumValue_norm_le,
    `QuaternaryQuadraticForms.singularSeriesTerm_one,
    `QuaternaryQuadraticForms.singularSeriesTerm_mul,
    `QuaternaryQuadraticForms.singularSeriesTerm_norm_le,
    `QuaternaryQuadraticForms.summable_norm_singularSeriesTerm,
    `QuaternaryQuadraticForms.summable_singularSeriesTerm,
    `QuaternaryQuadraticForms.singularSeriesTerm_eulerProduct_hasProd,
    `QuaternaryQuadraticForms.singularSeriesPartialSum_eq_sum_range,
    `QuaternaryQuadraticForms.singularSeriesPartialSum_sub_eq_sum_Ioc,
    `QuaternaryQuadraticForms.mem_singularSeries_tail_interval,
    `QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_tsum,
    `QuaternaryQuadraticForms.singularSeriesValue_eq_tsum,
    `QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_not_dvd,
    `QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_dvd,
    `QuaternaryQuadraticForms.tsum_singularSeriesTerm_primePower,
    `QuaternaryQuadraticForms.singularSeries_eulerProduct_hasProd,
    `QuaternaryQuadraticForms.singularSeriesEulerCorrection_zero,
    `QuaternaryQuadraticForms.singularSeriesValue_zero_eq,
    `QuaternaryQuadraticForms.correctedLocalDensityFactor_eq_dirichletRealEulerFactor,
    `QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_ne_zero,
    `QuaternaryQuadraticForms.hasProd_removedCorrectedLocalDensityFactor,
    `QuaternaryQuadraticForms.singularSeriesPartialSum_eq_orderedDirichletPartial,
    `QuaternaryQuadraticForms.exists_coprimeCompleteSumValue_bound,
    `QuaternaryQuadraticForms.singularSeriesValue_eq_orderedDirichletValue_of_bound,
    `QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum,
    `QuaternaryQuadraticForms.continuousWithinAt_singularSeriesValue_zero,
    `QuaternaryQuadraticForms.singularSeries_uniform_tail,
    `QuaternaryQuadraticForms.coprimeCompleteSumValue_zero,
    `QuaternaryQuadraticForms.singularSeriesTerm_zero,
    `QuaternaryQuadraticForms.sum_coprimeCompleteSumValue,
    `QuaternaryQuadraticForms.singularSeriesTerm_at_zero,
    `QuaternaryQuadraticForms.restrictedCorrectedShiftedFactor_goodPrime,
    `QuaternaryQuadraticForms.hasProd_restrictedCorrectedShiftedFactor,
    `QuaternaryQuadraticForms.tsum_singularSeriesTerm_eq_LFunction_mul_correction,
    `QuaternaryQuadraticForms.continuousWithinAt_singularSeriesEulerCorrection_zero,
    `QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_cpow,
    `QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_div,
    `QuaternaryQuadraticForms.dirichletRealEulerFactor_ne_zero,
    `QuaternaryQuadraticForms.continuous_dirichletRealEulerFactor,
    `QuaternaryQuadraticForms.hasProd_inv_dirichletRealEulerFactor,
    `QuaternaryQuadraticForms.LFunction_real_ne_zero,
    `QuaternaryQuadraticForms.hasProd_dirichletRealEulerFactor,
    `QuaternaryQuadraticForms.mem_singularSeriesPrimeDivisors,
    `QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_zero,
    `QuaternaryQuadraticForms.tendsto_singularSeriesTail_zero,
    `QuaternaryQuadraticForms.tendsto_singularSeriesTail_Ioc,
    `QuaternaryQuadraticForms.source_singular_series,
    `QuaternaryQuadraticForms.sourceDirichletCharacter_exists_neg_one,
    `QuaternaryQuadraticForms.sourceDirichletCharacter_ne_one,
    `QuaternaryQuadraticForms.polynomialBoxConstant_zero,
    `QuaternaryQuadraticForms.polynomialBoxConstant_succ,
    `QuaternaryQuadraticForms.polynomialBoxConstant_one,
    `QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_range,
    `QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_Icc,
    `QuaternaryQuadraticForms.polynomialBoxConstant_pos,
    `QuaternaryQuadraticForms.polynomialBox_pow_add_one_le,
    `QuaternaryQuadraticForms.sum_polynomialBox_bad_product_eq,
    `QuaternaryQuadraticForms.polynomialBox_subset_ratio_sum_le,
    `QuaternaryQuadraticForms.polynomialBox_subset_weight_sum_le,
    `QuaternaryQuadraticForms.sum_polynomialBox_bad_product_le,
    `QuaternaryQuadraticForms.polynomialBox_count_step,
    `QuaternaryQuadraticForms.mem_integerPolynomialBox,
    `QuaternaryQuadraticForms.mem_polynomialBoxSolutions,
    `QuaternaryQuadraticForms.integerPolynomialBox_card,
    `QuaternaryQuadraticForms.integerPolynomialBox_card_le,
    `QuaternaryQuadraticForms.polynomialBoxSolutions_empty,
    `QuaternaryQuadraticForms.polynomialBoxSolutions_card_le_box,
    `QuaternaryQuadraticForms.cons_mem_integerPolynomialBox,
    `QuaternaryQuadraticForms.integerPolynomialBox_zero,
    `QuaternaryQuadraticForms.integerPolynomialBox_filter_card_succ,
    `QuaternaryQuadraticForms.polynomialBoxSolutions_card_succ,
    `QuaternaryQuadraticForms.polynomialBoxBadPrimes_subset,
    `QuaternaryQuadraticForms.polynomialIntervalZeros_sdiff_bad,
    `QuaternaryQuadraticForms.polynomialBox_fiber_card_le,
    `QuaternaryQuadraticForms.polynomialBox_primeSet_card_le,
    `QuaternaryQuadraticForms.integerInterval_eq_Icc,
    `QuaternaryQuadraticForms.realInterval_integer_points_ordConnected,
    `QuaternaryQuadraticForms.realInterval_integer_points_eq_Icc,
    `QuaternaryQuadraticForms.realInterval_integer_membership_Icc,
    `QuaternaryQuadraticForms.mem_polynomialIntervalZeros,
    `QuaternaryQuadraticForms.polynomialIntervalZeros_card_le,
    `QuaternaryQuadraticForms.mem_primeResidueInterval,
    `QuaternaryQuadraticForms.primeProduct_modEq,
    `QuaternaryQuadraticForms.primeResidueInterval_card_le_blocks,
    `QuaternaryQuadraticForms.primeResidueInterval_card_le,
    `QuaternaryQuadraticForms.polynomialBoxSlice_eval,
    `QuaternaryQuadraticForms.polynomialBoxSlice_coeff,
    `QuaternaryQuadraticForms.polynomialBoxSlice_eq_zero_iff,
    `QuaternaryQuadraticForms.polynomialBoxSlice_natDegree_le,
    `QuaternaryQuadraticForms.polynomialBoxCoefficient_totalDegree_le,
    `QuaternaryQuadraticForms.exists_polynomialBoxCoefficient_ne_zero,
    `QuaternaryQuadraticForms.exists_polynomialBox_degeneracy_polynomial,
    `QuaternaryQuadraticForms.polynomialBoxSlice_empty_ne_zero,
    `QuaternaryQuadraticForms.polynomialBox_primeFactors_card_eq_omega,
    `QuaternaryQuadraticForms.polynomialBox_squarefree_card_le,
    `QuaternaryQuadraticForms.extendPolynomialBoxFamily_apply,
    `QuaternaryQuadraticForms.sourcePolynomialBoxSet_eq_integer,
    `QuaternaryQuadraticForms.source_polynomial_box,
    `QuaternaryQuadraticForms.congruenceEuclideanBall_subset_polynomialBox,
    `QuaternaryQuadraticForms.congruenceEuclideanBall_card_le_rpow,
    `QuaternaryQuadraticForms.exceptionalIndicator_eq_ite,
    `QuaternaryQuadraticForms.exceptionalIndicator_eq_one_iff,
    `QuaternaryQuadraticForms.exceptionalIndicator_eq_zero_of_ne_one,
    `QuaternaryQuadraticForms.exceptionalIndicator_one,
    `QuaternaryQuadraticForms.mem_congruenceEuclideanBall,
    `QuaternaryQuadraticForms.mem_divisibleEuclideanBall,
    `QuaternaryQuadraticForms.weightedCongruenceEuclideanSum_eq,
    `QuaternaryQuadraticForms.boxCongruencePolynomial_ne_zero,
    `QuaternaryQuadraticForms.boxCongruencePolynomial_totalDegree_le,
    `QuaternaryQuadraticForms.squarefree_int_dvd_iff_primeFactors,
    `QuaternaryQuadraticForms.boxCongruencePolynomial_eval_eq_zero_iff,
    `QuaternaryQuadraticForms.congruenceBox_bounds,
    `QuaternaryQuadraticForms.integerEuclideanNorm_eq_sqrt,
    `QuaternaryQuadraticForms.integerEuclideanNorm_nonneg,
    `QuaternaryQuadraticForms.coordinate_abs_le_integerEuclideanNorm,
    `QuaternaryQuadraticForms.integerEuclideanNorm_eq_zero_iff,
    `QuaternaryQuadraticForms.one_le_integerEuclideanNorm,
    `QuaternaryQuadraticForms.integerEuclideanNorm_pos_iff,
    `QuaternaryQuadraticForms.integerEuclideanNorm_le_mem_box,
    `QuaternaryQuadraticForms.mem_integerEuclideanBall,
    `QuaternaryQuadraticForms.integerEuclideanBall_mono,
    `QuaternaryQuadraticForms.integerEuclideanInterval_card_le_three_mul,
    `QuaternaryQuadraticForms.inverseRadiusSum_le_of_sublevel_card,
    `QuaternaryQuadraticForms.polynomialBox_squarefree_card_le_rpow,
    `QuaternaryQuadraticForms.source_polynomial_box_epsilon,
    `QuaternaryQuadraticForms.primeFactor_pow_le_rpow,
    `QuaternaryQuadraticForms.sourceCongruenceEuclideanSet_eq,
    `QuaternaryQuadraticForms.sourceWeightedCongruenceEuclideanSum_eq,
    `QuaternaryQuadraticForms.source_congruence_box_natDegree,
    `QuaternaryQuadraticForms.source_congruence_box,
    `QuaternaryQuadraticForms.extendExceptionalPolynomials_apply,
    `QuaternaryQuadraticForms.extendExceptionalPolynomials_ne_zero,
    `QuaternaryQuadraticForms.extendExceptionalPolynomials_totalDegree_le,
    `QuaternaryQuadraticForms.exceptionalIndicator_extend,
    `QuaternaryQuadraticForms.sourceExceptionalIndicator_one,
    `QuaternaryQuadraticForms.squarefree_divisor_sum_eq_powerset,
    `QuaternaryQuadraticForms.exceptional_prime_product_eq_divisor_sum,
    `QuaternaryQuadraticForms.fourier_stratified_product_eq,
    `QuaternaryQuadraticForms.constrainedFourierSum_norm_le_divisors,
    `QuaternaryQuadraticForms.divisor_halfPower_shape_le,
    `QuaternaryQuadraticForms.exceptional_divisor_sum_le,
    `QuaternaryQuadraticForms.weightedSum_le_exceptional_divisors,
    `QuaternaryQuadraticForms.averageFrequency_bound,
    `QuaternaryQuadraticForms.constrainedFourierSum_extend_eq_source,
    `QuaternaryQuadraticForms.sourceConstrainedFourierSum_prime,
    `QuaternaryQuadraticForms.sourceConstrainedFourierSum_one,
    `QuaternaryQuadraticForms.sourceConstrainedFourierSum_primeFactors,
    `QuaternaryQuadraticForms.source_average_frequency_natDegree,
    `QuaternaryQuadraticForms.source_average_frequency_bound,
    `QuaternaryQuadraticForms.bumpSamplingSum_finite_support,
    `QuaternaryQuadraticForms.bumpSamplingSum_summable,
    `QuaternaryQuadraticForms.bumpSamplingSum_uniform_pos,
    `QuaternaryQuadraticForms.bumpNormalization_error_bound,
    `QuaternaryQuadraticForms.deltaSymbolTerm_eq_unit_sum,
    `QuaternaryQuadraticForms.deltaSymbolTerm_eq_exponential_sum,
    `QuaternaryQuadraticForms.deltaSymbolTerm_modulus_one,
    `QuaternaryQuadraticForms.deltaSymbolKernel_eq_zero_of_modulus_bound,
    `QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_modulus_bound,
    `QuaternaryQuadraticForms.deltaSymbol_modulus_bound_eq_max,
    `QuaternaryQuadraticForms.mem_deltaSymbolModuli,
    `QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_not_mem,
    `QuaternaryQuadraticForms.deltaSymbolTerm_finite_support,
    `QuaternaryQuadraticForms.deltaSymbolTerm_summable,
    `QuaternaryQuadraticForms.deltaSymbolTerm_norm_summable,
    `QuaternaryQuadraticForms.deltaSymbolTerm_hasSum,
    `QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum,
    `QuaternaryQuadraticForms.deltaSymbolModuli_sum_eq_sum_range,
    `QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum_range,
    `QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_unit_sum,
    `QuaternaryQuadraticForms.heathBrownDeltaKernel_properties,
    `QuaternaryQuadraticForms.heathBrownSamplingSum_uniform_pos,
    `QuaternaryQuadraticForms.heathBrownSamplingSum_pos,
    `QuaternaryQuadraticForms.heathBrownNormalization_pos,
    `QuaternaryQuadraticForms.heathBrownNormalization_error_bound,
    `QuaternaryQuadraticForms.heathBrownNormalization_error_bound_real,
    `QuaternaryQuadraticForms.heathBrown_delta_identity,
    `QuaternaryQuadraticForms.heathBrown_delta_finite_identity,
    `QuaternaryQuadraticForms.source_delta_symbol,
    `QuaternaryQuadraticForms.heathBrownBaseBump_eq_expNegInvGlue,
    `QuaternaryQuadraticForms.heathBrownBaseBump_contDiff,
    `QuaternaryQuadraticForms.heathBrownBaseBump_nonneg,
    `QuaternaryQuadraticForms.heathBrownBaseBump_ne_zero_iff,
    `QuaternaryQuadraticForms.heathBrownBaseBump_hasCompactSupport,
    `QuaternaryQuadraticForms.heathBrownBaseBump_integrable,
    `QuaternaryQuadraticForms.heathBrownBumpMass_pos,
    `QuaternaryQuadraticForms.heathBrownTheta_nonneg,
    `QuaternaryQuadraticForms.heathBrownTheta_contDiff,
    `QuaternaryQuadraticForms.heathBrownTheta_coordinates_lt_one,
    `QuaternaryQuadraticForms.heathBrownTheta_tsupport_subset_cube,
    `QuaternaryQuadraticForms.heathBrownTheta_norm_le_two_of_mem_tsupport,
    `QuaternaryQuadraticForms.heathBrownTheta_hasCompactSupport,
    `QuaternaryQuadraticForms.heathBrownTheta_integrable,
    `QuaternaryQuadraticForms.heathBrownTheta_integral,
    `QuaternaryQuadraticForms.UniformCoordinateDerivatives.uniformWeightDerivatives,
    `QuaternaryQuadraticForms.UniformWeightDerivatives.uniformCoordinateDerivatives,
    `QuaternaryQuadraticForms.uniformCoordinateDerivatives_iff_uniformWeightDerivatives,
    `QuaternaryQuadraticForms.heathBrownTheta_uniform_translate_derivatives,
    `QuaternaryQuadraticForms.UniformWeightDerivatives.localizedWeight,
    `QuaternaryQuadraticForms.UniformCoordinateDerivatives.localizedWeight,
    `QuaternaryQuadraticForms.UniformWeightDerivatives.comp_realIsometry,
    `QuaternaryQuadraticForms.UniformCoordinateDerivatives.comp_realIsometry,
    `QuaternaryQuadraticForms.localizedWeight_contDiff,
    `QuaternaryQuadraticForms.localizedWeight_tsupport_subset,
    `QuaternaryQuadraticForms.localizedWeight_tsupport_subset_closedBall,
    `QuaternaryQuadraticForms.localizedWeight_hasCompactSupport,
    `QuaternaryQuadraticForms.localizedWeight_isSmoothWeight,
    `QuaternaryQuadraticForms.localizedWeight_nonzero_imp_near_support,
    `QuaternaryQuadraticForms.heathBrownTheta_integral_scaled_translate,
    `QuaternaryQuadraticForms.localizedWeight_integrable_in_center,
    `QuaternaryQuadraticForms.localizedWeight_integral_center,
    `QuaternaryQuadraticForms.localizedWeight_reconstruction,
    `QuaternaryQuadraticForms.quadraticFamily_singularIntegral_integrable_of_isometry_cover,
    `QuaternaryQuadraticForms.deltaIntegral_rescaledFrequency_norm,
    `QuaternaryQuadraticForms.deltaIntegral_rapid_scale_identity,
    `QuaternaryQuadraticForms.deltaIntegral_epsilon_scale_identity,
    `QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_add,
    `QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_double,
    `QuaternaryQuadraticForms.deltaIntegral_combine_value_derivative_bounds,
    `QuaternaryQuadraticForms.deltaIntegral_zero_weight,
    `QuaternaryQuadraticForms.deltaIntegral_eq_zero_of_support_bound,
    `QuaternaryQuadraticForms.deltaIntegral_eventually_zero,
    `QuaternaryQuadraticForms.hasDerivAt_deltaIntegral_zero,
    `QuaternaryQuadraticForms.deriv_deltaIntegral_eq_zero_of_support_bound,
    `QuaternaryQuadraticForms.deltaIntegral_uniform_cutoff,
    `QuaternaryQuadraticForms.source_delta_integrals_real,
    `QuaternaryQuadraticForms.source_delta_integrals,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.extend_of_cutoff,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.of_finite_cover,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.of_realIsometry,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.of_isometry_cover,
    `QuaternaryQuadraticForms.heathBrown_local_deltaIntegralBounds,
    `QuaternaryQuadraticForms.realQuadraticGradient_hasFDerivAt,
    `QuaternaryQuadraticForms.realHessian_realQuadraticValue,
    `QuaternaryQuadraticForms.det_realHessian_realQuadraticValue,
    `QuaternaryQuadraticForms.abs_det_realHessian_realQuadraticValue,
    `QuaternaryQuadraticForms.realQuadraticValue_hessian_uniform_lower_bound,
    `QuaternaryQuadraticForms.exists_uniformHBWeightControl,
    `QuaternaryQuadraticForms.IsSmoothWeight.comp_realIsometry,
    `QuaternaryQuadraticForms.tsupport_comp_realIsometry,
    `QuaternaryQuadraticForms.localizedWeightFamily_isSmoothWeight,
    `QuaternaryQuadraticForms.localizedWeightFamily_support_bound,
    `QuaternaryQuadraticForms.localizedIsometryWeightFamily_isSmoothWeight,
    `QuaternaryQuadraticForms.localizedIsometryWeightFamily_support_bound,
    `QuaternaryQuadraticForms.localizedIsometryWeightFamily_uniform_control,
    `QuaternaryQuadraticForms.localizedWeight_alternative,
    `QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_pos,
    `QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_norm_le_two,
    `QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_le_two,
    `QuaternaryQuadraticForms.sourceConstrainedFourierSum_zero_norm_le_two_mul_sq,
    `QuaternaryQuadraticForms.sourceMainCoefficient_local_norm_le,
    `QuaternaryQuadraticForms.graphPoint_contDiff,
    `QuaternaryQuadraticForms.graphPoint_continuous,
    `QuaternaryQuadraticForms.graphPoint_zero,
    `QuaternaryQuadraticForms.graphPoint_succ,
    `QuaternaryQuadraticForms.graphTail_apply,
    `QuaternaryQuadraticForms.graphTail_continuous,
    `QuaternaryQuadraticForms.graphTail_graphPoint,
    `QuaternaryQuadraticForms.graphPoint_graphTail,
    `QuaternaryQuadraticForms.real_inner_graphPoint,
    `QuaternaryQuadraticForms.realVector4_norm_sq_graphTail,
    `QuaternaryQuadraticForms.realQuadraticValue_graphPoint,
    `QuaternaryQuadraticForms.realQuadraticGradient_graphPoint_zero,
    `QuaternaryQuadraticForms.quadraticLinearCoeff_contDiff,
    `QuaternaryQuadraticForms.quadraticConstantCoeff_contDiff,
    `QuaternaryQuadraticForms.quadraticDiscriminant_contDiff,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_measurable,
    `QuaternaryQuadraticForms.quadraticPositiveRootDomain_isOpen,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_contDiffOn,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_firstDerivative,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_value_zero,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_zero_pos,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_unique,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_characterization,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_succ,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_norm,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_area_measure,
    `QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_graph,
    `QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable_of_geometry,
    `QuaternaryQuadraticForms.quadraticC0_thinSlab_tendsto_singularIntegral,
    `QuaternaryQuadraticForms.quadraticC0_thinSlabSingularIntegral_eq_singularIntegral,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.congr_sigma,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.quadraticC0_surface,
    `QuaternaryQuadraticForms.realVectorTail_continuous,
    `QuaternaryQuadraticForms.realVectorTail_graphPoint,
    `QuaternaryQuadraticForms.graphPoint_realVectorTail,
    `QuaternaryQuadraticForms.realVectorTail_surfaceGraph,
    `QuaternaryQuadraticForms.weightTailSupport_isCompact,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_hbGraphSelector,
    `QuaternaryQuadraticForms.weightTailSupport_subset_quadraticPositiveRootDomain,
    `QuaternaryQuadraticForms.quadraticC0_gradient_zero_pos_on_tsupport,
    `QuaternaryQuadraticForms.quadraticC0_zero_mem_graph_of_mem_tsupport,
    `QuaternaryQuadraticForms.weight_surfaceGraph_eq_zero_of_notMem_tailSupport,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_area_div_gradient,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_continuousOn,
    `QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_integrable,
    `QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_hbGraphIntegral,
    `QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable,
    `QuaternaryQuadraticForms.realQuadraticValue_eq_inner,
    `QuaternaryQuadraticForms.realQuadraticValue_contDiff,
    `QuaternaryQuadraticForms.realQuadraticValue_continuous,
    `QuaternaryQuadraticForms.realQuadraticValue_smul,
    `QuaternaryQuadraticForms.realQuadraticValue_hasGradientAt,
    `QuaternaryQuadraticForms.gradient_realQuadraticValue,
    `QuaternaryQuadraticForms.realQuadraticGradient_continuous,
    `QuaternaryQuadraticForms.realQuadraticGradient_ne_zero,
    `QuaternaryQuadraticForms.realVector4_isCompact_annulus,
    `QuaternaryQuadraticForms.realQuadraticGradient_norm_annulus_lower_bound,
    `QuaternaryQuadraticForms.gradient_realQuadraticValue_annulus_lower_bound,
    `QuaternaryQuadraticForms.realQuadraticValue_abs_bound_closedBall,
    `QuaternaryQuadraticForms.signedCoordinateIsometry_apply,
    `QuaternaryQuadraticForms.signedCoordinateChange_card,
    `QuaternaryQuadraticForms.signedCoordinateIsometry_norm,
    `QuaternaryQuadraticForms.signedCoordinateIsometry_symm_norm,
    `QuaternaryQuadraticForms.signedCoordinateIsometry_measurePreserving,
    `QuaternaryQuadraticForms.real_inner_symm_isometry,
    `QuaternaryQuadraticForms.hasGradientAt_comp_realIsometry,
    `QuaternaryQuadraticForms.gradient_comp_realIsometry,
    `QuaternaryQuadraticForms.norm_gradient_comp_realIsometry,
    `QuaternaryQuadraticForms.gradient_realQuadraticValue_comp_isometry,
    `QuaternaryQuadraticForms.realIsometryMatrix_apply,
    `QuaternaryQuadraticForms.realIsometryMatrix_det_ne_zero,
    `QuaternaryQuadraticForms.realQuadraticValue_matrix_congruence,
    `QuaternaryQuadraticForms.realQuadraticPullbackMatrix_value,
    `QuaternaryQuadraticForms.realQuadraticPullbackMatrix_symmetric,
    `QuaternaryQuadraticForms.realQuadraticPullbackMatrix_det_ne_zero,
    `QuaternaryQuadraticForms.deltaIntegral_comp_realIsometry,
    `QuaternaryQuadraticForms.singularSeriesRemovalFactor_eq_primeFactors,
    `QuaternaryQuadraticForms.singularSeriesRemovalFactor_one,
    `QuaternaryQuadraticForms.singularSeriesConstant_eq_orderedValue,
    `QuaternaryQuadraticForms.singularSeriesConstant_eq_of_goodPrimeAgreement,
    `QuaternaryQuadraticForms.sourceMainCoefficient_one,
    `QuaternaryQuadraticForms.sourceMainCoefficient_one_eq_singularSeriesConstant,
    `QuaternaryQuadraticForms.sourceMainCoefficient_eq_prime_product,
    `QuaternaryQuadraticForms.sourceMainCoefficient_norm_le,
    `QuaternaryQuadraticForms.source_main_coefficient_bound,
    `QuaternaryQuadraticForms.surfaceGraph_injective,
    `QuaternaryQuadraticForms.surfaceGraph_measurable,
    `QuaternaryQuadraticForms.surfaceGraph_measurableEmbedding,
    `QuaternaryQuadraticForms.graphAreaFactor_pos,
    `QuaternaryQuadraticForms.graphAreaFactor_nonneg,
    `QuaternaryQuadraticForms.graphAreaFactor_measurable,
    `QuaternaryQuadraticForms.integral_surfaceGraph_image,
    `QuaternaryQuadraticForms.integrable_surfaceGraph_image_iff,
    `QuaternaryQuadraticForms.euclideanSurfaceMeasure_realIsometry,
    `QuaternaryQuadraticForms.euclideanSurfaceMeasure_restrict_realIsometry,
    `QuaternaryQuadraticForms.singularIntegral_integrable_comp_realIsometry,
    `QuaternaryQuadraticForms.singularIntegral_comp_realIsometry,
    `QuaternaryQuadraticForms.mem_integerQuadricZeros,
    `QuaternaryQuadraticForms.sourceQuadricZeroSet_eq,
    `QuaternaryQuadraticForms.sourceQuadricZeroSet_finite,
    `QuaternaryQuadraticForms.sourceQuadricZeroSet_ncard,
    `QuaternaryQuadraticForms.integerQuadricZeros_card_le_one,
    `QuaternaryQuadraticForms.integerQuadricZeros_bound_of_lattice_model,
    `QuaternaryQuadraticForms.rationalQuadric_euclidean_bound,
    `QuaternaryQuadraticForms.source_quadric_count,
    `QuaternaryQuadraticForms.binary_zero_discriminant_isSquare,
    `QuaternaryQuadraticForms.det_hyperbolic_binary,
    `QuaternaryQuadraticForms.nonsquare_det_binary_anisotropic,
    `QuaternaryQuadraticForms.exists_hyperbolic_complement_basis,
    `QuaternaryQuadraticForms.rational_congruence_apply,
    `QuaternaryQuadraticForms.exists_rational_hyperbolic_matrix,
    `QuaternaryQuadraticForms.rational_family_clear_denominators,
    `QuaternaryQuadraticForms.integerMatrix_coordinate_bound,
    `QuaternaryQuadraticForms.rationalQuadric_integer_model,
    `QuaternaryQuadraticForms.exists_rational_quadric_normal_form,
    `QuaternaryQuadraticForms.splitQuadric_mem_interval,
    `QuaternaryQuadraticForms.splitQuadricCoefficient_pos,
    `QuaternaryQuadraticForms.splitQuadric_binaryValue_natAbs_le,
    `QuaternaryQuadraticForms.splitQuadric_zero_fiber_card_le,
    `QuaternaryQuadraticForms.splitQuadric_nonzero_fibers_uniform,
    `QuaternaryQuadraticForms.splitQuadric_nonzero_box_card_le,
    `QuaternaryQuadraticForms.splitQuadric_box_bound,
    `QuaternaryQuadraticForms.splitQuadric_mem_signedDivisors,
    `QuaternaryQuadraticForms.splitQuadric_signedDivisors_card_le,
    `QuaternaryQuadraticForms.splitQuadric_nonzero_fiber_card_le,
    `QuaternaryQuadraticForms.poissonTestFunction_isSmoothWeight,
    `QuaternaryQuadraticForms.poissonTestFunction_eventually_zero,
    `QuaternaryQuadraticForms.poissonDeltaIntegral_eventually_zero,
    `QuaternaryQuadraticForms.mixedIntegerSummand_fourier_phase,
    `QuaternaryQuadraticForms.poisson_mixed_fourier_coefficient,
    `QuaternaryQuadraticForms.poisson_mixed_complete_sum,
    `QuaternaryQuadraticForms.realQuadraticValue_integerRealVector,
    `QuaternaryQuadraticForms.realQuadraticValue_scaled_integerRealVector,
    `QuaternaryQuadraticForms.poisson_delta_scaled_argument,
    `QuaternaryQuadraticForms.poisson_delta_phase,
    `QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_weight_eq_zero,
    `QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_of_dvd,
    `QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_not_dvd,
    `QuaternaryQuadraticForms.poissonDeltaLatticeTerm_summable,
    `QuaternaryQuadraticForms.weightedQuadraticZeroSum_pointwise_delta,
    `QuaternaryQuadraticForms.poisson_tsum_comm_of_finite_left,
    `QuaternaryQuadraticForms.weightedQuadraticZeroSum_delta,
    `QuaternaryQuadraticForms.poisson_test_function_complete_sum,
    `QuaternaryQuadraticForms.poissonFrequencyTerm_eventually_zero,
    `QuaternaryQuadraticForms.poissonModulusTerm_finite_support,
    `QuaternaryQuadraticForms.compactSupport_integerRealVector_finite,
    `QuaternaryQuadraticForms.scaledWeight_integerRealVector_finite,
    `QuaternaryQuadraticForms.weightedQuadraticZeroSum_finite_support,
    `QuaternaryQuadraticForms.poissonTestFunction_integerRealVector_finite,
    `QuaternaryQuadraticForms.weightedQuadraticZeroSum_extend_eq_source,
    `QuaternaryQuadraticForms.poisson_normalization_factor,
    `QuaternaryQuadraticForms.poissonResidueVector_cast,
    `QuaternaryQuadraticForms.poissonResidueVector_injective,
    `QuaternaryQuadraticForms.poissonResidueVector_surjective,
    `QuaternaryQuadraticForms.poissonResidueEquiv_apply,
    `QuaternaryQuadraticForms.integerRealVector_poissonResidueVector,
    `QuaternaryQuadraticForms.poisson_tsum_residue_classes,
    `QuaternaryQuadraticForms.poisson_phase_mul_summable,
    `QuaternaryQuadraticForms.poisson_residue_fourier_summable,
    `QuaternaryQuadraticForms.poisson_periodic_weight,
    `QuaternaryQuadraticForms.poisson_integral_comp_inv_smul,
    `QuaternaryQuadraticForms.poissonFourierIntegral_testFunction_general,
    `QuaternaryQuadraticForms.poisson_frequency_scale,
    `QuaternaryQuadraticForms.poissonFourierIntegral_testFunction,
    `QuaternaryQuadraticForms.integerRealVector_inner,
    `QuaternaryQuadraticForms.poisson_affine_phase_eq_stdAddChar,
    `QuaternaryQuadraticForms.poisson_affine_integer_lattice,
    `QuaternaryQuadraticForms.mixedCompleteSum_extend_eq_source,
    `QuaternaryQuadraticForms.weightedQuadraticZeroSum_poisson,
    `QuaternaryQuadraticForms.source_delta_poisson,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error,
    `QuaternaryQuadraticForms.source_localized_frequency_integrals,
    `QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale,
    `QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale,
    `QuaternaryQuadraticForms.integerEuclidean_frequency_tail,
    `QuaternaryQuadraticForms.sourceMixedCompleteSum_trivial_bound,
    `QuaternaryQuadraticForms.sourceCompositeWeight_zero_of_one_lt,
    `QuaternaryQuadraticForms.sourceMixedCompleteSum_zero_frequency,
    `QuaternaryQuadraticForms.source_zero_frequency_contribution,
    `QuaternaryQuadraticForms.mem_poissonModuliBelow,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.largeFrequency,
    `QuaternaryQuadraticForms.source_large_frequency_truncation,
    `QuaternaryQuadraticForms.mem_offConeFrequencies,
    `QuaternaryQuadraticForms.sourceMixedCompleteSum_sum_le_gcd_classes,
    `QuaternaryQuadraticForms.dualQuadraticValue_ball_bound,
    `QuaternaryQuadraticForms.ScaledFrequencyIntegralBound.offCone_modulus_reduction,
    `QuaternaryQuadraticForms.offCone_dual_growth,
    `QuaternaryQuadraticForms.offCone_average_scale]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"
  let inputNames : List Lean.Name := [
    `QuaternaryQuadraticForms.Trusted.weil_simple_roots,
    `QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data,
    `QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants,
    `QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent,
    `QuaternaryQuadraticForms.Trusted.heathBrown_delta_data,
    `QuaternaryQuadraticForms.Trusted.simon_graph_area,
    `QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization,
    `QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph,
    `QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation,
    `QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction,
    `QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds,
    `QuaternaryQuadraticForms.Trusted.poisson_four_dimensional]
  for name in inputNames do
    match environment.find? name with
    | some (.axiomInfo _) => pure ()
    | _ => Lean.throwError "Expected a registered external premise for {name}"
  let _ ← environment.constants.foldM (init := ()) fun _ name info => do
    if (`QuaternaryQuadraticForms).isPrefixOf name then
      match info with
      | .axiomInfo _ =>
        unless inputNames.contains name do
          Lean.throwError "Unregistered project axiom: {name}"
      | _ => pure ()
    else
      pure ()
  pure ()

#check @QuaternaryQuadraticForms.Trusted.weil_simple_roots
#print axioms QuaternaryQuadraticForms.Trusted.weil_simple_roots

#check @QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data
#print axioms QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data

#check @QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants
#print axioms QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants

#check @QuaternaryQuadraticForms.weighted_ray_sum
#print axioms QuaternaryQuadraticForms.weighted_ray_sum

#check @QuaternaryQuadraticForms.primitiveAddChar_units_sum
#print axioms QuaternaryQuadraticForms.primitiveAddChar_units_sum

#check @QuaternaryQuadraticForms.stdAddChar_units_sum
#print axioms QuaternaryQuadraticForms.stdAddChar_units_sum

#check @QuaternaryQuadraticForms.projectiveRayVector_injective
#print axioms QuaternaryQuadraticForms.projectiveRayVector_injective

#check @QuaternaryQuadraticForms.projectiveRayVector_surjective
#print axioms QuaternaryQuadraticForms.projectiveRayVector_surjective

#check @QuaternaryQuadraticForms.invariant_rep_mk
#print axioms QuaternaryQuadraticForms.invariant_rep_mk

#check @QuaternaryQuadraticForms.cone_rep_mk
#print axioms QuaternaryQuadraticForms.cone_rep_mk

#check @QuaternaryQuadraticForms.sum_cone_weighted_eq_sum_projective
#print axioms QuaternaryQuadraticForms.sum_cone_weighted_eq_sum_projective

#check @QuaternaryQuadraticForms.homogeneous_eval_smul
#print axioms QuaternaryQuadraticForms.homogeneous_eval_smul

#check @QuaternaryQuadraticForms.homogeneous_reduce_mod
#print axioms QuaternaryQuadraticForms.homogeneous_reduce_mod

#check @QuaternaryQuadraticForms.polynomialCharacterWeight_properties
#print axioms QuaternaryQuadraticForms.polynomialCharacterWeight_properties

#check @QuaternaryQuadraticForms.mem_projectiveQuadric_mk
#print axioms QuaternaryQuadraticForms.mem_projectiveQuadric_mk

#check @QuaternaryQuadraticForms.projectiveWeight_rep_mk
#print axioms QuaternaryQuadraticForms.projectiveWeight_rep_mk

#check @QuaternaryQuadraticForms.hyperplane_rep_mk
#print axioms QuaternaryQuadraticForms.hyperplane_rep_mk

#check @QuaternaryQuadraticForms.fourierSum_ray_identity
#print axioms QuaternaryQuadraticForms.fourierSum_ray_identity

#check @QuaternaryQuadraticForms.fourierSum_zero
#print axioms QuaternaryQuadraticForms.fourierSum_zero

#check @QuaternaryQuadraticForms.reduceFrequency_eq_zero_iff
#print axioms QuaternaryQuadraticForms.reduceFrequency_eq_zero_iff

#check @QuaternaryQuadraticForms.integralFourierSum_ray_identity
#print axioms QuaternaryQuadraticForms.integralFourierSum_ray_identity

#check @QuaternaryQuadraticForms.integralFourierSum_of_dvd
#print axioms QuaternaryQuadraticForms.integralFourierSum_of_dvd

#check @QuaternaryQuadraticForms.complexQuadraticChar_apply
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_apply

#check @QuaternaryQuadraticForms.complexQuadraticChar_isQuadratic
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_isQuadratic

#check @QuaternaryQuadraticForms.complexQuadraticChar_sq
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_sq

#check @QuaternaryQuadraticForms.complexQuadraticChar_ne_one
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_ne_one

#check @QuaternaryQuadraticForms.complexQuadraticChar_intCast
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_intCast

#check @QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial
#print axioms QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_homogeneous
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_homogeneous

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree_le
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree_le

#check @QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial_quadraticValue
#print axioms QuaternaryQuadraticForms.eval_matrixQuadraticPolynomial_quadraticValue

#check @QuaternaryQuadraticForms.quadraticZeroIndicator_eval
#print axioms QuaternaryQuadraticForms.quadraticZeroIndicator_eval

#check @QuaternaryQuadraticForms.quadraticCharacterPolynomial_sum_zero
#print axioms QuaternaryQuadraticForms.quadraticCharacterPolynomial_sum_zero

#check @QuaternaryQuadraticForms.affineQuadraticCharacterSum_dvd
#print axioms QuaternaryQuadraticForms.affineQuadraticCharacterSum_dvd

#check @QuaternaryQuadraticForms.quadraticTraceWeight_rep_mk
#print axioms QuaternaryQuadraticForms.quadraticTraceWeight_rep_mk

#check @QuaternaryQuadraticForms.affineQuadraticTrace_complex
#print axioms QuaternaryQuadraticForms.affineQuadraticTrace_complex

#check @QuaternaryQuadraticForms.projectiveQuadraticTrace_complex
#print axioms QuaternaryQuadraticForms.projectiveQuadraticTrace_complex

#check @QuaternaryQuadraticForms.affineQuadraticTrace_eq
#print axioms QuaternaryQuadraticForms.affineQuadraticTrace_eq

#check @QuaternaryQuadraticForms.affineQuadraticTrace_dvd
#print axioms QuaternaryQuadraticForms.affineQuadraticTrace_dvd

#check @QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd
#print axioms QuaternaryQuadraticForms.projectiveQuadraticTrace_dvd

#check @QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd
#print axioms QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd

#check @QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd
#print axioms QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd

#check @QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd
#print axioms QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd

#check @QuaternaryQuadraticForms.binaryVector_eq_vec
#print axioms QuaternaryQuadraticForms.binaryVector_eq_vec

#check @QuaternaryQuadraticForms.projectiveLinePoint_injective
#print axioms QuaternaryQuadraticForms.projectiveLinePoint_injective

#check @QuaternaryQuadraticForms.projectiveLinePoint_surjective
#print axioms QuaternaryQuadraticForms.projectiveLinePoint_surjective

#check @QuaternaryQuadraticForms.projectiveLinePoint_weight
#print axioms QuaternaryQuadraticForms.projectiveLinePoint_weight

#check @QuaternaryQuadraticForms.sum_projectiveLine
#print axioms QuaternaryQuadraticForms.sum_projectiveLine

#check @QuaternaryQuadraticForms.projectiveLinePoint_predicate
#print axioms QuaternaryQuadraticForms.projectiveLinePoint_predicate

#check @QuaternaryQuadraticForms.binaryDehom_eval
#print axioms QuaternaryQuadraticForms.binaryDehom_eval

#check @QuaternaryQuadraticForms.binaryDehom_map
#print axioms QuaternaryQuadraticForms.binaryDehom_map

#check @QuaternaryQuadraticForms.binaryDehom_homogenize
#print axioms QuaternaryQuadraticForms.binaryDehom_homogenize

#check @QuaternaryQuadraticForms.binaryDehom_ne_zero
#print axioms QuaternaryQuadraticForms.binaryDehom_ne_zero

#check @QuaternaryQuadraticForms.binaryDehom_natDegree_le
#print axioms QuaternaryQuadraticForms.binaryDehom_natDegree_le

#check @QuaternaryQuadraticForms.homogenize_eval_infinity
#print axioms QuaternaryQuadraticForms.homogenize_eval_infinity

#check @QuaternaryQuadraticForms.binaryDehom_coeff_top
#print axioms QuaternaryQuadraticForms.binaryDehom_coeff_top

#check @QuaternaryQuadraticForms.binaryDehom_natDegree_eq_iff
#print axioms QuaternaryQuadraticForms.binaryDehom_natDegree_eq_iff

#check @QuaternaryQuadraticForms.binaryDehom_natDegree_lt_of_infinity_zero
#print axioms QuaternaryQuadraticForms.binaryDehom_natDegree_lt_of_infinity_zero

#check @QuaternaryQuadraticForms.rootSet_card_le_natDegree
#print axioms QuaternaryQuadraticForms.rootSet_card_le_natDegree

#check @QuaternaryQuadraticForms.geometricRootCount_eq_natDegree_iff
#print axioms QuaternaryQuadraticForms.geometricRootCount_eq_natDegree_iff

#check @QuaternaryQuadraticForms.geometricRootCount_eq_natDegree
#print axioms QuaternaryQuadraticForms.geometricRootCount_eq_natDegree

#check @QuaternaryQuadraticForms.homogeneous_binary_zero_units_smul
#print axioms QuaternaryQuadraticForms.homogeneous_binary_zero_units_smul

#check @QuaternaryQuadraticForms.binaryProjectiveZeros_card
#print axioms QuaternaryQuadraticForms.binaryProjectiveZeros_card

#check @QuaternaryQuadraticForms.binaryDehom_degree_and_rootCount
#print axioms QuaternaryQuadraticForms.binaryDehom_degree_and_rootCount

#check @QuaternaryQuadraticForms.binaryDehom_geometric_data
#print axioms QuaternaryQuadraticForms.binaryDehom_geometric_data

#check @QuaternaryQuadraticForms.binaryDehom_geometric_separable
#print axioms QuaternaryQuadraticForms.binaryDehom_geometric_separable

#check @QuaternaryQuadraticForms.weil_bound
#print axioms QuaternaryQuadraticForms.weil_bound

#check @QuaternaryQuadraticForms.weil_bound_of_separable
#print axioms QuaternaryQuadraticForms.weil_bound_of_separable

#check @QuaternaryQuadraticForms.projectiveLineCharacterSum_chart
#print axioms QuaternaryQuadraticForms.projectiveLineCharacterSum_chart

#check @QuaternaryQuadraticForms.projectiveLineCharacterSum_bound_of_affine_roots
#print axioms QuaternaryQuadraticForms.projectiveLineCharacterSum_bound_of_affine_roots

#check @QuaternaryQuadraticForms.projective_weil_bound
#print axioms QuaternaryQuadraticForms.projective_weil_bound

#check @QuaternaryQuadraticForms.pderiv_aeval_chain_rule
#print axioms QuaternaryQuadraticForms.pderiv_aeval_chain_rule

#check @QuaternaryQuadraticForms.eval_aeval_polynomial
#print axioms QuaternaryQuadraticForms.eval_aeval_polynomial

#check @QuaternaryQuadraticForms.eval_pderiv_aeval_chain_rule
#print axioms QuaternaryQuadraticForms.eval_pderiv_aeval_chain_rule

#check @QuaternaryQuadraticForms.mem_planeSubspace
#print axioms QuaternaryQuadraticForms.mem_planeSubspace

#check @QuaternaryQuadraticForms.matrixBilin_isSymm
#print axioms QuaternaryQuadraticForms.matrixBilin_isSymm

#check @QuaternaryQuadraticForms.matrix_mulVec_adjugate
#print axioms QuaternaryQuadraticForms.matrix_mulVec_adjugate

#check @QuaternaryQuadraticForms.adjugate_bilin_self
#print axioms QuaternaryQuadraticForms.adjugate_bilin_self

#check @QuaternaryQuadraticForms.planeSubspace_eq_orthogonal
#print axioms QuaternaryQuadraticForms.planeSubspace_eq_orthogonal

#check @QuaternaryQuadraticForms.plane_bilin_nondegenerate
#print axioms QuaternaryQuadraticForms.plane_bilin_nondegenerate

#check @QuaternaryQuadraticForms.planeFunctional_ne_zero
#print axioms QuaternaryQuadraticForms.planeFunctional_ne_zero

#check @QuaternaryQuadraticForms.planeSubspace_finrank
#print axioms QuaternaryQuadraticForms.planeSubspace_finrank

#check @QuaternaryQuadraticForms.eval_planePolynomial
#print axioms QuaternaryQuadraticForms.eval_planePolynomial

#check @QuaternaryQuadraticForms.planePolynomial_totalDegree_le
#print axioms QuaternaryQuadraticForms.planePolynomial_totalDegree_le

#check @QuaternaryQuadraticForms.plane_exists_isotropic
#print axioms QuaternaryQuadraticForms.plane_exists_isotropic

#check @QuaternaryQuadraticForms.exists_hyperbolic_partner
#print axioms QuaternaryQuadraticForms.exists_hyperbolic_partner

#check @QuaternaryQuadraticForms.exists_common_orthogonal
#print axioms QuaternaryQuadraticForms.exists_common_orthogonal

#check @QuaternaryQuadraticForms.hyperbolic_triple_linearIndependent
#print axioms QuaternaryQuadraticForms.hyperbolic_triple_linearIndependent

#check @QuaternaryQuadraticForms.exists_ternary_hyperbolic_coordinates
#print axioms QuaternaryQuadraticForms.exists_ternary_hyperbolic_coordinates

#check @QuaternaryQuadraticForms.plane_exists_hyperbolic_coordinates
#print axioms QuaternaryQuadraticForms.plane_exists_hyperbolic_coordinates

#check @QuaternaryQuadraticForms.extendCoordinateMap_apply_map
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_apply_map

#check @QuaternaryQuadraticForms.extendCoordinateMap_comp
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_comp

#check @QuaternaryQuadraticForms.extendCoordinateMap_id
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_id

#check @QuaternaryQuadraticForms.extendCoordinateMap_injective
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_injective

#check @QuaternaryQuadraticForms.eval_coordinatePolynomial
#print axioms QuaternaryQuadraticForms.eval_coordinatePolynomial

#check @QuaternaryQuadraticForms.coordinatePolynomial_homogeneous
#print axioms QuaternaryQuadraticForms.coordinatePolynomial_homogeneous

#check @QuaternaryQuadraticForms.coordinatePolynomial_map
#print axioms QuaternaryQuadraticForms.coordinatePolynomial_map

#check @QuaternaryQuadraticForms.extendCoordinateMap_mem_plane
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_mem_plane

#check @QuaternaryQuadraticForms.planeSubspace_finrank_of_ne_zero
#print axioms QuaternaryQuadraticForms.planeSubspace_finrank_of_ne_zero

#check @QuaternaryQuadraticForms.extendCoordinateMap_range_plane
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_range_plane

#check @QuaternaryQuadraticForms.map_aeval_polynomial
#print axioms QuaternaryQuadraticForms.map_aeval_polynomial

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_map
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_map

#check @QuaternaryQuadraticForms.extendCoordinateMap_quadratic
#print axioms QuaternaryQuadraticForms.extendCoordinateMap_quadratic

#check @QuaternaryQuadraticForms.canonicalConicVector_smul
#print axioms QuaternaryQuadraticForms.canonicalConicVector_smul

#check @QuaternaryQuadraticForms.canonicalConicVector_ne_zero
#print axioms QuaternaryQuadraticForms.canonicalConicVector_ne_zero

#check @QuaternaryQuadraticForms.canonicalConicValue_vector
#print axioms QuaternaryQuadraticForms.canonicalConicValue_vector

#check @QuaternaryQuadraticForms.canonicalConicValue_smul
#print axioms QuaternaryQuadraticForms.canonicalConicValue_smul

#check @QuaternaryQuadraticForms.canonicalConicValue_units_zero_iff
#print axioms QuaternaryQuadraticForms.canonicalConicValue_units_zero_iff

#check @QuaternaryQuadraticForms.canonicalConicProjective_mk
#print axioms QuaternaryQuadraticForms.canonicalConicProjective_mk

#check @QuaternaryQuadraticForms.canonicalConicPoint_injective
#print axioms QuaternaryQuadraticForms.canonicalConicPoint_injective

#check @QuaternaryQuadraticForms.canonicalConicVector_surjective_projective
#print axioms QuaternaryQuadraticForms.canonicalConicVector_surjective_projective

#check @QuaternaryQuadraticForms.canonicalConicPoint_surjective
#print axioms QuaternaryQuadraticForms.canonicalConicPoint_surjective

#check @QuaternaryQuadraticForms.canonicalConic_derivatives_independent
#print axioms QuaternaryQuadraticForms.canonicalConic_derivatives_independent

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_eval
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_eval

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_homogeneous
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_homogeneous

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_partial_s
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_partial_s

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_partial_t
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_partial_t

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_partials_independent
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_partials_independent

#check @QuaternaryQuadraticForms.canonicalConicPolynomials_map
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomials_map

#check @QuaternaryQuadraticForms.BinaryNonsingular.ne_zero
#print axioms QuaternaryQuadraticForms.BinaryNonsingular.ne_zero

#check @QuaternaryQuadraticForms.binaryDehom_derivative
#print axioms QuaternaryQuadraticForms.binaryDehom_derivative

#check @QuaternaryQuadraticForms.binary_euler_eval
#print axioms QuaternaryQuadraticForms.binary_euler_eval

#check @QuaternaryQuadraticForms.binaryDehom_euler
#print axioms QuaternaryQuadraticForms.binaryDehom_euler

#check @QuaternaryQuadraticForms.binaryDehom_derivative_ne_zero
#print axioms QuaternaryQuadraticForms.binaryDehom_derivative_ne_zero

#check @QuaternaryQuadraticForms.binaryDehom_separable_of_nonsingular
#print axioms QuaternaryQuadraticForms.binaryDehom_separable_of_nonsingular

#check @QuaternaryQuadraticForms.coeff_X_mul_derivative
#print axioms QuaternaryQuadraticForms.coeff_X_mul_derivative

#check @QuaternaryQuadraticForms.binaryDehom_degree_of_nonsingular_infinity
#print axioms QuaternaryQuadraticForms.binaryDehom_degree_of_nonsingular_infinity

#check @QuaternaryQuadraticForms.binaryProjectiveZeros_card_of_nonsingular
#print axioms QuaternaryQuadraticForms.binaryProjectiveZeros_card_of_nonsingular

#check @QuaternaryQuadraticForms.binary_nonsingular_geometric_roots
#print axioms QuaternaryQuadraticForms.binary_nonsingular_geometric_roots

#check @QuaternaryQuadraticForms.independent_three_two_dot_impossible
#print axioms QuaternaryQuadraticForms.independent_three_two_dot_impossible

#check @QuaternaryQuadraticForms.pderiv_planePolynomial
#print axioms QuaternaryQuadraticForms.pderiv_planePolynomial

#check @QuaternaryQuadraticForms.polynomialGradient_plane
#print axioms QuaternaryQuadraticForms.polynomialGradient_plane

#check @QuaternaryQuadraticForms.eval_pderiv_pullback
#print axioms QuaternaryQuadraticForms.eval_pderiv_pullback

#check @QuaternaryQuadraticForms.transverse_pullback_nonsingular
#print axioms QuaternaryQuadraticForms.transverse_pullback_nonsingular

#check @QuaternaryQuadraticForms.rank_three_iff_linearIndependent
#print axioms QuaternaryQuadraticForms.rank_three_iff_linearIndependent

#check @QuaternaryQuadraticForms.planeTransverseRank_iff
#print axioms QuaternaryQuadraticForms.planeTransverseRank_iff

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_eval
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_eval

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_homogeneous
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_homogeneous

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_map
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_map

#check @QuaternaryQuadraticForms.coordinatePolynomial_pderiv
#print axioms QuaternaryQuadraticForms.coordinatePolynomial_pderiv

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_partial
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_partial

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_partials_independent
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_partials_independent

#check @QuaternaryQuadraticForms.eval_canonicalConicPolynomial
#print axioms QuaternaryQuadraticForms.eval_canonicalConicPolynomial

#check @QuaternaryQuadraticForms.canonicalConicPolynomial_homogeneous
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomial_homogeneous

#check @QuaternaryQuadraticForms.coordinateQuadratic_pullback
#print axioms QuaternaryQuadraticForms.coordinateQuadratic_pullback

#check @QuaternaryQuadraticForms.canonicalConicPolynomial_substitution
#print axioms QuaternaryQuadraticForms.canonicalConicPolynomial_substitution

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_quadric_identity
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_quadric_identity

#check @QuaternaryQuadraticForms.coordinatePlane_pullback
#print axioms QuaternaryQuadraticForms.coordinatePlane_pullback

#check @QuaternaryQuadraticForms.embeddedConicPolynomials_plane_identity
#print axioms QuaternaryQuadraticForms.embeddedConicPolynomials_plane_identity

#check @QuaternaryQuadraticForms.planeConic_units_iff
#print axioms QuaternaryQuadraticForms.planeConic_units_iff

#check @QuaternaryQuadraticForms.embeddedCanonicalConicPoint_injective
#print axioms QuaternaryQuadraticForms.embeddedCanonicalConicPoint_injective

#check @QuaternaryQuadraticForms.embeddedCanonicalConicPoint_surjective
#print axioms QuaternaryQuadraticForms.embeddedCanonicalConicPoint_surjective

#check @QuaternaryQuadraticForms.embeddedConicEquiv_mk
#print axioms QuaternaryQuadraticForms.embeddedConicEquiv_mk

#check @QuaternaryQuadraticForms.goodPrime_ne_two
#print axioms QuaternaryQuadraticForms.goodPrime_ne_two

#check @QuaternaryQuadraticForms.goodPrime_reduced_det_ne_zero
#print axioms QuaternaryQuadraticForms.goodPrime_reduced_det_ne_zero

#check @QuaternaryQuadraticForms.reduceQuadraticMatrix_symmetric
#print axioms QuaternaryQuadraticForms.reduceQuadraticMatrix_symmetric

#check @QuaternaryQuadraticForms.reduceQuadraticMatrix_adjugate
#print axioms QuaternaryQuadraticForms.reduceQuadraticMatrix_adjugate

#check @QuaternaryQuadraticForms.primeField_two_ne_zero
#print axioms QuaternaryQuadraticForms.primeField_two_ne_zero

#check @QuaternaryQuadraticForms.conic_parametrization_prime_field
#print axioms QuaternaryQuadraticForms.conic_parametrization_prime_field

#check @QuaternaryQuadraticForms.conic_parametrization
#print axioms QuaternaryQuadraticForms.conic_parametrization

#check @QuaternaryQuadraticForms.projectiveSectionTrace_eq_sum_conic
#print axioms QuaternaryQuadraticForms.projectiveSectionTrace_eq_sum_conic

#check @QuaternaryQuadraticForms.projectiveSectionTrace_eq_projectiveLine
#print axioms QuaternaryQuadraticForms.projectiveSectionTrace_eq_projectiveLine

#check @QuaternaryQuadraticForms.plane_section_bound_of_parametrization
#print axioms QuaternaryQuadraticForms.plane_section_bound_of_parametrization

#check @QuaternaryQuadraticForms.plane_section_bound_prime_field
#print axioms QuaternaryQuadraticForms.plane_section_bound_prime_field

#check @QuaternaryQuadraticForms.plane_section_bound
#print axioms QuaternaryQuadraticForms.plane_section_bound

#check @QuaternaryQuadraticForms.rank_two_iff_linearIndependent
#print axioms QuaternaryQuadraticForms.rank_two_iff_linearIndependent

#check @QuaternaryQuadraticForms.projectiveIntersectionTransverseRank_iff
#print axioms QuaternaryQuadraticForms.projectiveIntersectionTransverseRank_iff

#check @QuaternaryQuadraticForms.mem_badReductionPrimes
#print axioms QuaternaryQuadraticForms.mem_badReductionPrimes

#check @QuaternaryQuadraticForms.prime_dvd_primeRadical_iff
#print axioms QuaternaryQuadraticForms.prime_dvd_primeRadical_iff

#check @QuaternaryQuadraticForms.primeRadical_pos
#print axioms QuaternaryQuadraticForms.primeRadical_pos

#check @QuaternaryQuadraticForms.quadraticBadPrimeModulus_ne_zero
#print axioms QuaternaryQuadraticForms.quadraticBadPrimeModulus_ne_zero

#check @QuaternaryQuadraticForms.polynomialBadPrimeModulus_pos
#print axioms QuaternaryQuadraticForms.polynomialBadPrimeModulus_pos

#check @QuaternaryQuadraticForms.prime_dvd_product_primes_iff
#print axioms QuaternaryQuadraticForms.prime_dvd_product_primes_iff

#check @QuaternaryQuadraticForms.not_dvd_polynomialBadPrimeModulus_iff
#print axioms QuaternaryQuadraticForms.not_dvd_polynomialBadPrimeModulus_iff

#check @QuaternaryQuadraticForms.badReductionPrimes_subset_primeFactors_of_common_divisor
#print axioms QuaternaryQuadraticForms.badReductionPrimes_subset_primeFactors_of_common_divisor

#check @QuaternaryQuadraticForms.badReductionPrimes_finite_of_common_divisor
#print axioms QuaternaryQuadraticForms.badReductionPrimes_finite_of_common_divisor

#check @QuaternaryQuadraticForms.badReductionPrimeProduct_dvd_common_divisor
#print axioms QuaternaryQuadraticForms.badReductionPrimeProduct_dvd_common_divisor

#check @QuaternaryQuadraticForms.polynomialBadPrimeModulus_le_of_common_divisor
#print axioms QuaternaryQuadraticForms.polynomialBadPrimeModulus_le_of_common_divisor

#check @QuaternaryQuadraticForms.eval_pderiv_matrixQuadraticPolynomial
#print axioms QuaternaryQuadraticForms.eval_pderiv_matrixQuadraticPolynomial

#check @QuaternaryQuadraticForms.polynomialGradient_matrixQuadraticPolynomial
#print axioms QuaternaryQuadraticForms.polynomialGradient_matrixQuadraticPolynomial

#check @QuaternaryQuadraticForms.matrixQuadratic_gradient_ne_zero
#print axioms QuaternaryQuadraticForms.matrixQuadratic_gradient_ne_zero

#check @QuaternaryQuadraticForms.matrixQuadratic_projective_smooth
#print axioms QuaternaryQuadraticForms.matrixQuadratic_projective_smooth

#check @QuaternaryQuadraticForms.matrixQuadratic_projective_smooth_map
#print axioms QuaternaryQuadraticForms.matrixQuadratic_projective_smooth_map

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_ne_zero
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_ne_zero

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_totalDegree

#check @QuaternaryQuadraticForms.eval_pderiv_eq_of_totalDegree_le_one
#print axioms QuaternaryQuadraticForms.eval_pderiv_eq_of_totalDegree_le_one

#check @QuaternaryQuadraticForms.polynomialGradient_eq_of_totalDegree_le_one
#print axioms QuaternaryQuadraticForms.polynomialGradient_eq_of_totalDegree_le_one

#check @QuaternaryQuadraticForms.matrixQuadratic_not_mul_affine
#print axioms QuaternaryQuadraticForms.matrixQuadratic_not_mul_affine

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible_map
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_irreducible_map

#check @QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_coeff
#print axioms QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_coeff

#check @QuaternaryQuadraticForms.surfaceChernRelation_coefficients
#print axioms QuaternaryQuadraticForms.surfaceChernRelation_coefficients

#check @QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_of_relation
#print axioms QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_of_relation

#check @QuaternaryQuadraticForms.quadricChernPolynomial_relation
#print axioms QuaternaryQuadraticForms.quadricChernPolynomial_relation

#check @QuaternaryQuadraticForms.quadric_surfaceSectionEulerCoefficient
#print axioms QuaternaryQuadraticForms.quadric_surfaceSectionEulerCoefficient

#check @QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_quadric_of_relation
#print axioms QuaternaryQuadraticForms.surfaceSectionEulerCoefficient_quadric_of_relation

#check @QuaternaryQuadraticForms.norm_sum_le_card_mul
#print axioms QuaternaryQuadraticForms.norm_sum_le_card_mul

#check @QuaternaryQuadraticForms.mem_projectiveHypersurfacePoints_mk
#print axioms QuaternaryQuadraticForms.mem_projectiveHypersurfacePoints_mk

#check @QuaternaryQuadraticForms.projectiveHypersurfacePoints_matrix
#print axioms QuaternaryQuadraticForms.projectiveHypersurfacePoints_matrix

#check @QuaternaryQuadraticForms.projectiveHypersurfaceTrace_matrix
#print axioms QuaternaryQuadraticForms.projectiveHypersurfaceTrace_matrix

#check @QuaternaryQuadraticForms.transverse_polynomial_ne_zero
#print axioms QuaternaryQuadraticForms.transverse_polynomial_ne_zero

#check @QuaternaryQuadraticForms.quadric_transverse_polynomial_ne_zero
#print axioms QuaternaryQuadraticForms.quadric_transverse_polynomial_ne_zero

#check @QuaternaryQuadraticForms.katz_quadric_bound_prime_field
#print axioms QuaternaryQuadraticForms.katz_quadric_bound_prime_field

#check @QuaternaryQuadraticForms.katz_quadric_bound
#print axioms QuaternaryQuadraticForms.katz_quadric_bound

#check @QuaternaryQuadraticForms.projectiveQuadraticTrace_abs_le
#print axioms QuaternaryQuadraticForms.projectiveQuadraticTrace_abs_le

#check @QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd_bound
#print axioms QuaternaryQuadraticForms.projectiveTrace_quadratic_integral_dvd_bound

#check @QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_abs_le
#print axioms QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_abs_le

#check @QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound
#print axioms QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound

#check @QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd_bound_of_modulus
#print axioms QuaternaryQuadraticForms.integralProjectiveQuadraticTrace_dvd_bound_of_modulus

#check @QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus
#print axioms QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_integral_dvd_bound_of_modulus

#check @QuaternaryQuadraticForms.homogeneousForm_isHomogeneous
#print axioms QuaternaryQuadraticForms.homogeneousForm_isHomogeneous

#check @QuaternaryQuadraticForms.homogeneousForm_coeff
#print axioms QuaternaryQuadraticForms.homogeneousForm_coeff

#check @QuaternaryQuadraticForms.homogeneousForm_coeff_eq_zero_of_degree_ne
#print axioms QuaternaryQuadraticForms.homogeneousForm_coeff_eq_zero_of_degree_ne

#check @QuaternaryQuadraticForms.homogeneousForm_coeff_formula
#print axioms QuaternaryQuadraticForms.homogeneousForm_coeff_formula

#check @QuaternaryQuadraticForms.homogeneousForm_coefficients
#print axioms QuaternaryQuadraticForms.homogeneousForm_coefficients

#check @QuaternaryQuadraticForms.homogeneousForm_map
#print axioms QuaternaryQuadraticForms.homogeneousForm_map

#check @QuaternaryQuadraticForms.homogeneousSystem_parameter_coefficients
#print axioms QuaternaryQuadraticForms.homogeneousSystem_parameter_coefficients

#check @QuaternaryQuadraticForms.homogeneous_parameter_resultants
#print axioms QuaternaryQuadraticForms.homogeneous_parameter_resultants

#check @QuaternaryQuadraticForms.rank_two_ne_iff_minors_zero
#print axioms QuaternaryQuadraticForms.rank_two_ne_iff_minors_zero

#check @QuaternaryQuadraticForms.rank_two_iff_exists_minor_ne_zero
#print axioms QuaternaryQuadraticForms.rank_two_iff_exists_minor_ne_zero

#check @QuaternaryQuadraticForms.card_badReductionIndex
#print axioms QuaternaryQuadraticForms.card_badReductionIndex

#check @QuaternaryQuadraticForms.gradientMinor_homogeneous
#print axioms QuaternaryQuadraticForms.gradientMinor_homogeneous

#check @QuaternaryQuadraticForms.badReductionSystem_homogeneous
#print axioms QuaternaryQuadraticForms.badReductionSystem_homogeneous

#check @QuaternaryQuadraticForms.badReductionSystemDegree_pos
#print axioms QuaternaryQuadraticForms.badReductionSystemDegree_pos

#check @QuaternaryQuadraticForms.matrixQuadraticPolynomial_map_ring
#print axioms QuaternaryQuadraticForms.matrixQuadraticPolynomial_map_ring

#check @QuaternaryQuadraticForms.gradientMinor_map
#print axioms QuaternaryQuadraticForms.gradientMinor_map

#check @QuaternaryQuadraticForms.badReductionSystem_map
#print axioms QuaternaryQuadraticForms.badReductionSystem_map

#check @QuaternaryQuadraticForms.eval_badReductionSystem_map
#print axioms QuaternaryQuadraticForms.eval_badReductionSystem_map

#check @QuaternaryQuadraticForms.eval_badReductionSystem_map_point
#print axioms QuaternaryQuadraticForms.eval_badReductionSystem_map_point

#check @QuaternaryQuadraticForms.eval_gradientMinor
#print axioms QuaternaryQuadraticForms.eval_gradientMinor

#check @QuaternaryQuadraticForms.badReductionSystem_zero_iff
#print axioms QuaternaryQuadraticForms.badReductionSystem_zero_iff

#check @QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff
#print axioms QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff

#check @QuaternaryQuadraticForms.exists_badReductionSystem_eval₂_zero_iff
#print axioms QuaternaryQuadraticForms.exists_badReductionSystem_eval₂_zero_iff

#check @QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff_not_goodReductionAt
#print axioms QuaternaryQuadraticForms.exists_badReductionSystem_zero_iff_not_goodReductionAt

#check @QuaternaryQuadraticForms.exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt
#print axioms QuaternaryQuadraticForms.exists_badReductionSystem_intCast_zero_iff_not_goodReductionAt

#check @QuaternaryQuadraticForms.two_le_polynomialCoefficientHeight
#print axioms QuaternaryQuadraticForms.two_le_polynomialCoefficientHeight

#check @QuaternaryQuadraticForms.natAbs_coeff_le_polynomialCoefficientHeight
#print axioms QuaternaryQuadraticForms.natAbs_coeff_le_polynomialCoefficientHeight

#check @QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow
#print axioms QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow

#check @QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow_of_forall
#print axioms QuaternaryQuadraticForms.natAbs_eval_le_coefficientSum_mul_pow_of_forall

#check @QuaternaryQuadraticForms.finite_polynomial_family_eval_bound
#print axioms QuaternaryQuadraticForms.finite_polynomial_family_eval_bound

#check @QuaternaryQuadraticForms.finite_polynomial_family_eval_bound_of_height
#print axioms QuaternaryQuadraticForms.finite_polynomial_family_eval_bound_of_height

#check @QuaternaryQuadraticForms.finite_polynomial_family_coeff_eval_bound
#print axioms QuaternaryQuadraticForms.finite_polynomial_family_coeff_eval_bound

#check @QuaternaryQuadraticForms.genericDegreeForm_homogeneous
#print axioms QuaternaryQuadraticForms.genericDegreeForm_homogeneous

#check @QuaternaryQuadraticForms.genericBadReductionSystem_homogeneous
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_homogeneous

#check @QuaternaryQuadraticForms.genericQuadricMatrix_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericQuadricMatrix_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericDegreeForm_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericDegreeForm_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericBadReductionSystem_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericBadReductionSystem_specialize
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_specialize

#check @QuaternaryQuadraticForms.genericBadReductionSystem_specialize_integral
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_specialize_integral

#check @QuaternaryQuadraticForms.genericBadReductionSystem_specialize_map
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_specialize_map

#check @QuaternaryQuadraticForms.genericBadReductionSystem_specialize_intCast
#print axioms QuaternaryQuadraticForms.genericBadReductionSystem_specialize_intCast

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_map_intCast_iff
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_map_intCast_iff

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_iff
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_iff

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_rat_iff
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_rat_iff

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_zmod_iff
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_badReductionSystem_zmod_iff

#check @QuaternaryQuadraticForms.badReduction_resultants_over_fields
#print axioms QuaternaryQuadraticForms.badReduction_resultants_over_fields

#check @QuaternaryQuadraticForms.badReduction_resultant_family
#print axioms QuaternaryQuadraticForms.badReduction_resultant_family

#check @QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor
#print axioms QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor

#check @QuaternaryQuadraticForms.badReductionPrimes_finite_of_smooth
#print axioms QuaternaryQuadraticForms.badReductionPrimes_finite_of_smooth

#check @QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor_height_bound
#print axioms QuaternaryQuadraticForms.exists_nonzero_badReduction_divisor_height_bound

#check @QuaternaryQuadraticForms.polynomialBadPrimeModulus_height_bound
#print axioms QuaternaryQuadraticForms.polynomialBadPrimeModulus_height_bound

#check @QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound
#print axioms QuaternaryQuadraticForms.badReductionPrimes_finite_and_height_bound

#check @QuaternaryQuadraticForms.quadratic_projective_trace_integer
#print axioms QuaternaryQuadraticForms.quadratic_projective_trace_integer

#check @QuaternaryQuadraticForms.quadratic_projective_trace
#print axioms QuaternaryQuadraticForms.quadratic_projective_trace

#check @QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent
#print axioms QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent

#check @QuaternaryQuadraticForms.rowTripleMinor_eq_det
#print axioms QuaternaryQuadraticForms.rowTripleMinor_eq_det

#check @QuaternaryQuadraticForms.rowTripleMinor_map
#print axioms QuaternaryQuadraticForms.rowTripleMinor_map

#check @QuaternaryQuadraticForms.rank_three_ne_iff_minors_zero
#print axioms QuaternaryQuadraticForms.rank_three_ne_iff_minors_zero

#check @QuaternaryQuadraticForms.rank_three_iff_exists_minor_ne_zero
#print axioms QuaternaryQuadraticForms.rank_three_iff_exists_minor_ne_zero

#check @QuaternaryQuadraticForms.planeEquationPolynomial_eq_planePolynomial
#print axioms QuaternaryQuadraticForms.planeEquationPolynomial_eq_planePolynomial

#check @QuaternaryQuadraticForms.eval_planeEquationPolynomial
#print axioms QuaternaryQuadraticForms.eval_planeEquationPolynomial

#check @QuaternaryQuadraticForms.planeEquationPolynomial_homogeneous
#print axioms QuaternaryQuadraticForms.planeEquationPolynomial_homogeneous

#check @QuaternaryQuadraticForms.planeEquationPolynomial_map
#print axioms QuaternaryQuadraticForms.planeEquationPolynomial_map

#check @QuaternaryQuadraticForms.gradientPlaneMinor_homogeneous
#print axioms QuaternaryQuadraticForms.gradientPlaneMinor_homogeneous

#check @QuaternaryQuadraticForms.gradientPlaneMinor_map
#print axioms QuaternaryQuadraticForms.gradientPlaneMinor_map

#check @QuaternaryQuadraticForms.eval_gradientPlaneMinor
#print axioms QuaternaryQuadraticForms.eval_gradientPlaneMinor

#check @QuaternaryQuadraticForms.card_planeReductionIndex
#print axioms QuaternaryQuadraticForms.card_planeReductionIndex

#check @QuaternaryQuadraticForms.planeReductionSystem_homogeneous
#print axioms QuaternaryQuadraticForms.planeReductionSystem_homogeneous

#check @QuaternaryQuadraticForms.planeReductionSystemDegree_pos
#print axioms QuaternaryQuadraticForms.planeReductionSystemDegree_pos

#check @QuaternaryQuadraticForms.planeReductionSystem_map
#print axioms QuaternaryQuadraticForms.planeReductionSystem_map

#check @QuaternaryQuadraticForms.eval_planeReductionSystem_map
#print axioms QuaternaryQuadraticForms.eval_planeReductionSystem_map

#check @QuaternaryQuadraticForms.planeReductionSystem_zero_iff
#print axioms QuaternaryQuadraticForms.planeReductionSystem_zero_iff

#check @QuaternaryQuadraticForms.exists_planeReductionSystem_zero_iff
#print axioms QuaternaryQuadraticForms.exists_planeReductionSystem_zero_iff

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_planeReductionSystem_iff
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_planeReductionSystem_iff

#check @QuaternaryQuadraticForms.genericPlaneDegreeForm_homogeneous
#print axioms QuaternaryQuadraticForms.genericPlaneDegreeForm_homogeneous

#check @QuaternaryQuadraticForms.genericPlaneReductionSystem_homogeneous
#print axioms QuaternaryQuadraticForms.genericPlaneReductionSystem_homogeneous

#check @QuaternaryQuadraticForms.genericPlaneQuadricMatrix_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericPlaneQuadricMatrix_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericPlaneDegreeForm_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericPlaneDegreeForm_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericPlaneNormal_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericPlaneNormal_eval₂Hom

#check @QuaternaryQuadraticForms.genericPlaneReductionSystem_map_eval₂Hom
#print axioms QuaternaryQuadraticForms.genericPlaneReductionSystem_map_eval₂Hom

#check @QuaternaryQuadraticForms.genericPlaneReductionSystem_specialize
#print axioms QuaternaryQuadraticForms.genericPlaneReductionSystem_specialize

#check @QuaternaryQuadraticForms.exceptionalPlane_resultants_over_fields
#print axioms QuaternaryQuadraticForms.exceptionalPlane_resultants_over_fields

#check @QuaternaryQuadraticForms.exceptionalPlane_resultant_family
#print axioms QuaternaryQuadraticForms.exceptionalPlane_resultant_family

#check @QuaternaryQuadraticForms.eval_specializePlaneResultant
#print axioms QuaternaryQuadraticForms.eval_specializePlaneResultant

#check @QuaternaryQuadraticForms.exceptionalPlane_specialized_resultant_family
#print axioms QuaternaryQuadraticForms.exceptionalPlane_specialized_resultant_family

#check @QuaternaryQuadraticForms.hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed
#print axioms QuaternaryQuadraticForms.hasNonzeroGeometricZero_iff_exists_zero_of_isAlgClosed

#check @QuaternaryQuadraticForms.specializePlaneResultant_map
#print axioms QuaternaryQuadraticForms.specializePlaneResultant_map

#check @QuaternaryQuadraticForms.exceptionalPlane_resultants_over_algClosed_fields
#print axioms QuaternaryQuadraticForms.exceptionalPlane_resultants_over_algClosed_fields

#check @QuaternaryQuadraticForms.exceptionalPlane_resultants_nonzero_of_transverse_witness
#print axioms QuaternaryQuadraticForms.exceptionalPlane_resultants_nonzero_of_transverse_witness

#check @QuaternaryQuadraticForms.rank_three_of_rank_two_of_tangent
#print axioms QuaternaryQuadraticForms.rank_three_of_rank_two_of_tangent

#check @QuaternaryQuadraticForms.exists_transverse_plane_of_smooth_intersection
#print axioms QuaternaryQuadraticForms.exists_transverse_plane_of_smooth_intersection

#check @QuaternaryQuadraticForms.totalDegree_eval₂_le_of_degree_one
#print axioms QuaternaryQuadraticForms.totalDegree_eval₂_le_of_degree_one

#check @QuaternaryQuadraticForms.totalDegree_specializePlaneResultant_le
#print axioms QuaternaryQuadraticForms.totalDegree_specializePlaneResultant_le

#check @QuaternaryQuadraticForms.exceptionalPlane_bounded_resultant_family
#print axioms QuaternaryQuadraticForms.exceptionalPlane_bounded_resultant_family

#check @QuaternaryQuadraticForms.exceptional_plane_polynomial_over_fields
#print axioms QuaternaryQuadraticForms.exceptional_plane_polynomial_over_fields

#check @QuaternaryQuadraticForms.exceptional_plane_polynomial
#print axioms QuaternaryQuadraticForms.exceptional_plane_polynomial

#check @QuaternaryQuadraticForms.plane_exists_nonzero_quadratic_value
#print axioms QuaternaryQuadraticForms.plane_exists_nonzero_quadratic_value

#check @QuaternaryQuadraticForms.eval_planeRestrictionPolynomial
#print axioms QuaternaryQuadraticForms.eval_planeRestrictionPolynomial

#check @QuaternaryQuadraticForms.planeRestrictionPolynomial_homogeneous
#print axioms QuaternaryQuadraticForms.planeRestrictionPolynomial_homogeneous

#check @QuaternaryQuadraticForms.planeRestrictionPolynomial_totalDegree_le
#print axioms QuaternaryQuadraticForms.planeRestrictionPolynomial_totalDegree_le

#check @QuaternaryQuadraticForms.planeRestrictionPolynomial_ne_zero
#print axioms QuaternaryQuadraticForms.planeRestrictionPolynomial_ne_zero

#check @QuaternaryQuadraticForms.exists_plane_quadratic_restriction
#print axioms QuaternaryQuadraticForms.exists_plane_quadratic_restriction

#check @QuaternaryQuadraticForms.ternary_polynomial_zero_card_le
#print axioms QuaternaryQuadraticForms.ternary_polynomial_zero_card_le

#check @QuaternaryQuadraticForms.planeSection_affine_card_eq
#print axioms QuaternaryQuadraticForms.planeSection_affine_card_eq

#check @QuaternaryQuadraticForms.planeSection_affine_card_le
#print axioms QuaternaryQuadraticForms.planeSection_affine_card_le

#check @QuaternaryQuadraticForms.planeSection_card_le
#print axioms QuaternaryQuadraticForms.planeSection_card_le

#check @QuaternaryQuadraticForms.projectiveSectionTrace_norm_le
#print axioms QuaternaryQuadraticForms.projectiveSectionTrace_norm_le

#check @QuaternaryQuadraticForms.fourier_generic_constant_bound
#print axioms QuaternaryQuadraticForms.fourier_generic_constant_bound

#check @QuaternaryQuadraticForms.fourier_exceptional_constant_bound
#print axioms QuaternaryQuadraticForms.fourier_exceptional_constant_bound

#check @QuaternaryQuadraticForms.fourier_zero_constant_bound
#print axioms QuaternaryQuadraticForms.fourier_zero_constant_bound

#check @QuaternaryQuadraticForms.rpow_three_halves_eq_mul_sqrt
#print axioms QuaternaryQuadraticForms.rpow_three_halves_eq_mul_sqrt

#check @QuaternaryQuadraticForms.fourierSum_norm_le_section_and_trace
#print axioms QuaternaryQuadraticForms.fourierSum_norm_le_section_and_trace

#check @QuaternaryQuadraticForms.fourierSum_zero_norm
#print axioms QuaternaryQuadraticForms.fourierSum_zero_norm

#check @QuaternaryQuadraticForms.fourierSum_generic_bound
#print axioms QuaternaryQuadraticForms.fourierSum_generic_bound

#check @QuaternaryQuadraticForms.fourierSum_zero_bound
#print axioms QuaternaryQuadraticForms.fourierSum_zero_bound

#check @QuaternaryQuadraticForms.fourierSum_nonzero_bound
#print axioms QuaternaryQuadraticForms.fourierSum_nonzero_bound

#check @QuaternaryQuadraticForms.fourierSum_bound_prime_field
#print axioms QuaternaryQuadraticForms.fourierSum_bound_prime_field

#check @QuaternaryQuadraticForms.fourier_bound
#print axioms QuaternaryQuadraticForms.fourier_bound

#check @QuaternaryQuadraticForms.uniform_polynomial_fourier_bound
#print axioms QuaternaryQuadraticForms.uniform_polynomial_fourier_bound

#check @QuaternaryQuadraticForms.diagonalQuadraticPolynomial_eq_sum
#print axioms QuaternaryQuadraticForms.diagonalQuadraticPolynomial_eq_sum

#check @QuaternaryQuadraticForms.diagonalPairProduct_map
#print axioms QuaternaryQuadraticForms.diagonalPairProduct_map

#check @QuaternaryQuadraticForms.diagonalPairProduct_ne_zero_iff
#print axioms QuaternaryQuadraticForms.diagonalPairProduct_ne_zero_iff

#check @QuaternaryQuadraticForms.diagonal_pair_difference_ne_zero
#print axioms QuaternaryQuadraticForms.diagonal_pair_difference_ne_zero

#check @QuaternaryQuadraticForms.diagonalQuadraticPolynomial_map
#print axioms QuaternaryQuadraticForms.diagonalQuadraticPolynomial_map

#check @QuaternaryQuadraticForms.diagonal_coefficients_ne_zero
#print axioms QuaternaryQuadraticForms.diagonal_coefficients_ne_zero

#check @QuaternaryQuadraticForms.quadraticBadPrimeModulus_diagonal
#print axioms QuaternaryQuadraticForms.quadraticBadPrimeModulus_diagonal

#check @QuaternaryQuadraticForms.diagonal_bad_modulus_product
#print axioms QuaternaryQuadraticForms.diagonal_bad_modulus_product

#check @QuaternaryQuadraticForms.eval_diagonalQuadraticPolynomial
#print axioms QuaternaryQuadraticForms.eval_diagonalQuadraticPolynomial

#check @QuaternaryQuadraticForms.polynomialGradient_diagonalQuadraticPolynomial
#print axioms QuaternaryQuadraticForms.polynomialGradient_diagonalQuadraticPolynomial

#check @QuaternaryQuadraticForms.diagonal_gradient_minor
#print axioms QuaternaryQuadraticForms.diagonal_gradient_minor

#check @QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank
#print axioms QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank

#check @QuaternaryQuadraticForms.exists_diagonal_rank_failure_of_pair_eq_zero
#print axioms QuaternaryQuadraticForms.exists_diagonal_rank_failure_of_pair_eq_zero

#check @QuaternaryQuadraticForms.not_diagonal_projectiveIntersectionTransverseRank_of_pair_eq_zero
#print axioms QuaternaryQuadraticForms.not_diagonal_projectiveIntersectionTransverseRank_of_pair_eq_zero

#check @QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff
#print axioms QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff

#check @QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff_pairProduct_ne_zero
#print axioms QuaternaryQuadraticForms.diagonal_projectiveIntersectionTransverseRank_iff_pairProduct_ne_zero

#check @QuaternaryQuadraticForms.diagonal_smooth_characteristicZero
#print axioms QuaternaryQuadraticForms.diagonal_smooth_characteristicZero

#check @QuaternaryQuadraticForms.diagonal_badReductionAt_iff
#print axioms QuaternaryQuadraticForms.diagonal_badReductionAt_iff

#check @QuaternaryQuadraticForms.badReductionPrimes_finite_of_iff_dvd
#print axioms QuaternaryQuadraticForms.badReductionPrimes_finite_of_iff_dvd

#check @QuaternaryQuadraticForms.badReductionPrimes_toFinset_eq_primeFactors_sdiff
#print axioms QuaternaryQuadraticForms.badReductionPrimes_toFinset_eq_primeFactors_sdiff

#check @QuaternaryQuadraticForms.polynomialBadPrimeModulus_eq_primeRadical_of_bad_iff
#print axioms QuaternaryQuadraticForms.polynomialBadPrimeModulus_eq_primeRadical_of_bad_iff

#check @QuaternaryQuadraticForms.diagonal_badReductionPrimes_finite
#print axioms QuaternaryQuadraticForms.diagonal_badReductionPrimes_finite

#check @QuaternaryQuadraticForms.diagonal_badPrimeModulus
#print axioms QuaternaryQuadraticForms.diagonal_badPrimeModulus

#check @QuaternaryQuadraticForms.diagonal_bad_primes
#print axioms QuaternaryQuadraticForms.diagonal_bad_primes

#check @QuaternaryQuadraticForms.nonseparable_cubic_factorization
#print axioms QuaternaryQuadraticForms.nonseparable_cubic_factorization

#check @QuaternaryQuadraticForms.quadraticChar_repeated_cubic_sum
#print axioms QuaternaryQuadraticForms.quadraticChar_repeated_cubic_sum

#check @QuaternaryQuadraticForms.quadraticChar_nonseparable_cubic_sum_norm_le_one
#print axioms QuaternaryQuadraticForms.quadraticChar_nonseparable_cubic_sum_norm_le_one

#check @QuaternaryQuadraticForms.quadraticChar_cubic_sum_norm_le
#print axioms QuaternaryQuadraticForms.quadraticChar_cubic_sum_norm_le

#check @QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_norm_le
#print axioms QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_norm_le

#check @QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_four_norm_le
#print axioms QuaternaryQuadraticForms.quadraticChar_cubic_sum_sdiff_four_norm_le

#check @QuaternaryQuadraticForms.eval_diagonalPencilPhi
#print axioms QuaternaryQuadraticForms.eval_diagonalPencilPhi

#check @QuaternaryQuadraticForms.diagonalPencilCoeff_map
#print axioms QuaternaryQuadraticForms.diagonalPencilCoeff_map

#check @QuaternaryQuadraticForms.diagonalKappa_map
#print axioms QuaternaryQuadraticForms.diagonalKappa_map

#check @QuaternaryQuadraticForms.diagonalPencilPhi_map
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_map

#check @QuaternaryQuadraticForms.diagonalPencilNu_map
#print axioms QuaternaryQuadraticForms.diagonalPencilNu_map

#check @QuaternaryQuadraticForms.diagonalPencilCoeff_eq_zero_iff
#print axioms QuaternaryQuadraticForms.diagonalPencilCoeff_eq_zero_iff

#check @QuaternaryQuadraticForms.diagonalPencilCoeff_at_own_root
#print axioms QuaternaryQuadraticForms.diagonalPencilCoeff_at_own_root

#check @QuaternaryQuadraticForms.diagonalPencilCoeff_at_root
#print axioms QuaternaryQuadraticForms.diagonalPencilCoeff_at_root

#check @QuaternaryQuadraticForms.diagonalPencilCoeff_at_root_ne_zero
#print axioms QuaternaryQuadraticForms.diagonalPencilCoeff_at_root_ne_zero

#check @QuaternaryQuadraticForms.diagonalPencilRoot_injective
#print axioms QuaternaryQuadraticForms.diagonalPencilRoot_injective

#check @QuaternaryQuadraticForms.five_le_of_diagonalPencil_roots
#print axioms QuaternaryQuadraticForms.five_le_of_diagonalPencil_roots

#check @QuaternaryQuadraticForms.diagonalPencilDelta_ne_zero
#print axioms QuaternaryQuadraticForms.diagonalPencilDelta_ne_zero

#check @QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_ne_zero
#print axioms QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_ne_zero

#check @QuaternaryQuadraticForms.diagonalPencilPhi_div_delta
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_div_delta

#check @QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_eq
#print axioms QuaternaryQuadraticForms.diagonalPencilDeltaAtRoot_eq

#check @QuaternaryQuadraticForms.neg_diagonalPencilDeltaAtRoot_eq
#print axioms QuaternaryQuadraticForms.neg_diagonalPencilDeltaAtRoot_eq

#check @QuaternaryQuadraticForms.diagonalKappa_ne_zero
#print axioms QuaternaryQuadraticForms.diagonalKappa_ne_zero

#check @QuaternaryQuadraticForms.diagonalPencilW_eq
#print axioms QuaternaryQuadraticForms.diagonalPencilW_eq

#check @QuaternaryQuadraticForms.diagonal_projectiveTrace_eq
#print axioms QuaternaryQuadraticForms.diagonal_projectiveTrace_eq

#check @QuaternaryQuadraticForms.diagonal_projectiveQuadraticTrace_eq
#print axioms QuaternaryQuadraticForms.diagonal_projectiveQuadraticTrace_eq

#check @QuaternaryQuadraticForms.diagonal_fourier_generic_bound_sqrt
#print axioms QuaternaryQuadraticForms.diagonal_fourier_generic_bound_sqrt

#check @QuaternaryQuadraticForms.diagonal_fourier_generic_bound
#print axioms QuaternaryQuadraticForms.diagonal_fourier_generic_bound

#check @QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_le
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_le

#check @QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three

#check @QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three_eq_eval
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_coeff_three_eq_eval

#check @QuaternaryQuadraticForms.eval_diagonalPencilPhi_eq_dual
#print axioms QuaternaryQuadraticForms.eval_diagonalPencilPhi_eq_dual

#check @QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_eq_three
#print axioms QuaternaryQuadraticForms.diagonalPencilPhi_natDegree_eq_three

#check @QuaternaryQuadraticForms.diagonalPencilRawSum_regular
#print axioms QuaternaryQuadraticForms.diagonalPencilRawSum_regular

#check @QuaternaryQuadraticForms.diagonalPencilRawSum_singular
#print axioms QuaternaryQuadraticForms.diagonalPencilRawSum_singular

#check @QuaternaryQuadraticForms.mem_diagonalPencilRoots
#print axioms QuaternaryQuadraticForms.mem_diagonalPencilRoots

#check @QuaternaryQuadraticForms.diagonalPencilRoots_card_le
#print axioms QuaternaryQuadraticForms.diagonalPencilRoots_card_le

#check @QuaternaryQuadraticForms.diagonalPencil_sum_split
#print axioms QuaternaryQuadraticForms.diagonalPencil_sum_split

#check @QuaternaryQuadraticForms.diagonal_fourier_pencil_formula
#print axioms QuaternaryQuadraticForms.diagonal_fourier_pencil_formula

#check @QuaternaryQuadraticForms.diagonalPencil_reduced_data
#print axioms QuaternaryQuadraticForms.diagonalPencil_reduced_data

#check @QuaternaryQuadraticForms.diagonalPencil_dual_map
#print axioms QuaternaryQuadraticForms.diagonalPencil_dual_map

#check @QuaternaryQuadraticForms.diagonalPencil_generic_reduction
#print axioms QuaternaryQuadraticForms.diagonalPencil_generic_reduction

#check @QuaternaryQuadraticForms.integral_diagonal_fourier_pencil_formula
#print axioms QuaternaryQuadraticForms.integral_diagonal_fourier_pencil_formula

#check @QuaternaryQuadraticForms.integral_diagonal_projectiveTrace_eq
#print axioms QuaternaryQuadraticForms.integral_diagonal_projectiveTrace_eq

#check @QuaternaryQuadraticForms.integral_diagonal_fourier_bound
#print axioms QuaternaryQuadraticForms.integral_diagonal_fourier_bound

#check @QuaternaryQuadraticForms.diagonal_pencil
#print axioms QuaternaryQuadraticForms.diagonal_pencil

#check @QuaternaryQuadraticForms.primeQuadraticGauss_phase_expansion
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_phase_expansion

#check @QuaternaryQuadraticForms.fourierSum_quadraticGauss_expansion
#print axioms QuaternaryQuadraticForms.fourierSum_quadraticGauss_expansion

#check @QuaternaryQuadraticForms.diagonal_fourier_pencil_expansion
#print axioms QuaternaryQuadraticForms.diagonal_fourier_pencil_expansion

#check @QuaternaryQuadraticForms.stdAddChar_orthogonality
#print axioms QuaternaryQuadraticForms.stdAddChar_orthogonality

#check @QuaternaryQuadraticForms.fourierSum_additive_expansion
#print axioms QuaternaryQuadraticForms.fourierSum_additive_expansion

#check @QuaternaryQuadraticForms.stdAddChar_sum
#print axioms QuaternaryQuadraticForms.stdAddChar_sum

#check @QuaternaryQuadraticForms.diagonal_exponential_sum_factorization
#print axioms QuaternaryQuadraticForms.diagonal_exponential_sum_factorization

#check @QuaternaryQuadraticForms.complexQuadraticChar_sq_apply
#print axioms QuaternaryQuadraticForms.complexQuadraticChar_sq_apply

#check @QuaternaryQuadraticForms.primeQuadraticGauss_ne_zero
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_ne_zero

#check @QuaternaryQuadraticForms.primeQuadraticGauss_sq
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_sq

#check @QuaternaryQuadraticForms.primeQuadraticGauss_fourth
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_fourth

#check @QuaternaryQuadraticForms.primeQuadraticGauss_inversion
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_inversion

#check @QuaternaryQuadraticForms.primeQuadraticGauss_units_inversion
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_units_inversion

#check @QuaternaryQuadraticForms.primeQuadraticGauss_units_div_inversion
#print axioms QuaternaryQuadraticForms.primeQuadraticGauss_units_div_inversion

#check @QuaternaryQuadraticForms.primeQuadraticExponentialSum_zero
#print axioms QuaternaryQuadraticForms.primeQuadraticExponentialSum_zero

#check @QuaternaryQuadraticForms.primeQuadraticExponentialSum_unshifted
#print axioms QuaternaryQuadraticForms.primeQuadraticExponentialSum_unshifted

#check @QuaternaryQuadraticForms.primeQuadraticExponentialSum_of_ne_zero
#print axioms QuaternaryQuadraticForms.primeQuadraticExponentialSum_of_ne_zero

#check @QuaternaryQuadraticForms.primeRamanujan_eq
#print axioms QuaternaryQuadraticForms.primeRamanujan_eq

#check @QuaternaryQuadraticForms.primeRamanujan_mul
#print axioms QuaternaryQuadraticForms.primeRamanujan_mul

#check @QuaternaryQuadraticForms.primeRamanujan_inverse_sum
#print axioms QuaternaryQuadraticForms.primeRamanujan_inverse_sum

#check @QuaternaryQuadraticForms.primeRamanujan_reciprocal_phase
#print axioms QuaternaryQuadraticForms.primeRamanujan_reciprocal_phase

#check @QuaternaryQuadraticForms.scaledChineseRemainder_fst
#print axioms QuaternaryQuadraticForms.scaledChineseRemainder_fst

#check @QuaternaryQuadraticForms.scaledChineseRemainder_snd
#print axioms QuaternaryQuadraticForms.scaledChineseRemainder_snd

#check @QuaternaryQuadraticForms.scaledChineseRemainder_intCast
#print axioms QuaternaryQuadraticForms.scaledChineseRemainder_intCast

#check @QuaternaryQuadraticForms.scaledChineseRemainder_apply
#print axioms QuaternaryQuadraticForms.scaledChineseRemainder_apply

#check @QuaternaryQuadraticForms.scaledChineseRemainderUnits_coe
#print axioms QuaternaryQuadraticForms.scaledChineseRemainderUnits_coe

#check @QuaternaryQuadraticForms.scaledChineseRemainderUnits_apply
#print axioms QuaternaryQuadraticForms.scaledChineseRemainderUnits_apply

#check @QuaternaryQuadraticForms.scaledChineseRemainderVector_apply
#print axioms QuaternaryQuadraticForms.scaledChineseRemainderVector_apply

#check @QuaternaryQuadraticForms.stdAddChar_scaledChineseRemainder
#print axioms QuaternaryQuadraticForms.stdAddChar_scaledChineseRemainder

#check @QuaternaryQuadraticForms.stdAddChar_mul_modulus
#print axioms QuaternaryQuadraticForms.stdAddChar_mul_modulus

#check @QuaternaryQuadraticForms.stdAddChar_crt_split
#print axioms QuaternaryQuadraticForms.stdAddChar_crt_split

#check @QuaternaryQuadraticForms.stdAddChar_modulus_one
#print axioms QuaternaryQuadraticForms.stdAddChar_modulus_one

#check @QuaternaryQuadraticForms.residueLift_cast
#print axioms QuaternaryQuadraticForms.residueLift_cast

#check @QuaternaryQuadraticForms.integralQuadraticValue_eq_eval
#print axioms QuaternaryQuadraticForms.integralQuadraticValue_eq_eval

#check @QuaternaryQuadraticForms.matrixQuadraticValue_map
#print axioms QuaternaryQuadraticForms.matrixQuadraticValue_map

#check @QuaternaryQuadraticForms.matrixQuadraticValue_mul
#print axioms QuaternaryQuadraticForms.matrixQuadraticValue_mul

#check @QuaternaryQuadraticForms.integralQuadraticValue_mul
#print axioms QuaternaryQuadraticForms.integralQuadraticValue_mul

#check @QuaternaryQuadraticForms.integralQuadraticValue_congr_mod
#print axioms QuaternaryQuadraticForms.integralQuadraticValue_congr_mod

#check @QuaternaryQuadraticForms.integralQuadraticValue_dvd_congr
#print axioms QuaternaryQuadraticForms.integralQuadraticValue_dvd_congr

#check @QuaternaryQuadraticForms.dotProduct_intCast
#print axioms QuaternaryQuadraticForms.dotProduct_intCast

#check @QuaternaryQuadraticForms.dotProduct_congr_mod
#print axioms QuaternaryQuadraticForms.dotProduct_congr_mod

#check @QuaternaryQuadraticForms.mixedIntegerSummand_crt
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_crt

#check @QuaternaryQuadraticForms.mixedCompleteSum_crt
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_crt

#check @QuaternaryQuadraticForms.unweightedCompleteSum_mul
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_mul

#check @QuaternaryQuadraticForms.constrainedFourierSum_mul
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_mul

#check @QuaternaryQuadraticForms.constrainedFourierSum_primeFactors
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_primeFactors

#check @QuaternaryQuadraticForms.mixedIntegerSummand_inverse_scale
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_inverse_scale

#check @QuaternaryQuadraticForms.mixedCompleteSum_isUnit_frequency
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_isUnit_frequency

#check @QuaternaryQuadraticForms.mixedCompleteSum_unit_frequency
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_unit_frequency

#check @QuaternaryQuadraticForms.mixedCompleteSum_one_left
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_one_left

#check @QuaternaryQuadraticForms.mixedCompleteSum_one_right
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_one_right

#check @QuaternaryQuadraticForms.unweightedCompleteSum_one
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_one

#check @QuaternaryQuadraticForms.constrainedFourierSum_one
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_one

#check @QuaternaryQuadraticForms.mixedCompleteSum_one_one
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_one_one

#check @QuaternaryQuadraticForms.constrainedFourierSum_prime
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_prime

#check @QuaternaryQuadraticForms.constrainedFourierSum_eq_integralFourierSum
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_eq_integralFourierSum

#check @QuaternaryQuadraticForms.constrainedFourierSum_polynomial_character
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_polynomial_character

#check @QuaternaryQuadraticForms.complete_sum_crt
#print axioms QuaternaryQuadraticForms.complete_sum_crt

#check @QuaternaryQuadraticForms.source_mixedCompleteSum_crt
#print axioms QuaternaryQuadraticForms.source_mixedCompleteSum_crt

#check @QuaternaryQuadraticForms.source_mixedCompleteSum_unit_frequency
#print axioms QuaternaryQuadraticForms.source_mixedCompleteSum_unit_frequency

#check @QuaternaryQuadraticForms.source_complete_sum_crt
#print axioms QuaternaryQuadraticForms.source_complete_sum_crt

#check @QuaternaryQuadraticForms.mixedIntegerSummand_a_congr
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_a_congr

#check @QuaternaryQuadraticForms.mixedIntegerSummand_x_congr
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_x_congr

#check @QuaternaryQuadraticForms.mixedIntegerSummand_congr
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_congr

#check @QuaternaryQuadraticForms.compositeWeight_one
#print axioms QuaternaryQuadraticForms.compositeWeight_one

#check @QuaternaryQuadraticForms.compositeWeight_prime
#print axioms QuaternaryQuadraticForms.compositeWeight_prime

#check @QuaternaryQuadraticForms.compositeWeight_congr
#print axioms QuaternaryQuadraticForms.compositeWeight_congr

#check @QuaternaryQuadraticForms.compositeWeight_congr_of_dvd_sub
#print axioms QuaternaryQuadraticForms.compositeWeight_congr_of_dvd_sub

#check @QuaternaryQuadraticForms.compositeWeight_add_modulus
#print axioms QuaternaryQuadraticForms.compositeWeight_add_modulus

#check @QuaternaryQuadraticForms.compositeWeight_congr_mod
#print axioms QuaternaryQuadraticForms.compositeWeight_congr_mod

#check @QuaternaryQuadraticForms.compositeWeight_mul
#print axioms QuaternaryQuadraticForms.compositeWeight_mul

#check @QuaternaryQuadraticForms.compositeWeight_smul_of_nonzero
#print axioms QuaternaryQuadraticForms.compositeWeight_smul_of_nonzero

#check @QuaternaryQuadraticForms.compositeWeight_smul
#print axioms QuaternaryQuadraticForms.compositeWeight_smul

#check @QuaternaryQuadraticForms.compositeWeight_smul_of_isUnit
#print axioms QuaternaryQuadraticForms.compositeWeight_smul_of_isUnit

#check @QuaternaryQuadraticForms.compositeWeight_mod_one
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_one

#check @QuaternaryQuadraticForms.compositeWeight_mod_eq_of_lift
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_eq_of_lift

#check @QuaternaryQuadraticForms.compositeWeight_mod_intCast
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_intCast

#check @QuaternaryQuadraticForms.compositeWeight_mod_prime
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_prime

#check @QuaternaryQuadraticForms.compositeWeight_mod_cast
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_cast

#check @QuaternaryQuadraticForms.compositeWeight_mod_units_smul
#print axioms QuaternaryQuadraticForms.compositeWeight_mod_units_smul

#check @QuaternaryQuadraticForms.mixedPhase_intCast_lift_independent
#print axioms QuaternaryQuadraticForms.mixedPhase_intCast_lift_independent

#check @QuaternaryQuadraticForms.mixedPhase_lift_independent
#print axioms QuaternaryQuadraticForms.mixedPhase_lift_independent

#check @QuaternaryQuadraticForms.mixedPhase_crt_intCast
#print axioms QuaternaryQuadraticForms.mixedPhase_crt_intCast

#check @QuaternaryQuadraticForms.mixedPhase_crt
#print axioms QuaternaryQuadraticForms.mixedPhase_crt

#check @QuaternaryQuadraticForms.extendPrimeWeights_apply
#print axioms QuaternaryQuadraticForms.extendPrimeWeights_apply

#check @QuaternaryQuadraticForms.primeWeightsInvariant_extend
#print axioms QuaternaryQuadraticForms.primeWeightsInvariant_extend

#check @QuaternaryQuadraticForms.compositeWeight_extend
#print axioms QuaternaryQuadraticForms.compositeWeight_extend

#check @QuaternaryQuadraticForms.quadraticGaussSum_reciprocal_phase_sum
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_reciprocal_phase_sum

#check @QuaternaryQuadraticForms.sum_quadraticGaussSum_of_constant
#print axioms QuaternaryQuadraticForms.sum_quadraticGaussSum_of_constant

#check @QuaternaryQuadraticForms.unweightedCompleteSum_of_constant_gauss
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_of_constant_gauss

#check @QuaternaryQuadraticForms.quadraticGaussSum_prime_zero_frequency
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_prime_zero_frequency

#check @QuaternaryQuadraticForms.quadraticGaussSum_prime_all_scalars
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_prime_all_scalars

#check @QuaternaryQuadraticForms.adjugateQuadraticValue_intCast
#print axioms QuaternaryQuadraticForms.adjugateQuadraticValue_intCast

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_shift
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_shift

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_shift_prime_power
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_shift_prime_power

#check @QuaternaryQuadraticForms.integralQuadraticValue_residueLift
#print axioms QuaternaryQuadraticForms.integralQuadraticValue_residueLift

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_eq_lift_sum
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_eq_lift_sum

#check @QuaternaryQuadraticForms.quadraticGaussSum_zero
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_zero

#check @QuaternaryQuadraticForms.quadraticGaussSum_modulus_one
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_modulus_one

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_modulus_one
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_modulus_one

#check @QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_quadraticGaussSum
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_quadraticGaussSum

#check @QuaternaryQuadraticForms.matrix_quadratic_square_completion
#print axioms QuaternaryQuadraticForms.matrix_quadratic_square_completion

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power_pure
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power_pure

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_prime_power

#check @QuaternaryQuadraticForms.quadraticGaussSum_prime_power_units_pure
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_prime_power_units_pure

#check @QuaternaryQuadraticForms.stdAddChar_vector_orthogonality
#print axioms QuaternaryQuadraticForms.stdAddChar_vector_orthogonality

#check @QuaternaryQuadraticForms.matrix_bilinear_character_sum
#print axioms QuaternaryQuadraticForms.matrix_bilinear_character_sum

#check @QuaternaryQuadraticForms.primeSquare_digit_phase_intCast
#print axioms QuaternaryQuadraticForms.primeSquare_digit_phase_intCast

#check @QuaternaryQuadraticForms.primeSquare_digit_phase
#print axioms QuaternaryQuadraticForms.primeSquare_digit_phase

#check @QuaternaryQuadraticForms.primeSquare_digit_orthogonality
#print axioms QuaternaryQuadraticForms.primeSquare_digit_orthogonality

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_primeSquare_mul
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_primeSquare_mul

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_primePower_recurrence
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_primePower_recurrence

#check @QuaternaryQuadraticForms.prime_power_gauss
#print axioms QuaternaryQuadraticForms.prime_power_gauss

#check @QuaternaryQuadraticForms.residueDigitsEquiv_val
#print axioms QuaternaryQuadraticForms.residueDigitsEquiv_val

#check @QuaternaryQuadraticForms.residueDigitsEquiv_apply
#print axioms QuaternaryQuadraticForms.residueDigitsEquiv_apply

#check @QuaternaryQuadraticForms.residueDigitsVectorEquiv_apply
#print axioms QuaternaryQuadraticForms.residueDigitsVectorEquiv_apply

#check @QuaternaryQuadraticForms.sum_residueLift_digits
#print axioms QuaternaryQuadraticForms.sum_residueLift_digits

#check @QuaternaryQuadraticForms.sum_residueLift_three_digits
#print axioms QuaternaryQuadraticForms.sum_residueLift_three_digits

#check @QuaternaryQuadraticForms.intCast_isUnit_prime_pow
#print axioms QuaternaryQuadraticForms.intCast_isUnit_prime_pow

#check @QuaternaryQuadraticForms.goodPrime_not_dvd_det
#print axioms QuaternaryQuadraticForms.goodPrime_not_dvd_det

#check @QuaternaryQuadraticForms.goodPrime_two_isUnit_prime_pow
#print axioms QuaternaryQuadraticForms.goodPrime_two_isUnit_prime_pow

#check @QuaternaryQuadraticForms.goodPrime_det_isUnit_prime_pow
#print axioms QuaternaryQuadraticForms.goodPrime_det_isUnit_prime_pow

#check @QuaternaryQuadraticForms.quadraticGaussSum_shift_of_inverse
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_shift_of_inverse

#check @QuaternaryQuadraticForms.quadraticGaussSum_shift
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_shift

#check @QuaternaryQuadraticForms.quadraticGaussSum_shift_of_units
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_shift_of_units

#check @QuaternaryQuadraticForms.affineQuadric_card_additive
#print axioms QuaternaryQuadraticForms.affineQuadric_card_additive

#check @QuaternaryQuadraticForms.affineQuadric_card_projective
#print axioms QuaternaryQuadraticForms.affineQuadric_card_projective

#check @QuaternaryQuadraticForms.affineQuadric_card_complex
#print axioms QuaternaryQuadraticForms.affineQuadric_card_complex

#check @QuaternaryQuadraticForms.affineQuadric_card
#print axioms QuaternaryQuadraticForms.affineQuadric_card

#check @QuaternaryQuadraticForms.projectiveQuadric_card_complex
#print axioms QuaternaryQuadraticForms.projectiveQuadric_card_complex

#check @QuaternaryQuadraticForms.projectiveQuadric_card
#print axioms QuaternaryQuadraticForms.projectiveQuadric_card

#check @QuaternaryQuadraticForms.integral_projectiveQuadric_card
#print axioms QuaternaryQuadraticForms.integral_projectiveQuadric_card

#check @QuaternaryQuadraticForms.integralRamanujanSum_eq_lift_sum
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_eq_lift_sum

#check @QuaternaryQuadraticForms.residueRamanujanSum_prime
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_prime

#check @QuaternaryQuadraticForms.residueRamanujanSum_modulus_one
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_modulus_one

#check @QuaternaryQuadraticForms.integralRamanujanSum_modulus_one
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_modulus_one

#check @QuaternaryQuadraticForms.residueRamanujanSum_units_mul
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_units_mul

#check @QuaternaryQuadraticForms.residueRamanujanSum_mul
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_mul

#check @QuaternaryQuadraticForms.residueRamanujanSum_inverse_sum
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_inverse_sum

#check @QuaternaryQuadraticForms.residueRamanujanSum_reciprocal_phase
#print axioms QuaternaryQuadraticForms.residueRamanujanSum_reciprocal_phase

#check @QuaternaryQuadraticForms.unweightedCompleteSum_prime_power
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_prime_power

#check @QuaternaryQuadraticForms.stdAddChar_residue_vector_orthogonality
#print axioms QuaternaryQuadraticForms.stdAddChar_residue_vector_orthogonality

#check @QuaternaryQuadraticForms.quadraticGaussSum_mul_conj_eq_kernel_sum
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_mul_conj_eq_kernel_sum

#check @QuaternaryQuadraticForms.quadraticGaussSum_norm_sq_le_kernel_card
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_norm_sq_le_kernel_card

#check @QuaternaryQuadraticForms.mem_matrixResidueKernel
#print axioms QuaternaryQuadraticForms.mem_matrixResidueKernel

#check @QuaternaryQuadraticForms.matrixResidueKernel_card_le_det
#print axioms QuaternaryQuadraticForms.matrixResidueKernel_card_le_det

#check @QuaternaryQuadraticForms.quaternary_det_two_smul
#print axioms QuaternaryQuadraticForms.quaternary_det_two_smul

#check @QuaternaryQuadraticForms.quaternary_det_two_smul_natAbs
#print axioms QuaternaryQuadraticForms.quaternary_det_two_smul_natAbs

#check @QuaternaryQuadraticForms.gauss_norm_le_of_sq_le
#print axioms QuaternaryQuadraticForms.gauss_norm_le_of_sq_le

#check @QuaternaryQuadraticForms.zmod_card_units_le
#print axioms QuaternaryQuadraticForms.zmod_card_units_le

#check @QuaternaryQuadraticForms.reduceQuadraticMatrix_two_smul
#print axioms QuaternaryQuadraticForms.reduceQuadraticMatrix_two_smul

#check @QuaternaryQuadraticForms.matrixResidueKernel_two_smul
#print axioms QuaternaryQuadraticForms.matrixResidueKernel_two_smul

#check @QuaternaryQuadraticForms.unweightedCompleteSum_norm_le_of_gauss_bound
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_norm_le_of_gauss_bound

#check @QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_sq_le
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_sq_le

#check @QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_le
#print axioms QuaternaryQuadraticForms.quadraticGaussSum_integral_norm_le

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_norm_le
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_norm_le

#check @QuaternaryQuadraticForms.unweightedCompleteSum_norm_le
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_norm_le

#check @QuaternaryQuadraticForms.bad_prime_bound
#print axioms QuaternaryQuadraticForms.bad_prime_bound

#check @QuaternaryQuadraticForms.residueUnitDigitsEquiv_val
#print axioms QuaternaryQuadraticForms.residueUnitDigitsEquiv_val

#check @QuaternaryQuadraticForms.sum_units_residueLift_digits
#print axioms QuaternaryQuadraticForms.sum_units_residueLift_digits

#check @QuaternaryQuadraticForms.ramified_complete_sum
#print axioms QuaternaryQuadraticForms.ramified_complete_sum

#check @QuaternaryQuadraticForms.source_ramified_complete_sum
#print axioms QuaternaryQuadraticForms.source_ramified_complete_sum

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_eq_prime_mul_mixedCompleteSum

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_lift
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_lift

#check @QuaternaryQuadraticForms.source_not_dvd_quadraticBadPrimeModulus
#print axioms QuaternaryQuadraticForms.source_not_dvd_quadraticBadPrimeModulus

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_of_gauss_factor
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_of_gauss_factor

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_factor
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power_factor

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_prime_power

#check @QuaternaryQuadraticForms.stationary_weight_eq_adjugate
#print axioms QuaternaryQuadraticForms.stationary_weight_eq_adjugate

#check @QuaternaryQuadraticForms.weightedIntegralGaussSum_mul_extract
#print axioms QuaternaryQuadraticForms.weightedIntegralGaussSum_mul_extract

#check @QuaternaryQuadraticForms.weightedIntegralGaussSum_prime_power_extract
#print axioms QuaternaryQuadraticForms.weightedIntegralGaussSum_prime_power_extract

#check @QuaternaryQuadraticForms.weightedGauss_digit_phase
#print axioms QuaternaryQuadraticForms.weightedGauss_digit_phase

#check @QuaternaryQuadraticForms.weightedIntegralGaussSum_stationary_expansion
#print axioms QuaternaryQuadraticForms.weightedIntegralGaussSum_stationary_expansion

#check @QuaternaryQuadraticForms.weightedIntegralGaussSum_one
#print axioms QuaternaryQuadraticForms.weightedIntegralGaussSum_one

#check @QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_integralQuadraticGaussSum
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_eq_sum_integralQuadraticGaussSum

#check @QuaternaryQuadraticForms.primeWeightedCompleteSum_one
#print axioms QuaternaryQuadraticForms.primeWeightedCompleteSum_one

#check @QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_dual_cone
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_dual_cone

#check @QuaternaryQuadraticForms.mixedCompleteSum_dual_cone
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_dual_cone

#check @QuaternaryQuadraticForms.globalQuadraticChar_one
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_one

#check @QuaternaryQuadraticForms.globalQuadraticChar_mul
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_mul

#check @QuaternaryQuadraticForms.globalQuadraticChar_prime
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_prime

#check @QuaternaryQuadraticForms.globalQuadraticChar_prime_power
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_prime_power

#check @QuaternaryQuadraticForms.globalQuadraticChar_sq
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_sq

#check @QuaternaryQuadraticForms.monoidHom_eq_globalQuadraticChar
#print axioms QuaternaryQuadraticForms.monoidHom_eq_globalQuadraticChar

#check @QuaternaryQuadraticForms.globalQuadraticChar_eq_dirichletCharacter
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_eq_dirichletCharacter

#check @QuaternaryQuadraticForms.mixedCompleteSum_good_modulus
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_good_modulus

#check @QuaternaryQuadraticForms.source_mixedCompleteSum_good_modulus
#print axioms QuaternaryQuadraticForms.source_mixedCompleteSum_good_modulus

#check @QuaternaryQuadraticForms.source_mixedCompleteSum_dual_cone
#print axioms QuaternaryQuadraticForms.source_mixedCompleteSum_dual_cone

#check @QuaternaryQuadraticForms.source_good_global_complete_sum
#print axioms QuaternaryQuadraticForms.source_good_global_complete_sum

#check @QuaternaryQuadraticForms.unweightedCompleteSum_good_modulus
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_good_modulus

#check @QuaternaryQuadraticForms.exists_modulus_prime_split
#print axioms QuaternaryQuadraticForms.exists_modulus_prime_split

#check @QuaternaryQuadraticForms.coprime_of_prime_dvd_support
#print axioms QuaternaryQuadraticForms.coprime_of_prime_dvd_support

#check @QuaternaryQuadraticForms.gcd_eq_good_part_of_prime_support
#print axioms QuaternaryQuadraticForms.gcd_eq_good_part_of_prime_support

#check @QuaternaryQuadraticForms.integralRamanujanSum_mul
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_mul

#check @QuaternaryQuadraticForms.integralRamanujanSum_zero
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_zero

#check @QuaternaryQuadraticForms.totient_mul_of_dvd
#print axioms QuaternaryQuadraticForms.totient_mul_of_dvd

#check @QuaternaryQuadraticForms.mixedCompleteSum_shared_support
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_shared_support

#check @QuaternaryQuadraticForms.compositeWeight_extend_eq_source
#print axioms QuaternaryQuadraticForms.compositeWeight_extend_eq_source

#check @QuaternaryQuadraticForms.source_coprime_quadraticBadPrimeModulus
#print axioms QuaternaryQuadraticForms.source_coprime_quadraticBadPrimeModulus

#check @QuaternaryQuadraticForms.squarefree_gcd_factors
#print axioms QuaternaryQuadraticForms.squarefree_gcd_factors

#check @QuaternaryQuadraticForms.gcd_mul_blocks_coprime
#print axioms QuaternaryQuadraticForms.gcd_mul_blocks_coprime

#check @QuaternaryQuadraticForms.squarefree_shared_gcd_factors
#print axioms QuaternaryQuadraticForms.squarefree_shared_gcd_factors

#check @QuaternaryQuadraticForms.squarefree_dvd_prime_pow_eq_one_or_prime
#print axioms QuaternaryQuadraticForms.squarefree_dvd_prime_pow_eq_one_or_prime

#check @QuaternaryQuadraticForms.divisors_card_le_rpow
#print axioms QuaternaryQuadraticForms.divisors_card_le_rpow

#check @QuaternaryQuadraticForms.sum_le_product_of_factorization
#print axioms QuaternaryQuadraticForms.sum_le_product_of_factorization

#check @QuaternaryQuadraticForms.sum_divisor_multiples_div_le_harmonic
#print axioms QuaternaryQuadraticForms.sum_divisor_multiples_div_le_harmonic

#check @QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_harmonic
#print axioms QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_harmonic

#check @QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_log
#print axioms QuaternaryQuadraticForms.sum_gcd_div_le_divisor_card_mul_log

#check @QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_not_dvd
#print axioms QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_not_dvd

#check @QuaternaryQuadraticForms.modulusNormSum_le_divisor_log
#print axioms QuaternaryQuadraticForms.modulusNormSum_le_divisor_log

#check @QuaternaryQuadraticForms.modulusNormSum_le_rpow
#print axioms QuaternaryQuadraticForms.modulusNormSum_le_rpow

#check @QuaternaryQuadraticForms.source_generic_modulus_bound
#print axioms QuaternaryQuadraticForms.source_generic_modulus_bound

#check @QuaternaryQuadraticForms.one_add_log_pow_le_rpow
#print axioms QuaternaryQuadraticForms.one_add_log_pow_le_rpow

#check @QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_eq_zero_of_gcd_not_dvd

#check @QuaternaryQuadraticForms.mixedCompleteSum_eq_zero_of_gcd_not_dvd
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_eq_zero_of_gcd_not_dvd

#check @QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_of_prime_split
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_of_prime_split

#check @QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_indicator_of_prime_split
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_gcd_indicator_of_prime_split

#check @QuaternaryQuadraticForms.globalQuadraticChar_norm_le
#print axioms QuaternaryQuadraticForms.globalQuadraticChar_norm_le

#check @QuaternaryQuadraticForms.compositeWeight_norm_le
#print axioms QuaternaryQuadraticForms.compositeWeight_norm_le

#check @QuaternaryQuadraticForms.primeWeightsNorm_le_extend
#print axioms QuaternaryQuadraticForms.primeWeightsNorm_le_extend

#check @QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_norm_le
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_good_modulus_norm_le

#check @QuaternaryQuadraticForms.mixedCompleteSum_eq_bad_mul_good
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_eq_bad_mul_good

#check @QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_of_prime_split
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_div_cube_le_of_prime_split

#check @QuaternaryQuadraticForms.mem_gcdModuliUpTo
#print axioms QuaternaryQuadraticForms.mem_gcdModuliUpTo

#check @QuaternaryQuadraticForms.normalizedMixedCompleteSum_of_neZero
#print axioms QuaternaryQuadraticForms.normalizedMixedCompleteSum_of_neZero

#check @QuaternaryQuadraticForms.normalizedMixedCompleteSum_nonneg
#print axioms QuaternaryQuadraticForms.normalizedMixedCompleteSum_nonneg

#check @QuaternaryQuadraticForms.modulusNormSum_nonneg
#print axioms QuaternaryQuadraticForms.modulusNormSum_nonneg

#check @QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_vanishing
#print axioms QuaternaryQuadraticForms.modulusNormSum_eq_zero_of_vanishing

#check @QuaternaryQuadraticForms.mem_primeSupportModuliUpTo
#print axioms QuaternaryQuadraticForms.mem_primeSupportModuliUpTo

#check @QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le
#print axioms QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le

#check @QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log
#print axioms QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log

#check @QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log_normalized
#print axioms QuaternaryQuadraticForms.primeSupportModuliUpTo_card_le_log_normalized

#check @QuaternaryQuadraticForms.integralRamanujanSum_prime_power_norm_le_gcd
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_prime_power_norm_le_gcd

#check @QuaternaryQuadraticForms.integralRamanujanSum_norm_le_gcd
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_norm_le_gcd

#check @QuaternaryQuadraticForms.integralRamanujanSum_mul_norm_le
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_mul_norm_le

#check @QuaternaryQuadraticForms.integralRamanujanSum_eq_zero_of_prime_sq_dvd
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_eq_zero_of_prime_sq_dvd

#check @QuaternaryQuadraticForms.integralRamanujanSum_shared_eq_zero
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_shared_eq_zero

#check @QuaternaryQuadraticForms.integralRamanujanSum_shared_norm_le
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_shared_norm_le

#check @QuaternaryQuadraticForms.integralRamanujanSum_prime_eq
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_prime_eq

#check @QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_eq_zero
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_eq_zero

#check @QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_mul
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_mul_modulus_mul

#check @QuaternaryQuadraticForms.integralRamanujanSum_prime_power_eq
#print axioms QuaternaryQuadraticForms.integralRamanujanSum_prime_power_eq

#check @QuaternaryQuadraticForms.periodic_cubic_sum_norm_le
#print axioms QuaternaryQuadraticForms.periodic_cubic_sum_norm_le

#check @QuaternaryQuadraticForms.periodic_cubic_sum_floor_norm_le
#print axioms QuaternaryQuadraticForms.periodic_cubic_sum_floor_norm_le

#check @QuaternaryQuadraticForms.good_modulus_sum_norm_le_harmonic
#print axioms QuaternaryQuadraticForms.good_modulus_sum_norm_le_harmonic

#check @QuaternaryQuadraticForms.unweightedModulusSum_le_divisor_log
#print axioms QuaternaryQuadraticForms.unweightedModulusSum_le_divisor_log

#check @QuaternaryQuadraticForms.unweightedCompleteSum_on_dual_cone
#print axioms QuaternaryQuadraticForms.unweightedCompleteSum_on_dual_cone

#check @QuaternaryQuadraticForms.good_modulus_sum_eq_quadratic_totient
#print axioms QuaternaryQuadraticForms.good_modulus_sum_eq_quadratic_totient

#check @QuaternaryQuadraticForms.unweightedModulusSum_le_rpow
#print axioms QuaternaryQuadraticForms.unweightedModulusSum_le_rpow

#check @QuaternaryQuadraticForms.source_cone_modulus_bound
#print axioms QuaternaryQuadraticForms.source_cone_modulus_bound

#check @QuaternaryQuadraticForms.sum_gcd_totient_eq_moebius
#print axioms QuaternaryQuadraticForms.sum_gcd_totient_eq_moebius

#check @QuaternaryQuadraticForms.sum_Icc_dvd_eq_sum_div
#print axioms QuaternaryQuadraticForms.sum_Icc_dvd_eq_sum_div

#check @QuaternaryQuadraticForms.coprime_indicator_eq_moebius_sum
#print axioms QuaternaryQuadraticForms.coprime_indicator_eq_moebius_sum

#check @QuaternaryQuadraticForms.sum_coprime_eq_sum_moebius_multiples
#print axioms QuaternaryQuadraticForms.sum_coprime_eq_sum_moebius_multiples

#check @QuaternaryQuadraticForms.moebius_complex_norm_le_one
#print axioms QuaternaryQuadraticForms.moebius_complex_norm_le_one

#check @QuaternaryQuadraticForms.coprime_cubic_sum_norm_le
#print axioms QuaternaryQuadraticForms.coprime_cubic_sum_norm_le

#check @QuaternaryQuadraticForms.sum_Icc_divisors_eq_sum_mul
#print axioms QuaternaryQuadraticForms.sum_Icc_divisors_eq_sum_mul

#check @QuaternaryQuadraticForms.sum_gcdModuliUpTo_eq_sum_coprime
#print axioms QuaternaryQuadraticForms.sum_gcdModuliUpTo_eq_sum_coprime

#check @QuaternaryQuadraticForms.sum_coprime_divisors_eq_sum_mul
#print axioms QuaternaryQuadraticForms.sum_coprime_divisors_eq_sum_mul

#check @QuaternaryQuadraticForms.modulus_prime_split_unique
#print axioms QuaternaryQuadraticForms.modulus_prime_split_unique

#check @QuaternaryQuadraticForms.sum_gcdModuli_eq_sum_prime_split
#print axioms QuaternaryQuadraticForms.sum_gcdModuli_eq_sum_prime_split

#check @QuaternaryQuadraticForms.unweightedCompleteSumValue_of_neZero
#print axioms QuaternaryQuadraticForms.unweightedCompleteSumValue_of_neZero

#check @QuaternaryQuadraticForms.unweightedModulusSum_prime_split
#print axioms QuaternaryQuadraticForms.unweightedModulusSum_prime_split

#check @QuaternaryQuadraticForms.periodic_sum_range_norm_le
#print axioms QuaternaryQuadraticForms.periodic_sum_range_norm_le

#check @QuaternaryQuadraticForms.exists_good_jacobiSym_neg_one
#print axioms QuaternaryQuadraticForms.exists_good_jacobiSym_neg_one

#check @QuaternaryQuadraticForms.goodQuadraticDirichletChar_ne_one
#print axioms QuaternaryQuadraticForms.goodQuadraticDirichletChar_ne_one

#check @QuaternaryQuadraticForms.goodQuadraticChar_sum_period_eq_zero
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_sum_period_eq_zero

#check @QuaternaryQuadraticForms.goodQuadraticChar_one
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_one

#check @QuaternaryQuadraticForms.goodQuadraticChar_zero
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_zero

#check @QuaternaryQuadraticForms.goodQuadraticChar_of_coprime
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_of_coprime

#check @QuaternaryQuadraticForms.goodQuadraticChar_of_not_coprime
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_of_not_coprime

#check @QuaternaryQuadraticForms.goodQuadraticChar_mul
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_mul

#check @QuaternaryQuadraticForms.goodQuadraticChar_norm_le_one
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_norm_le_one

#check @QuaternaryQuadraticForms.goodQuadraticChar_coprime_four_iff
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_coprime_four_iff

#check @QuaternaryQuadraticForms.goodQuadraticChar_mod
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_mod

#check @QuaternaryQuadraticForms.goodQuadraticChar_periodic
#print axioms QuaternaryQuadraticForms.goodQuadraticChar_periodic

#check @QuaternaryQuadraticForms.goodQuadraticDirichletChar_natCast
#print axioms QuaternaryQuadraticForms.goodQuadraticDirichletChar_natCast

#check @QuaternaryQuadraticForms.exists_jacobiSym_neg_one_mod_eight_of_squarefree
#print axioms QuaternaryQuadraticForms.exists_jacobiSym_neg_one_mod_eight_of_squarefree

#check @QuaternaryQuadraticForms.sum_gcd_totient_norm_le_harmonic
#print axioms QuaternaryQuadraticForms.sum_gcd_totient_norm_le_harmonic

#check @QuaternaryQuadraticForms.sum_gcd_totient_floor_norm_le_log
#print axioms QuaternaryQuadraticForms.sum_gcd_totient_floor_norm_le_log

#check @QuaternaryQuadraticForms.totient_eq_sum_moebius
#print axioms QuaternaryQuadraticForms.totient_eq_sum_moebius

#check @QuaternaryQuadraticForms.totient_mul_eq_sum_moebius
#print axioms QuaternaryQuadraticForms.totient_mul_eq_sum_moebius

#check @QuaternaryQuadraticForms.localQuadraticDensity_eq_tsum_re
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_eq_tsum_re

#check @QuaternaryQuadraticForms.tendsto_normalizedPrimePowerZeroCount
#print axioms QuaternaryQuadraticForms.tendsto_normalizedPrimePowerZeroCount

#check @QuaternaryQuadraticForms.hasSum_localDensityTerm
#print axioms QuaternaryQuadraticForms.hasSum_localDensityTerm

#check @QuaternaryQuadraticForms.localQuadraticDensity_nonneg
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_nonneg

#check @QuaternaryQuadraticForms.primePowerZeroCount_additive
#print axioms QuaternaryQuadraticForms.primePowerZeroCount_additive

#check @QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_fullGauss
#print axioms QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_fullGauss

#check @QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_recurrence
#print axioms QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_recurrence

#check @QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_zero
#print axioms QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_zero

#check @QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_sum
#print axioms QuaternaryQuadraticForms.normalizedPrimePowerZeroCount_eq_sum

#check @QuaternaryQuadraticForms.localQuadraticDensity_goodPrime
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_goodPrime

#check @QuaternaryQuadraticForms.source_localQuadraticDensity_goodPrime
#print axioms QuaternaryQuadraticForms.source_localQuadraticDensity_goodPrime

#check @QuaternaryQuadraticForms.correctedLocalDensityFactor_goodPrime
#print axioms QuaternaryQuadraticForms.correctedLocalDensityFactor_goodPrime

#check @QuaternaryQuadraticForms.correctedLocalDensityFactor_sub_one_norm_le
#print axioms QuaternaryQuadraticForms.correctedLocalDensityFactor_sub_one_norm_le

#check @QuaternaryQuadraticForms.eventually_prime_not_dvd_quadraticBadPrimeModulus
#print axioms QuaternaryQuadraticForms.eventually_prime_not_dvd_quadraticBadPrimeModulus

#check @QuaternaryQuadraticForms.summable_norm_correctedLocalDensityFactor_sub_one
#print axioms QuaternaryQuadraticForms.summable_norm_correctedLocalDensityFactor_sub_one

#check @QuaternaryQuadraticForms.multipliable_correctedLocalDensityFactor
#print axioms QuaternaryQuadraticForms.multipliable_correctedLocalDensityFactor

#check @QuaternaryQuadraticForms.multipliable_norm_correctedLocalDensityFactor
#print axioms QuaternaryQuadraticForms.multipliable_norm_correctedLocalDensityFactor

#check @QuaternaryQuadraticForms.integralQuadraticGaussSum_scaled_modulus
#print axioms QuaternaryQuadraticForms.integralQuadraticGaussSum_scaled_modulus

#check @QuaternaryQuadraticForms.primePower_fullGauss_recurrence
#print axioms QuaternaryQuadraticForms.primePower_fullGauss_recurrence

#check @QuaternaryQuadraticForms.localDensityTerm_zero
#print axioms QuaternaryQuadraticForms.localDensityTerm_zero

#check @QuaternaryQuadraticForms.legendreSym_complex_norm_le_one
#print axioms QuaternaryQuadraticForms.legendreSym_complex_norm_le_one

#check @QuaternaryQuadraticForms.localDensity_goodPrime_ratio_norm_lt_one
#print axioms QuaternaryQuadraticForms.localDensity_goodPrime_ratio_norm_lt_one

#check @QuaternaryQuadraticForms.localDensityTerm_goodPrime_succ
#print axioms QuaternaryQuadraticForms.localDensityTerm_goodPrime_succ

#check @QuaternaryQuadraticForms.localDensityTerm_hasSum_goodPrime
#print axioms QuaternaryQuadraticForms.localDensityTerm_hasSum_goodPrime

#check @QuaternaryQuadraticForms.localDensityTerm_norm_le
#print axioms QuaternaryQuadraticForms.localDensityTerm_norm_le

#check @QuaternaryQuadraticForms.summable_norm_localDensityTerm
#print axioms QuaternaryQuadraticForms.summable_norm_localDensityTerm

#check @QuaternaryQuadraticForms.summable_localDensityTerm
#print axioms QuaternaryQuadraticForms.summable_localDensityTerm

#check @QuaternaryQuadraticForms.local_density
#print axioms QuaternaryQuadraticForms.local_density

#check @QuaternaryQuadraticForms.source_local_density
#print axioms QuaternaryQuadraticForms.source_local_density

#check @QuaternaryQuadraticForms.sum_primePower_scalars
#print axioms QuaternaryQuadraticForms.sum_primePower_scalars

#check @QuaternaryQuadraticForms.orderedCoeffSum_eq_Icc_one
#print axioms QuaternaryQuadraticForms.orderedCoeffSum_eq_Icc_one

#check @QuaternaryQuadraticForms.orderedDirichletPartial_four
#print axioms QuaternaryQuadraticForms.orderedDirichletPartial_four

#check @QuaternaryQuadraticForms.norm_orderedDirichlet_integrand_le
#print axioms QuaternaryQuadraticForms.norm_orderedDirichlet_integrand_le

#check @QuaternaryQuadraticForms.orderedDirichlet_integrable
#print axioms QuaternaryQuadraticForms.orderedDirichlet_integrable

#check @QuaternaryQuadraticForms.orderedDirichlet_integral_norm_le
#print axioms QuaternaryQuadraticForms.orderedDirichlet_integral_norm_le

#check @QuaternaryQuadraticForms.tendsto_orderedDirichletPartial
#print axioms QuaternaryQuadraticForms.tendsto_orderedDirichletPartial

#check @QuaternaryQuadraticForms.orderedDirichletPartial_eq_boundary_add_integral
#print axioms QuaternaryQuadraticForms.orderedDirichletPartial_eq_boundary_add_integral

#check @QuaternaryQuadraticForms.orderedDirichletValue_sub_partial
#print axioms QuaternaryQuadraticForms.orderedDirichletValue_sub_partial

#check @QuaternaryQuadraticForms.norm_orderedDirichletValue_sub_partial_le
#print axioms QuaternaryQuadraticForms.norm_orderedDirichletValue_sub_partial_le

#check @QuaternaryQuadraticForms.continuousWithinAt_orderedDirichletValue_four
#print axioms QuaternaryQuadraticForms.continuousWithinAt_orderedDirichletValue_four

#check @QuaternaryQuadraticForms.shiftedLocalDensity_damping_norm_le_one
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_damping_norm_le_one

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_norm_le
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_norm_le

#check @QuaternaryQuadraticForms.summable_norm_shiftedLocalDensityTerm
#print axioms QuaternaryQuadraticForms.summable_norm_shiftedLocalDensityTerm

#check @QuaternaryQuadraticForms.summable_shiftedLocalDensityTerm
#print axioms QuaternaryQuadraticForms.summable_shiftedLocalDensityTerm

#check @QuaternaryQuadraticForms.continuous_shiftedLocalDensityTerm
#print axioms QuaternaryQuadraticForms.continuous_shiftedLocalDensityTerm

#check @QuaternaryQuadraticForms.continuousOn_shiftedLocalDensity
#print axioms QuaternaryQuadraticForms.continuousOn_shiftedLocalDensity

#check @QuaternaryQuadraticForms.shiftedLocalDensity_zero
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_zero

#check @QuaternaryQuadraticForms.tendsto_shiftedLocalDensity_zero
#print axioms QuaternaryQuadraticForms.tendsto_shiftedLocalDensity_zero

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_exponent
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_exponent

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_shift
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_zero_shift

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_eq_primePower
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_eq_primePower

#check @QuaternaryQuadraticForms.div_natCast_rpow_nat_add
#print axioms QuaternaryQuadraticForms.div_natCast_rpow_nat_add

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ratio_norm_lt_one
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ratio_norm_lt_one

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_div_norm_lt_one
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_div_norm_lt_one

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_den_ne_zero
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_den_ne_zero

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_goodPrime_succ
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_goodPrime_succ

#check @QuaternaryQuadraticForms.shiftedLocalDensityTerm_hasSum_goodPrime
#print axioms QuaternaryQuadraticForms.shiftedLocalDensityTerm_hasSum_goodPrime

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_num_ne_zero
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_num_ne_zero

#check @QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ne_zero
#print axioms QuaternaryQuadraticForms.shiftedLocalDensity_goodPrime_ne_zero

#check @QuaternaryQuadraticForms.source_shiftedLocalDensity_goodPrime
#print axioms QuaternaryQuadraticForms.source_shiftedLocalDensity_goodPrime

#check @QuaternaryQuadraticForms.coprimeCompleteSumValue_one
#print axioms QuaternaryQuadraticForms.coprimeCompleteSumValue_one

#check @QuaternaryQuadraticForms.coprimeCompleteSumValue_mul
#print axioms QuaternaryQuadraticForms.coprimeCompleteSumValue_mul

#check @QuaternaryQuadraticForms.coprimeCompleteSumValue_norm_le
#print axioms QuaternaryQuadraticForms.coprimeCompleteSumValue_norm_le

#check @QuaternaryQuadraticForms.singularSeriesTerm_one
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_one

#check @QuaternaryQuadraticForms.singularSeriesTerm_mul
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_mul

#check @QuaternaryQuadraticForms.singularSeriesTerm_norm_le
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_norm_le

#check @QuaternaryQuadraticForms.summable_norm_singularSeriesTerm
#print axioms QuaternaryQuadraticForms.summable_norm_singularSeriesTerm

#check @QuaternaryQuadraticForms.summable_singularSeriesTerm
#print axioms QuaternaryQuadraticForms.summable_singularSeriesTerm

#check @QuaternaryQuadraticForms.singularSeriesTerm_eulerProduct_hasProd
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_eulerProduct_hasProd

#check @QuaternaryQuadraticForms.singularSeriesPartialSum_eq_sum_range
#print axioms QuaternaryQuadraticForms.singularSeriesPartialSum_eq_sum_range

#check @QuaternaryQuadraticForms.singularSeriesPartialSum_sub_eq_sum_Ioc
#print axioms QuaternaryQuadraticForms.singularSeriesPartialSum_sub_eq_sum_Ioc

#check @QuaternaryQuadraticForms.mem_singularSeries_tail_interval
#print axioms QuaternaryQuadraticForms.mem_singularSeries_tail_interval

#check @QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_tsum
#print axioms QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_tsum

#check @QuaternaryQuadraticForms.singularSeriesValue_eq_tsum
#print axioms QuaternaryQuadraticForms.singularSeriesValue_eq_tsum

#check @QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_not_dvd
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_not_dvd

#check @QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_dvd
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_primePower_of_dvd

#check @QuaternaryQuadraticForms.tsum_singularSeriesTerm_primePower
#print axioms QuaternaryQuadraticForms.tsum_singularSeriesTerm_primePower

#check @QuaternaryQuadraticForms.singularSeries_eulerProduct_hasProd
#print axioms QuaternaryQuadraticForms.singularSeries_eulerProduct_hasProd

#check @QuaternaryQuadraticForms.singularSeriesEulerCorrection_zero
#print axioms QuaternaryQuadraticForms.singularSeriesEulerCorrection_zero

#check @QuaternaryQuadraticForms.singularSeriesValue_zero_eq
#print axioms QuaternaryQuadraticForms.singularSeriesValue_zero_eq

#check @QuaternaryQuadraticForms.correctedLocalDensityFactor_eq_dirichletRealEulerFactor
#print axioms QuaternaryQuadraticForms.correctedLocalDensityFactor_eq_dirichletRealEulerFactor

#check @QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_ne_zero
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_ne_zero

#check @QuaternaryQuadraticForms.hasProd_removedCorrectedLocalDensityFactor
#print axioms QuaternaryQuadraticForms.hasProd_removedCorrectedLocalDensityFactor

#check @QuaternaryQuadraticForms.singularSeriesPartialSum_eq_orderedDirichletPartial
#print axioms QuaternaryQuadraticForms.singularSeriesPartialSum_eq_orderedDirichletPartial

#check @QuaternaryQuadraticForms.exists_coprimeCompleteSumValue_bound
#print axioms QuaternaryQuadraticForms.exists_coprimeCompleteSumValue_bound

#check @QuaternaryQuadraticForms.singularSeriesValue_eq_orderedDirichletValue_of_bound
#print axioms QuaternaryQuadraticForms.singularSeriesValue_eq_orderedDirichletValue_of_bound

#check @QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum
#print axioms QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum

#check @QuaternaryQuadraticForms.continuousWithinAt_singularSeriesValue_zero
#print axioms QuaternaryQuadraticForms.continuousWithinAt_singularSeriesValue_zero

#check @QuaternaryQuadraticForms.singularSeries_uniform_tail
#print axioms QuaternaryQuadraticForms.singularSeries_uniform_tail

#check @QuaternaryQuadraticForms.coprimeCompleteSumValue_zero
#print axioms QuaternaryQuadraticForms.coprimeCompleteSumValue_zero

#check @QuaternaryQuadraticForms.singularSeriesTerm_zero
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_zero

#check @QuaternaryQuadraticForms.sum_coprimeCompleteSumValue
#print axioms QuaternaryQuadraticForms.sum_coprimeCompleteSumValue

#check @QuaternaryQuadraticForms.singularSeriesTerm_at_zero
#print axioms QuaternaryQuadraticForms.singularSeriesTerm_at_zero

#check @QuaternaryQuadraticForms.restrictedCorrectedShiftedFactor_goodPrime
#print axioms QuaternaryQuadraticForms.restrictedCorrectedShiftedFactor_goodPrime

#check @QuaternaryQuadraticForms.hasProd_restrictedCorrectedShiftedFactor
#print axioms QuaternaryQuadraticForms.hasProd_restrictedCorrectedShiftedFactor

#check @QuaternaryQuadraticForms.tsum_singularSeriesTerm_eq_LFunction_mul_correction
#print axioms QuaternaryQuadraticForms.tsum_singularSeriesTerm_eq_LFunction_mul_correction

#check @QuaternaryQuadraticForms.continuousWithinAt_singularSeriesEulerCorrection_zero
#print axioms QuaternaryQuadraticForms.continuousWithinAt_singularSeriesEulerCorrection_zero

#check @QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_cpow
#print axioms QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_cpow

#check @QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_div
#print axioms QuaternaryQuadraticForms.dirichletRealEulerFactor_eq_div

#check @QuaternaryQuadraticForms.dirichletRealEulerFactor_ne_zero
#print axioms QuaternaryQuadraticForms.dirichletRealEulerFactor_ne_zero

#check @QuaternaryQuadraticForms.continuous_dirichletRealEulerFactor
#print axioms QuaternaryQuadraticForms.continuous_dirichletRealEulerFactor

#check @QuaternaryQuadraticForms.hasProd_inv_dirichletRealEulerFactor
#print axioms QuaternaryQuadraticForms.hasProd_inv_dirichletRealEulerFactor

#check @QuaternaryQuadraticForms.LFunction_real_ne_zero
#print axioms QuaternaryQuadraticForms.LFunction_real_ne_zero

#check @QuaternaryQuadraticForms.hasProd_dirichletRealEulerFactor
#print axioms QuaternaryQuadraticForms.hasProd_dirichletRealEulerFactor

#check @QuaternaryQuadraticForms.mem_singularSeriesPrimeDivisors
#print axioms QuaternaryQuadraticForms.mem_singularSeriesPrimeDivisors

#check @QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_zero
#print axioms QuaternaryQuadraticForms.tendsto_singularSeriesPartialSum_zero

#check @QuaternaryQuadraticForms.tendsto_singularSeriesTail_zero
#print axioms QuaternaryQuadraticForms.tendsto_singularSeriesTail_zero

#check @QuaternaryQuadraticForms.tendsto_singularSeriesTail_Ioc
#print axioms QuaternaryQuadraticForms.tendsto_singularSeriesTail_Ioc

#check @QuaternaryQuadraticForms.source_singular_series
#print axioms QuaternaryQuadraticForms.source_singular_series

#check @QuaternaryQuadraticForms.sourceDirichletCharacter_exists_neg_one
#print axioms QuaternaryQuadraticForms.sourceDirichletCharacter_exists_neg_one

#check @QuaternaryQuadraticForms.sourceDirichletCharacter_ne_one
#print axioms QuaternaryQuadraticForms.sourceDirichletCharacter_ne_one

#check @QuaternaryQuadraticForms.polynomialBoxConstant_zero
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_zero

#check @QuaternaryQuadraticForms.polynomialBoxConstant_succ
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_succ

#check @QuaternaryQuadraticForms.polynomialBoxConstant_one
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_one

#check @QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_range
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_range

#check @QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_Icc
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_eq_sum_Icc

#check @QuaternaryQuadraticForms.polynomialBoxConstant_pos
#print axioms QuaternaryQuadraticForms.polynomialBoxConstant_pos

#check @QuaternaryQuadraticForms.polynomialBox_pow_add_one_le
#print axioms QuaternaryQuadraticForms.polynomialBox_pow_add_one_le

#check @QuaternaryQuadraticForms.sum_polynomialBox_bad_product_eq
#print axioms QuaternaryQuadraticForms.sum_polynomialBox_bad_product_eq

#check @QuaternaryQuadraticForms.polynomialBox_subset_ratio_sum_le
#print axioms QuaternaryQuadraticForms.polynomialBox_subset_ratio_sum_le

#check @QuaternaryQuadraticForms.polynomialBox_subset_weight_sum_le
#print axioms QuaternaryQuadraticForms.polynomialBox_subset_weight_sum_le

#check @QuaternaryQuadraticForms.sum_polynomialBox_bad_product_le
#print axioms QuaternaryQuadraticForms.sum_polynomialBox_bad_product_le

#check @QuaternaryQuadraticForms.polynomialBox_count_step
#print axioms QuaternaryQuadraticForms.polynomialBox_count_step

#check @QuaternaryQuadraticForms.mem_integerPolynomialBox
#print axioms QuaternaryQuadraticForms.mem_integerPolynomialBox

#check @QuaternaryQuadraticForms.mem_polynomialBoxSolutions
#print axioms QuaternaryQuadraticForms.mem_polynomialBoxSolutions

#check @QuaternaryQuadraticForms.integerPolynomialBox_card
#print axioms QuaternaryQuadraticForms.integerPolynomialBox_card

#check @QuaternaryQuadraticForms.integerPolynomialBox_card_le
#print axioms QuaternaryQuadraticForms.integerPolynomialBox_card_le

#check @QuaternaryQuadraticForms.polynomialBoxSolutions_empty
#print axioms QuaternaryQuadraticForms.polynomialBoxSolutions_empty

#check @QuaternaryQuadraticForms.polynomialBoxSolutions_card_le_box
#print axioms QuaternaryQuadraticForms.polynomialBoxSolutions_card_le_box

#check @QuaternaryQuadraticForms.cons_mem_integerPolynomialBox
#print axioms QuaternaryQuadraticForms.cons_mem_integerPolynomialBox

#check @QuaternaryQuadraticForms.integerPolynomialBox_zero
#print axioms QuaternaryQuadraticForms.integerPolynomialBox_zero

#check @QuaternaryQuadraticForms.integerPolynomialBox_filter_card_succ
#print axioms QuaternaryQuadraticForms.integerPolynomialBox_filter_card_succ

#check @QuaternaryQuadraticForms.polynomialBoxSolutions_card_succ
#print axioms QuaternaryQuadraticForms.polynomialBoxSolutions_card_succ

#check @QuaternaryQuadraticForms.polynomialBoxBadPrimes_subset
#print axioms QuaternaryQuadraticForms.polynomialBoxBadPrimes_subset

#check @QuaternaryQuadraticForms.polynomialIntervalZeros_sdiff_bad
#print axioms QuaternaryQuadraticForms.polynomialIntervalZeros_sdiff_bad

#check @QuaternaryQuadraticForms.polynomialBox_fiber_card_le
#print axioms QuaternaryQuadraticForms.polynomialBox_fiber_card_le

#check @QuaternaryQuadraticForms.polynomialBox_primeSet_card_le
#print axioms QuaternaryQuadraticForms.polynomialBox_primeSet_card_le

#check @QuaternaryQuadraticForms.integerInterval_eq_Icc
#print axioms QuaternaryQuadraticForms.integerInterval_eq_Icc

#check @QuaternaryQuadraticForms.realInterval_integer_points_ordConnected
#print axioms QuaternaryQuadraticForms.realInterval_integer_points_ordConnected

#check @QuaternaryQuadraticForms.realInterval_integer_points_eq_Icc
#print axioms QuaternaryQuadraticForms.realInterval_integer_points_eq_Icc

#check @QuaternaryQuadraticForms.realInterval_integer_membership_Icc
#print axioms QuaternaryQuadraticForms.realInterval_integer_membership_Icc

#check @QuaternaryQuadraticForms.mem_polynomialIntervalZeros
#print axioms QuaternaryQuadraticForms.mem_polynomialIntervalZeros

#check @QuaternaryQuadraticForms.polynomialIntervalZeros_card_le
#print axioms QuaternaryQuadraticForms.polynomialIntervalZeros_card_le

#check @QuaternaryQuadraticForms.mem_primeResidueInterval
#print axioms QuaternaryQuadraticForms.mem_primeResidueInterval

#check @QuaternaryQuadraticForms.primeProduct_modEq
#print axioms QuaternaryQuadraticForms.primeProduct_modEq

#check @QuaternaryQuadraticForms.primeResidueInterval_card_le_blocks
#print axioms QuaternaryQuadraticForms.primeResidueInterval_card_le_blocks

#check @QuaternaryQuadraticForms.primeResidueInterval_card_le
#print axioms QuaternaryQuadraticForms.primeResidueInterval_card_le

#check @QuaternaryQuadraticForms.polynomialBoxSlice_eval
#print axioms QuaternaryQuadraticForms.polynomialBoxSlice_eval

#check @QuaternaryQuadraticForms.polynomialBoxSlice_coeff
#print axioms QuaternaryQuadraticForms.polynomialBoxSlice_coeff

#check @QuaternaryQuadraticForms.polynomialBoxSlice_eq_zero_iff
#print axioms QuaternaryQuadraticForms.polynomialBoxSlice_eq_zero_iff

#check @QuaternaryQuadraticForms.polynomialBoxSlice_natDegree_le
#print axioms QuaternaryQuadraticForms.polynomialBoxSlice_natDegree_le

#check @QuaternaryQuadraticForms.polynomialBoxCoefficient_totalDegree_le
#print axioms QuaternaryQuadraticForms.polynomialBoxCoefficient_totalDegree_le

#check @QuaternaryQuadraticForms.exists_polynomialBoxCoefficient_ne_zero
#print axioms QuaternaryQuadraticForms.exists_polynomialBoxCoefficient_ne_zero

#check @QuaternaryQuadraticForms.exists_polynomialBox_degeneracy_polynomial
#print axioms QuaternaryQuadraticForms.exists_polynomialBox_degeneracy_polynomial

#check @QuaternaryQuadraticForms.polynomialBoxSlice_empty_ne_zero
#print axioms QuaternaryQuadraticForms.polynomialBoxSlice_empty_ne_zero

#check @QuaternaryQuadraticForms.polynomialBox_primeFactors_card_eq_omega
#print axioms QuaternaryQuadraticForms.polynomialBox_primeFactors_card_eq_omega

#check @QuaternaryQuadraticForms.polynomialBox_squarefree_card_le
#print axioms QuaternaryQuadraticForms.polynomialBox_squarefree_card_le

#check @QuaternaryQuadraticForms.extendPolynomialBoxFamily_apply
#print axioms QuaternaryQuadraticForms.extendPolynomialBoxFamily_apply

#check @QuaternaryQuadraticForms.sourcePolynomialBoxSet_eq_integer
#print axioms QuaternaryQuadraticForms.sourcePolynomialBoxSet_eq_integer

#check @QuaternaryQuadraticForms.source_polynomial_box
#print axioms QuaternaryQuadraticForms.source_polynomial_box

#check @QuaternaryQuadraticForms.congruenceEuclideanBall_subset_polynomialBox
#print axioms QuaternaryQuadraticForms.congruenceEuclideanBall_subset_polynomialBox

#check @QuaternaryQuadraticForms.congruenceEuclideanBall_card_le_rpow
#print axioms QuaternaryQuadraticForms.congruenceEuclideanBall_card_le_rpow

#check @QuaternaryQuadraticForms.exceptionalIndicator_eq_ite
#print axioms QuaternaryQuadraticForms.exceptionalIndicator_eq_ite

#check @QuaternaryQuadraticForms.exceptionalIndicator_eq_one_iff
#print axioms QuaternaryQuadraticForms.exceptionalIndicator_eq_one_iff

#check @QuaternaryQuadraticForms.exceptionalIndicator_eq_zero_of_ne_one
#print axioms QuaternaryQuadraticForms.exceptionalIndicator_eq_zero_of_ne_one

#check @QuaternaryQuadraticForms.exceptionalIndicator_one
#print axioms QuaternaryQuadraticForms.exceptionalIndicator_one

#check @QuaternaryQuadraticForms.mem_congruenceEuclideanBall
#print axioms QuaternaryQuadraticForms.mem_congruenceEuclideanBall

#check @QuaternaryQuadraticForms.mem_divisibleEuclideanBall
#print axioms QuaternaryQuadraticForms.mem_divisibleEuclideanBall

#check @QuaternaryQuadraticForms.weightedCongruenceEuclideanSum_eq
#print axioms QuaternaryQuadraticForms.weightedCongruenceEuclideanSum_eq

#check @QuaternaryQuadraticForms.boxCongruencePolynomial_ne_zero
#print axioms QuaternaryQuadraticForms.boxCongruencePolynomial_ne_zero

#check @QuaternaryQuadraticForms.boxCongruencePolynomial_totalDegree_le
#print axioms QuaternaryQuadraticForms.boxCongruencePolynomial_totalDegree_le

#check @QuaternaryQuadraticForms.squarefree_int_dvd_iff_primeFactors
#print axioms QuaternaryQuadraticForms.squarefree_int_dvd_iff_primeFactors

#check @QuaternaryQuadraticForms.boxCongruencePolynomial_eval_eq_zero_iff
#print axioms QuaternaryQuadraticForms.boxCongruencePolynomial_eval_eq_zero_iff

#check @QuaternaryQuadraticForms.congruenceBox_bounds
#print axioms QuaternaryQuadraticForms.congruenceBox_bounds

#check @QuaternaryQuadraticForms.integerEuclideanNorm_eq_sqrt
#print axioms QuaternaryQuadraticForms.integerEuclideanNorm_eq_sqrt

#check @QuaternaryQuadraticForms.integerEuclideanNorm_nonneg
#print axioms QuaternaryQuadraticForms.integerEuclideanNorm_nonneg

#check @QuaternaryQuadraticForms.coordinate_abs_le_integerEuclideanNorm
#print axioms QuaternaryQuadraticForms.coordinate_abs_le_integerEuclideanNorm

#check @QuaternaryQuadraticForms.integerEuclideanNorm_eq_zero_iff
#print axioms QuaternaryQuadraticForms.integerEuclideanNorm_eq_zero_iff

#check @QuaternaryQuadraticForms.one_le_integerEuclideanNorm
#print axioms QuaternaryQuadraticForms.one_le_integerEuclideanNorm

#check @QuaternaryQuadraticForms.integerEuclideanNorm_pos_iff
#print axioms QuaternaryQuadraticForms.integerEuclideanNorm_pos_iff

#check @QuaternaryQuadraticForms.integerEuclideanNorm_le_mem_box
#print axioms QuaternaryQuadraticForms.integerEuclideanNorm_le_mem_box

#check @QuaternaryQuadraticForms.mem_integerEuclideanBall
#print axioms QuaternaryQuadraticForms.mem_integerEuclideanBall

#check @QuaternaryQuadraticForms.integerEuclideanBall_mono
#print axioms QuaternaryQuadraticForms.integerEuclideanBall_mono

#check @QuaternaryQuadraticForms.integerEuclideanInterval_card_le_three_mul
#print axioms QuaternaryQuadraticForms.integerEuclideanInterval_card_le_three_mul

#check @QuaternaryQuadraticForms.inverseRadiusSum_le_of_sublevel_card
#print axioms QuaternaryQuadraticForms.inverseRadiusSum_le_of_sublevel_card

#check @QuaternaryQuadraticForms.polynomialBox_squarefree_card_le_rpow
#print axioms QuaternaryQuadraticForms.polynomialBox_squarefree_card_le_rpow

#check @QuaternaryQuadraticForms.source_polynomial_box_epsilon
#print axioms QuaternaryQuadraticForms.source_polynomial_box_epsilon

#check @QuaternaryQuadraticForms.primeFactor_pow_le_rpow
#print axioms QuaternaryQuadraticForms.primeFactor_pow_le_rpow

#check @QuaternaryQuadraticForms.sourceCongruenceEuclideanSet_eq
#print axioms QuaternaryQuadraticForms.sourceCongruenceEuclideanSet_eq

#check @QuaternaryQuadraticForms.sourceWeightedCongruenceEuclideanSum_eq
#print axioms QuaternaryQuadraticForms.sourceWeightedCongruenceEuclideanSum_eq

#check @QuaternaryQuadraticForms.source_congruence_box_natDegree
#print axioms QuaternaryQuadraticForms.source_congruence_box_natDegree

#check @QuaternaryQuadraticForms.source_congruence_box
#print axioms QuaternaryQuadraticForms.source_congruence_box

#check @QuaternaryQuadraticForms.extendExceptionalPolynomials_apply
#print axioms QuaternaryQuadraticForms.extendExceptionalPolynomials_apply

#check @QuaternaryQuadraticForms.extendExceptionalPolynomials_ne_zero
#print axioms QuaternaryQuadraticForms.extendExceptionalPolynomials_ne_zero

#check @QuaternaryQuadraticForms.extendExceptionalPolynomials_totalDegree_le
#print axioms QuaternaryQuadraticForms.extendExceptionalPolynomials_totalDegree_le

#check @QuaternaryQuadraticForms.exceptionalIndicator_extend
#print axioms QuaternaryQuadraticForms.exceptionalIndicator_extend

#check @QuaternaryQuadraticForms.sourceExceptionalIndicator_one
#print axioms QuaternaryQuadraticForms.sourceExceptionalIndicator_one

#check @QuaternaryQuadraticForms.squarefree_divisor_sum_eq_powerset
#print axioms QuaternaryQuadraticForms.squarefree_divisor_sum_eq_powerset

#check @QuaternaryQuadraticForms.exceptional_prime_product_eq_divisor_sum
#print axioms QuaternaryQuadraticForms.exceptional_prime_product_eq_divisor_sum

#check @QuaternaryQuadraticForms.fourier_stratified_product_eq
#print axioms QuaternaryQuadraticForms.fourier_stratified_product_eq

#check @QuaternaryQuadraticForms.constrainedFourierSum_norm_le_divisors
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_norm_le_divisors

#check @QuaternaryQuadraticForms.divisor_halfPower_shape_le
#print axioms QuaternaryQuadraticForms.divisor_halfPower_shape_le

#check @QuaternaryQuadraticForms.exceptional_divisor_sum_le
#print axioms QuaternaryQuadraticForms.exceptional_divisor_sum_le

#check @QuaternaryQuadraticForms.weightedSum_le_exceptional_divisors
#print axioms QuaternaryQuadraticForms.weightedSum_le_exceptional_divisors

#check @QuaternaryQuadraticForms.averageFrequency_bound
#print axioms QuaternaryQuadraticForms.averageFrequency_bound

#check @QuaternaryQuadraticForms.constrainedFourierSum_extend_eq_source
#print axioms QuaternaryQuadraticForms.constrainedFourierSum_extend_eq_source

#check @QuaternaryQuadraticForms.sourceConstrainedFourierSum_prime
#print axioms QuaternaryQuadraticForms.sourceConstrainedFourierSum_prime

#check @QuaternaryQuadraticForms.sourceConstrainedFourierSum_one
#print axioms QuaternaryQuadraticForms.sourceConstrainedFourierSum_one

#check @QuaternaryQuadraticForms.sourceConstrainedFourierSum_primeFactors
#print axioms QuaternaryQuadraticForms.sourceConstrainedFourierSum_primeFactors

#check @QuaternaryQuadraticForms.source_average_frequency_natDegree
#print axioms QuaternaryQuadraticForms.source_average_frequency_natDegree

#check @QuaternaryQuadraticForms.source_average_frequency_bound
#print axioms QuaternaryQuadraticForms.source_average_frequency_bound

#check @QuaternaryQuadraticForms.Trusted.heathBrown_delta_data
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_delta_data

#check @QuaternaryQuadraticForms.bumpSamplingSum_finite_support
#print axioms QuaternaryQuadraticForms.bumpSamplingSum_finite_support

#check @QuaternaryQuadraticForms.bumpSamplingSum_summable
#print axioms QuaternaryQuadraticForms.bumpSamplingSum_summable

#check @QuaternaryQuadraticForms.bumpSamplingSum_uniform_pos
#print axioms QuaternaryQuadraticForms.bumpSamplingSum_uniform_pos

#check @QuaternaryQuadraticForms.bumpNormalization_error_bound
#print axioms QuaternaryQuadraticForms.bumpNormalization_error_bound

#check @QuaternaryQuadraticForms.deltaSymbolTerm_eq_unit_sum
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_eq_unit_sum

#check @QuaternaryQuadraticForms.deltaSymbolTerm_eq_exponential_sum
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_eq_exponential_sum

#check @QuaternaryQuadraticForms.deltaSymbolTerm_modulus_one
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_modulus_one

#check @QuaternaryQuadraticForms.deltaSymbolKernel_eq_zero_of_modulus_bound
#print axioms QuaternaryQuadraticForms.deltaSymbolKernel_eq_zero_of_modulus_bound

#check @QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_modulus_bound
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_modulus_bound

#check @QuaternaryQuadraticForms.deltaSymbol_modulus_bound_eq_max
#print axioms QuaternaryQuadraticForms.deltaSymbol_modulus_bound_eq_max

#check @QuaternaryQuadraticForms.mem_deltaSymbolModuli
#print axioms QuaternaryQuadraticForms.mem_deltaSymbolModuli

#check @QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_not_mem
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_eq_zero_of_not_mem

#check @QuaternaryQuadraticForms.deltaSymbolTerm_finite_support
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_finite_support

#check @QuaternaryQuadraticForms.deltaSymbolTerm_summable
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_summable

#check @QuaternaryQuadraticForms.deltaSymbolTerm_norm_summable
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_norm_summable

#check @QuaternaryQuadraticForms.deltaSymbolTerm_hasSum
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_hasSum

#check @QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum

#check @QuaternaryQuadraticForms.deltaSymbolModuli_sum_eq_sum_range
#print axioms QuaternaryQuadraticForms.deltaSymbolModuli_sum_eq_sum_range

#check @QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum_range
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_sum_range

#check @QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_unit_sum
#print axioms QuaternaryQuadraticForms.deltaSymbolTerm_tsum_eq_unit_sum

#check @QuaternaryQuadraticForms.heathBrownDeltaKernel_properties
#print axioms QuaternaryQuadraticForms.heathBrownDeltaKernel_properties

#check @QuaternaryQuadraticForms.heathBrownSamplingSum_uniform_pos
#print axioms QuaternaryQuadraticForms.heathBrownSamplingSum_uniform_pos

#check @QuaternaryQuadraticForms.heathBrownSamplingSum_pos
#print axioms QuaternaryQuadraticForms.heathBrownSamplingSum_pos

#check @QuaternaryQuadraticForms.heathBrownNormalization_pos
#print axioms QuaternaryQuadraticForms.heathBrownNormalization_pos

#check @QuaternaryQuadraticForms.heathBrownNormalization_error_bound
#print axioms QuaternaryQuadraticForms.heathBrownNormalization_error_bound

#check @QuaternaryQuadraticForms.heathBrownNormalization_error_bound_real
#print axioms QuaternaryQuadraticForms.heathBrownNormalization_error_bound_real

#check @QuaternaryQuadraticForms.heathBrown_delta_identity
#print axioms QuaternaryQuadraticForms.heathBrown_delta_identity

#check @QuaternaryQuadraticForms.heathBrown_delta_finite_identity
#print axioms QuaternaryQuadraticForms.heathBrown_delta_finite_identity

#check @QuaternaryQuadraticForms.source_delta_symbol
#print axioms QuaternaryQuadraticForms.source_delta_symbol

#check @QuaternaryQuadraticForms.Trusted.simon_graph_area
#print axioms QuaternaryQuadraticForms.Trusted.simon_graph_area

#check @QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization

#check @QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph

#check @QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation

#check @QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction

#check @QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds

#check @QuaternaryQuadraticForms.heathBrownBaseBump_eq_expNegInvGlue
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_eq_expNegInvGlue

#check @QuaternaryQuadraticForms.heathBrownBaseBump_contDiff
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_contDiff

#check @QuaternaryQuadraticForms.heathBrownBaseBump_nonneg
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_nonneg

#check @QuaternaryQuadraticForms.heathBrownBaseBump_ne_zero_iff
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_ne_zero_iff

#check @QuaternaryQuadraticForms.heathBrownBaseBump_hasCompactSupport
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_hasCompactSupport

#check @QuaternaryQuadraticForms.heathBrownBaseBump_integrable
#print axioms QuaternaryQuadraticForms.heathBrownBaseBump_integrable

#check @QuaternaryQuadraticForms.heathBrownBumpMass_pos
#print axioms QuaternaryQuadraticForms.heathBrownBumpMass_pos

#check @QuaternaryQuadraticForms.heathBrownTheta_nonneg
#print axioms QuaternaryQuadraticForms.heathBrownTheta_nonneg

#check @QuaternaryQuadraticForms.heathBrownTheta_contDiff
#print axioms QuaternaryQuadraticForms.heathBrownTheta_contDiff

#check @QuaternaryQuadraticForms.heathBrownTheta_coordinates_lt_one
#print axioms QuaternaryQuadraticForms.heathBrownTheta_coordinates_lt_one

#check @QuaternaryQuadraticForms.heathBrownTheta_tsupport_subset_cube
#print axioms QuaternaryQuadraticForms.heathBrownTheta_tsupport_subset_cube

#check @QuaternaryQuadraticForms.heathBrownTheta_norm_le_two_of_mem_tsupport
#print axioms QuaternaryQuadraticForms.heathBrownTheta_norm_le_two_of_mem_tsupport

#check @QuaternaryQuadraticForms.heathBrownTheta_hasCompactSupport
#print axioms QuaternaryQuadraticForms.heathBrownTheta_hasCompactSupport

#check @QuaternaryQuadraticForms.heathBrownTheta_integrable
#print axioms QuaternaryQuadraticForms.heathBrownTheta_integrable

#check @QuaternaryQuadraticForms.heathBrownTheta_integral
#print axioms QuaternaryQuadraticForms.heathBrownTheta_integral

#check @QuaternaryQuadraticForms.UniformCoordinateDerivatives.uniformWeightDerivatives
#print axioms QuaternaryQuadraticForms.UniformCoordinateDerivatives.uniformWeightDerivatives

#check @QuaternaryQuadraticForms.UniformWeightDerivatives.uniformCoordinateDerivatives
#print axioms QuaternaryQuadraticForms.UniformWeightDerivatives.uniformCoordinateDerivatives

#check @QuaternaryQuadraticForms.uniformCoordinateDerivatives_iff_uniformWeightDerivatives
#print axioms QuaternaryQuadraticForms.uniformCoordinateDerivatives_iff_uniformWeightDerivatives

#check @QuaternaryQuadraticForms.heathBrownTheta_uniform_translate_derivatives
#print axioms QuaternaryQuadraticForms.heathBrownTheta_uniform_translate_derivatives

#check @QuaternaryQuadraticForms.UniformWeightDerivatives.localizedWeight
#print axioms QuaternaryQuadraticForms.UniformWeightDerivatives.localizedWeight

#check @QuaternaryQuadraticForms.UniformCoordinateDerivatives.localizedWeight
#print axioms QuaternaryQuadraticForms.UniformCoordinateDerivatives.localizedWeight

#check @QuaternaryQuadraticForms.UniformWeightDerivatives.comp_realIsometry
#print axioms QuaternaryQuadraticForms.UniformWeightDerivatives.comp_realIsometry

#check @QuaternaryQuadraticForms.UniformCoordinateDerivatives.comp_realIsometry
#print axioms QuaternaryQuadraticForms.UniformCoordinateDerivatives.comp_realIsometry

#check @QuaternaryQuadraticForms.localizedWeight_contDiff
#print axioms QuaternaryQuadraticForms.localizedWeight_contDiff

#check @QuaternaryQuadraticForms.localizedWeight_tsupport_subset
#print axioms QuaternaryQuadraticForms.localizedWeight_tsupport_subset

#check @QuaternaryQuadraticForms.localizedWeight_tsupport_subset_closedBall
#print axioms QuaternaryQuadraticForms.localizedWeight_tsupport_subset_closedBall

#check @QuaternaryQuadraticForms.localizedWeight_hasCompactSupport
#print axioms QuaternaryQuadraticForms.localizedWeight_hasCompactSupport

#check @QuaternaryQuadraticForms.localizedWeight_isSmoothWeight
#print axioms QuaternaryQuadraticForms.localizedWeight_isSmoothWeight

#check @QuaternaryQuadraticForms.localizedWeight_nonzero_imp_near_support
#print axioms QuaternaryQuadraticForms.localizedWeight_nonzero_imp_near_support

#check @QuaternaryQuadraticForms.heathBrownTheta_integral_scaled_translate
#print axioms QuaternaryQuadraticForms.heathBrownTheta_integral_scaled_translate

#check @QuaternaryQuadraticForms.localizedWeight_integrable_in_center
#print axioms QuaternaryQuadraticForms.localizedWeight_integrable_in_center

#check @QuaternaryQuadraticForms.localizedWeight_integral_center
#print axioms QuaternaryQuadraticForms.localizedWeight_integral_center

#check @QuaternaryQuadraticForms.localizedWeight_reconstruction
#print axioms QuaternaryQuadraticForms.localizedWeight_reconstruction

#check @QuaternaryQuadraticForms.quadraticFamily_singularIntegral_integrable_of_isometry_cover
#print axioms QuaternaryQuadraticForms.quadraticFamily_singularIntegral_integrable_of_isometry_cover

#check @QuaternaryQuadraticForms.deltaIntegral_rescaledFrequency_norm
#print axioms QuaternaryQuadraticForms.deltaIntegral_rescaledFrequency_norm

#check @QuaternaryQuadraticForms.deltaIntegral_rapid_scale_identity
#print axioms QuaternaryQuadraticForms.deltaIntegral_rapid_scale_identity

#check @QuaternaryQuadraticForms.deltaIntegral_epsilon_scale_identity
#print axioms QuaternaryQuadraticForms.deltaIntegral_epsilon_scale_identity

#check @QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_add
#print axioms QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_add

#check @QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_double
#print axioms QuaternaryQuadraticForms.deltaIntegral_value_derivative_scale_double

#check @QuaternaryQuadraticForms.deltaIntegral_combine_value_derivative_bounds
#print axioms QuaternaryQuadraticForms.deltaIntegral_combine_value_derivative_bounds

#check @QuaternaryQuadraticForms.deltaIntegral_zero_weight
#print axioms QuaternaryQuadraticForms.deltaIntegral_zero_weight

#check @QuaternaryQuadraticForms.deltaIntegral_eq_zero_of_support_bound
#print axioms QuaternaryQuadraticForms.deltaIntegral_eq_zero_of_support_bound

#check @QuaternaryQuadraticForms.deltaIntegral_eventually_zero
#print axioms QuaternaryQuadraticForms.deltaIntegral_eventually_zero

#check @QuaternaryQuadraticForms.hasDerivAt_deltaIntegral_zero
#print axioms QuaternaryQuadraticForms.hasDerivAt_deltaIntegral_zero

#check @QuaternaryQuadraticForms.deriv_deltaIntegral_eq_zero_of_support_bound
#print axioms QuaternaryQuadraticForms.deriv_deltaIntegral_eq_zero_of_support_bound

#check @QuaternaryQuadraticForms.deltaIntegral_uniform_cutoff
#print axioms QuaternaryQuadraticForms.deltaIntegral_uniform_cutoff

#check @QuaternaryQuadraticForms.source_delta_integrals_real
#print axioms QuaternaryQuadraticForms.source_delta_integrals_real

#check @QuaternaryQuadraticForms.source_delta_integrals
#print axioms QuaternaryQuadraticForms.source_delta_integrals

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.extend_of_cutoff
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.extend_of_cutoff

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.of_finite_cover
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.of_finite_cover

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.of_realIsometry
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.of_realIsometry

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.of_isometry_cover
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.of_isometry_cover

#check @QuaternaryQuadraticForms.heathBrown_local_deltaIntegralBounds
#print axioms QuaternaryQuadraticForms.heathBrown_local_deltaIntegralBounds

#check @QuaternaryQuadraticForms.realQuadraticGradient_hasFDerivAt
#print axioms QuaternaryQuadraticForms.realQuadraticGradient_hasFDerivAt

#check @QuaternaryQuadraticForms.realHessian_realQuadraticValue
#print axioms QuaternaryQuadraticForms.realHessian_realQuadraticValue

#check @QuaternaryQuadraticForms.det_realHessian_realQuadraticValue
#print axioms QuaternaryQuadraticForms.det_realHessian_realQuadraticValue

#check @QuaternaryQuadraticForms.abs_det_realHessian_realQuadraticValue
#print axioms QuaternaryQuadraticForms.abs_det_realHessian_realQuadraticValue

#check @QuaternaryQuadraticForms.realQuadraticValue_hessian_uniform_lower_bound
#print axioms QuaternaryQuadraticForms.realQuadraticValue_hessian_uniform_lower_bound

#check @QuaternaryQuadraticForms.exists_uniformHBWeightControl
#print axioms QuaternaryQuadraticForms.exists_uniformHBWeightControl

#check @QuaternaryQuadraticForms.IsSmoothWeight.comp_realIsometry
#print axioms QuaternaryQuadraticForms.IsSmoothWeight.comp_realIsometry

#check @QuaternaryQuadraticForms.tsupport_comp_realIsometry
#print axioms QuaternaryQuadraticForms.tsupport_comp_realIsometry

#check @QuaternaryQuadraticForms.localizedWeightFamily_isSmoothWeight
#print axioms QuaternaryQuadraticForms.localizedWeightFamily_isSmoothWeight

#check @QuaternaryQuadraticForms.localizedWeightFamily_support_bound
#print axioms QuaternaryQuadraticForms.localizedWeightFamily_support_bound

#check @QuaternaryQuadraticForms.localizedIsometryWeightFamily_isSmoothWeight
#print axioms QuaternaryQuadraticForms.localizedIsometryWeightFamily_isSmoothWeight

#check @QuaternaryQuadraticForms.localizedIsometryWeightFamily_support_bound
#print axioms QuaternaryQuadraticForms.localizedIsometryWeightFamily_support_bound

#check @QuaternaryQuadraticForms.localizedIsometryWeightFamily_uniform_control
#print axioms QuaternaryQuadraticForms.localizedIsometryWeightFamily_uniform_control

#check @QuaternaryQuadraticForms.localizedWeight_alternative
#print axioms QuaternaryQuadraticForms.localizedWeight_alternative

#check @QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_pos
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_pos

#check @QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_norm_le_two
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_norm_le_two

#check @QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_le_two
#print axioms QuaternaryQuadraticForms.localQuadraticDensity_goodPrime_inv_le_two

#check @QuaternaryQuadraticForms.sourceConstrainedFourierSum_zero_norm_le_two_mul_sq
#print axioms QuaternaryQuadraticForms.sourceConstrainedFourierSum_zero_norm_le_two_mul_sq

#check @QuaternaryQuadraticForms.sourceMainCoefficient_local_norm_le
#print axioms QuaternaryQuadraticForms.sourceMainCoefficient_local_norm_le

#check @QuaternaryQuadraticForms.graphPoint_contDiff
#print axioms QuaternaryQuadraticForms.graphPoint_contDiff

#check @QuaternaryQuadraticForms.graphPoint_continuous
#print axioms QuaternaryQuadraticForms.graphPoint_continuous

#check @QuaternaryQuadraticForms.graphPoint_zero
#print axioms QuaternaryQuadraticForms.graphPoint_zero

#check @QuaternaryQuadraticForms.graphPoint_succ
#print axioms QuaternaryQuadraticForms.graphPoint_succ

#check @QuaternaryQuadraticForms.graphTail_apply
#print axioms QuaternaryQuadraticForms.graphTail_apply

#check @QuaternaryQuadraticForms.graphTail_continuous
#print axioms QuaternaryQuadraticForms.graphTail_continuous

#check @QuaternaryQuadraticForms.graphTail_graphPoint
#print axioms QuaternaryQuadraticForms.graphTail_graphPoint

#check @QuaternaryQuadraticForms.graphPoint_graphTail
#print axioms QuaternaryQuadraticForms.graphPoint_graphTail

#check @QuaternaryQuadraticForms.real_inner_graphPoint
#print axioms QuaternaryQuadraticForms.real_inner_graphPoint

#check @QuaternaryQuadraticForms.realVector4_norm_sq_graphTail
#print axioms QuaternaryQuadraticForms.realVector4_norm_sq_graphTail

#check @QuaternaryQuadraticForms.realQuadraticValue_graphPoint
#print axioms QuaternaryQuadraticForms.realQuadraticValue_graphPoint

#check @QuaternaryQuadraticForms.realQuadraticGradient_graphPoint_zero
#print axioms QuaternaryQuadraticForms.realQuadraticGradient_graphPoint_zero

#check @QuaternaryQuadraticForms.quadraticLinearCoeff_contDiff
#print axioms QuaternaryQuadraticForms.quadraticLinearCoeff_contDiff

#check @QuaternaryQuadraticForms.quadraticConstantCoeff_contDiff
#print axioms QuaternaryQuadraticForms.quadraticConstantCoeff_contDiff

#check @QuaternaryQuadraticForms.quadraticDiscriminant_contDiff
#print axioms QuaternaryQuadraticForms.quadraticDiscriminant_contDiff

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_measurable
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_measurable

#check @QuaternaryQuadraticForms.quadraticPositiveRootDomain_isOpen
#print axioms QuaternaryQuadraticForms.quadraticPositiveRootDomain_isOpen

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_contDiffOn
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_contDiffOn

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_firstDerivative
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_firstDerivative

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_value_zero
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_value_zero

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_zero_pos
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_zero_pos

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_unique
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_unique

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_characterization
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_characterization

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_succ
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_succ

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_norm
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_gradient_norm

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_area_measure
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_area_measure

#check @QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_graph
#print axioms QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_graph

#check @QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable_of_geometry
#print axioms QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable_of_geometry

#check @QuaternaryQuadraticForms.quadraticC0_thinSlab_tendsto_singularIntegral
#print axioms QuaternaryQuadraticForms.quadraticC0_thinSlab_tendsto_singularIntegral

#check @QuaternaryQuadraticForms.quadraticC0_thinSlabSingularIntegral_eq_singularIntegral
#print axioms QuaternaryQuadraticForms.quadraticC0_thinSlabSingularIntegral_eq_singularIntegral

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.congr_sigma
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.congr_sigma

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.quadraticC0_surface
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.quadraticC0_surface

#check @QuaternaryQuadraticForms.realVectorTail_continuous
#print axioms QuaternaryQuadraticForms.realVectorTail_continuous

#check @QuaternaryQuadraticForms.realVectorTail_graphPoint
#print axioms QuaternaryQuadraticForms.realVectorTail_graphPoint

#check @QuaternaryQuadraticForms.graphPoint_realVectorTail
#print axioms QuaternaryQuadraticForms.graphPoint_realVectorTail

#check @QuaternaryQuadraticForms.realVectorTail_surfaceGraph
#print axioms QuaternaryQuadraticForms.realVectorTail_surfaceGraph

#check @QuaternaryQuadraticForms.weightTailSupport_isCompact
#print axioms QuaternaryQuadraticForms.weightTailSupport_isCompact

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_hbGraphSelector
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_hbGraphSelector

#check @QuaternaryQuadraticForms.weightTailSupport_subset_quadraticPositiveRootDomain
#print axioms QuaternaryQuadraticForms.weightTailSupport_subset_quadraticPositiveRootDomain

#check @QuaternaryQuadraticForms.quadraticC0_gradient_zero_pos_on_tsupport
#print axioms QuaternaryQuadraticForms.quadraticC0_gradient_zero_pos_on_tsupport

#check @QuaternaryQuadraticForms.quadraticC0_zero_mem_graph_of_mem_tsupport
#print axioms QuaternaryQuadraticForms.quadraticC0_zero_mem_graph_of_mem_tsupport

#check @QuaternaryQuadraticForms.weight_surfaceGraph_eq_zero_of_notMem_tailSupport
#print axioms QuaternaryQuadraticForms.weight_surfaceGraph_eq_zero_of_notMem_tailSupport

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_area_div_gradient
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_area_div_gradient

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_continuousOn
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_continuousOn

#check @QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_integrable
#print axioms QuaternaryQuadraticForms.quadraticPositiveRoot_graphIntegrand_integrable

#check @QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_hbGraphIntegral
#print axioms QuaternaryQuadraticForms.quadraticC0_singularIntegral_eq_hbGraphIntegral

#check @QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable
#print axioms QuaternaryQuadraticForms.quadraticC0_singularIntegral_integrable

#check @QuaternaryQuadraticForms.realQuadraticValue_eq_inner
#print axioms QuaternaryQuadraticForms.realQuadraticValue_eq_inner

#check @QuaternaryQuadraticForms.realQuadraticValue_contDiff
#print axioms QuaternaryQuadraticForms.realQuadraticValue_contDiff

#check @QuaternaryQuadraticForms.realQuadraticValue_continuous
#print axioms QuaternaryQuadraticForms.realQuadraticValue_continuous

#check @QuaternaryQuadraticForms.realQuadraticValue_smul
#print axioms QuaternaryQuadraticForms.realQuadraticValue_smul

#check @QuaternaryQuadraticForms.realQuadraticValue_hasGradientAt
#print axioms QuaternaryQuadraticForms.realQuadraticValue_hasGradientAt

#check @QuaternaryQuadraticForms.gradient_realQuadraticValue
#print axioms QuaternaryQuadraticForms.gradient_realQuadraticValue

#check @QuaternaryQuadraticForms.realQuadraticGradient_continuous
#print axioms QuaternaryQuadraticForms.realQuadraticGradient_continuous

#check @QuaternaryQuadraticForms.realQuadraticGradient_ne_zero
#print axioms QuaternaryQuadraticForms.realQuadraticGradient_ne_zero

#check @QuaternaryQuadraticForms.realVector4_isCompact_annulus
#print axioms QuaternaryQuadraticForms.realVector4_isCompact_annulus

#check @QuaternaryQuadraticForms.realQuadraticGradient_norm_annulus_lower_bound
#print axioms QuaternaryQuadraticForms.realQuadraticGradient_norm_annulus_lower_bound

#check @QuaternaryQuadraticForms.gradient_realQuadraticValue_annulus_lower_bound
#print axioms QuaternaryQuadraticForms.gradient_realQuadraticValue_annulus_lower_bound

#check @QuaternaryQuadraticForms.realQuadraticValue_abs_bound_closedBall
#print axioms QuaternaryQuadraticForms.realQuadraticValue_abs_bound_closedBall

#check @QuaternaryQuadraticForms.signedCoordinateIsometry_apply
#print axioms QuaternaryQuadraticForms.signedCoordinateIsometry_apply

#check @QuaternaryQuadraticForms.signedCoordinateChange_card
#print axioms QuaternaryQuadraticForms.signedCoordinateChange_card

#check @QuaternaryQuadraticForms.signedCoordinateIsometry_norm
#print axioms QuaternaryQuadraticForms.signedCoordinateIsometry_norm

#check @QuaternaryQuadraticForms.signedCoordinateIsometry_symm_norm
#print axioms QuaternaryQuadraticForms.signedCoordinateIsometry_symm_norm

#check @QuaternaryQuadraticForms.signedCoordinateIsometry_measurePreserving
#print axioms QuaternaryQuadraticForms.signedCoordinateIsometry_measurePreserving

#check @QuaternaryQuadraticForms.real_inner_symm_isometry
#print axioms QuaternaryQuadraticForms.real_inner_symm_isometry

#check @QuaternaryQuadraticForms.hasGradientAt_comp_realIsometry
#print axioms QuaternaryQuadraticForms.hasGradientAt_comp_realIsometry

#check @QuaternaryQuadraticForms.gradient_comp_realIsometry
#print axioms QuaternaryQuadraticForms.gradient_comp_realIsometry

#check @QuaternaryQuadraticForms.norm_gradient_comp_realIsometry
#print axioms QuaternaryQuadraticForms.norm_gradient_comp_realIsometry

#check @QuaternaryQuadraticForms.gradient_realQuadraticValue_comp_isometry
#print axioms QuaternaryQuadraticForms.gradient_realQuadraticValue_comp_isometry

#check @QuaternaryQuadraticForms.realIsometryMatrix_apply
#print axioms QuaternaryQuadraticForms.realIsometryMatrix_apply

#check @QuaternaryQuadraticForms.realIsometryMatrix_det_ne_zero
#print axioms QuaternaryQuadraticForms.realIsometryMatrix_det_ne_zero

#check @QuaternaryQuadraticForms.realQuadraticValue_matrix_congruence
#print axioms QuaternaryQuadraticForms.realQuadraticValue_matrix_congruence

#check @QuaternaryQuadraticForms.realQuadraticPullbackMatrix_value
#print axioms QuaternaryQuadraticForms.realQuadraticPullbackMatrix_value

#check @QuaternaryQuadraticForms.realQuadraticPullbackMatrix_symmetric
#print axioms QuaternaryQuadraticForms.realQuadraticPullbackMatrix_symmetric

#check @QuaternaryQuadraticForms.realQuadraticPullbackMatrix_det_ne_zero
#print axioms QuaternaryQuadraticForms.realQuadraticPullbackMatrix_det_ne_zero

#check @QuaternaryQuadraticForms.deltaIntegral_comp_realIsometry
#print axioms QuaternaryQuadraticForms.deltaIntegral_comp_realIsometry

#check @QuaternaryQuadraticForms.singularSeriesRemovalFactor_eq_primeFactors
#print axioms QuaternaryQuadraticForms.singularSeriesRemovalFactor_eq_primeFactors

#check @QuaternaryQuadraticForms.singularSeriesRemovalFactor_one
#print axioms QuaternaryQuadraticForms.singularSeriesRemovalFactor_one

#check @QuaternaryQuadraticForms.singularSeriesConstant_eq_orderedValue
#print axioms QuaternaryQuadraticForms.singularSeriesConstant_eq_orderedValue

#check @QuaternaryQuadraticForms.singularSeriesConstant_eq_of_goodPrimeAgreement
#print axioms QuaternaryQuadraticForms.singularSeriesConstant_eq_of_goodPrimeAgreement

#check @QuaternaryQuadraticForms.sourceMainCoefficient_one
#print axioms QuaternaryQuadraticForms.sourceMainCoefficient_one

#check @QuaternaryQuadraticForms.sourceMainCoefficient_one_eq_singularSeriesConstant
#print axioms QuaternaryQuadraticForms.sourceMainCoefficient_one_eq_singularSeriesConstant

#check @QuaternaryQuadraticForms.sourceMainCoefficient_eq_prime_product
#print axioms QuaternaryQuadraticForms.sourceMainCoefficient_eq_prime_product

#check @QuaternaryQuadraticForms.sourceMainCoefficient_norm_le
#print axioms QuaternaryQuadraticForms.sourceMainCoefficient_norm_le

#check @QuaternaryQuadraticForms.source_main_coefficient_bound
#print axioms QuaternaryQuadraticForms.source_main_coefficient_bound

#check @QuaternaryQuadraticForms.surfaceGraph_injective
#print axioms QuaternaryQuadraticForms.surfaceGraph_injective

#check @QuaternaryQuadraticForms.surfaceGraph_measurable
#print axioms QuaternaryQuadraticForms.surfaceGraph_measurable

#check @QuaternaryQuadraticForms.surfaceGraph_measurableEmbedding
#print axioms QuaternaryQuadraticForms.surfaceGraph_measurableEmbedding

#check @QuaternaryQuadraticForms.graphAreaFactor_pos
#print axioms QuaternaryQuadraticForms.graphAreaFactor_pos

#check @QuaternaryQuadraticForms.graphAreaFactor_nonneg
#print axioms QuaternaryQuadraticForms.graphAreaFactor_nonneg

#check @QuaternaryQuadraticForms.graphAreaFactor_measurable
#print axioms QuaternaryQuadraticForms.graphAreaFactor_measurable

#check @QuaternaryQuadraticForms.integral_surfaceGraph_image
#print axioms QuaternaryQuadraticForms.integral_surfaceGraph_image

#check @QuaternaryQuadraticForms.integrable_surfaceGraph_image_iff
#print axioms QuaternaryQuadraticForms.integrable_surfaceGraph_image_iff

#check @QuaternaryQuadraticForms.euclideanSurfaceMeasure_realIsometry
#print axioms QuaternaryQuadraticForms.euclideanSurfaceMeasure_realIsometry

#check @QuaternaryQuadraticForms.euclideanSurfaceMeasure_restrict_realIsometry
#print axioms QuaternaryQuadraticForms.euclideanSurfaceMeasure_restrict_realIsometry

#check @QuaternaryQuadraticForms.singularIntegral_integrable_comp_realIsometry
#print axioms QuaternaryQuadraticForms.singularIntegral_integrable_comp_realIsometry

#check @QuaternaryQuadraticForms.singularIntegral_comp_realIsometry
#print axioms QuaternaryQuadraticForms.singularIntegral_comp_realIsometry

#check @QuaternaryQuadraticForms.mem_integerQuadricZeros
#print axioms QuaternaryQuadraticForms.mem_integerQuadricZeros

#check @QuaternaryQuadraticForms.sourceQuadricZeroSet_eq
#print axioms QuaternaryQuadraticForms.sourceQuadricZeroSet_eq

#check @QuaternaryQuadraticForms.sourceQuadricZeroSet_finite
#print axioms QuaternaryQuadraticForms.sourceQuadricZeroSet_finite

#check @QuaternaryQuadraticForms.sourceQuadricZeroSet_ncard
#print axioms QuaternaryQuadraticForms.sourceQuadricZeroSet_ncard

#check @QuaternaryQuadraticForms.integerQuadricZeros_card_le_one
#print axioms QuaternaryQuadraticForms.integerQuadricZeros_card_le_one

#check @QuaternaryQuadraticForms.integerQuadricZeros_bound_of_lattice_model
#print axioms QuaternaryQuadraticForms.integerQuadricZeros_bound_of_lattice_model

#check @QuaternaryQuadraticForms.rationalQuadric_euclidean_bound
#print axioms QuaternaryQuadraticForms.rationalQuadric_euclidean_bound

#check @QuaternaryQuadraticForms.source_quadric_count
#print axioms QuaternaryQuadraticForms.source_quadric_count

#check @QuaternaryQuadraticForms.binary_zero_discriminant_isSquare
#print axioms QuaternaryQuadraticForms.binary_zero_discriminant_isSquare

#check @QuaternaryQuadraticForms.det_hyperbolic_binary
#print axioms QuaternaryQuadraticForms.det_hyperbolic_binary

#check @QuaternaryQuadraticForms.nonsquare_det_binary_anisotropic
#print axioms QuaternaryQuadraticForms.nonsquare_det_binary_anisotropic

#check @QuaternaryQuadraticForms.exists_hyperbolic_complement_basis
#print axioms QuaternaryQuadraticForms.exists_hyperbolic_complement_basis

#check @QuaternaryQuadraticForms.rational_congruence_apply
#print axioms QuaternaryQuadraticForms.rational_congruence_apply

#check @QuaternaryQuadraticForms.exists_rational_hyperbolic_matrix
#print axioms QuaternaryQuadraticForms.exists_rational_hyperbolic_matrix

#check @QuaternaryQuadraticForms.rational_family_clear_denominators
#print axioms QuaternaryQuadraticForms.rational_family_clear_denominators

#check @QuaternaryQuadraticForms.integerMatrix_coordinate_bound
#print axioms QuaternaryQuadraticForms.integerMatrix_coordinate_bound

#check @QuaternaryQuadraticForms.rationalQuadric_integer_model
#print axioms QuaternaryQuadraticForms.rationalQuadric_integer_model

#check @QuaternaryQuadraticForms.exists_rational_quadric_normal_form
#print axioms QuaternaryQuadraticForms.exists_rational_quadric_normal_form

#check @QuaternaryQuadraticForms.splitQuadric_mem_interval
#print axioms QuaternaryQuadraticForms.splitQuadric_mem_interval

#check @QuaternaryQuadraticForms.splitQuadricCoefficient_pos
#print axioms QuaternaryQuadraticForms.splitQuadricCoefficient_pos

#check @QuaternaryQuadraticForms.splitQuadric_binaryValue_natAbs_le
#print axioms QuaternaryQuadraticForms.splitQuadric_binaryValue_natAbs_le

#check @QuaternaryQuadraticForms.splitQuadric_zero_fiber_card_le
#print axioms QuaternaryQuadraticForms.splitQuadric_zero_fiber_card_le

#check @QuaternaryQuadraticForms.splitQuadric_nonzero_fibers_uniform
#print axioms QuaternaryQuadraticForms.splitQuadric_nonzero_fibers_uniform

#check @QuaternaryQuadraticForms.splitQuadric_nonzero_box_card_le
#print axioms QuaternaryQuadraticForms.splitQuadric_nonzero_box_card_le

#check @QuaternaryQuadraticForms.splitQuadric_box_bound
#print axioms QuaternaryQuadraticForms.splitQuadric_box_bound

#check @QuaternaryQuadraticForms.splitQuadric_mem_signedDivisors
#print axioms QuaternaryQuadraticForms.splitQuadric_mem_signedDivisors

#check @QuaternaryQuadraticForms.splitQuadric_signedDivisors_card_le
#print axioms QuaternaryQuadraticForms.splitQuadric_signedDivisors_card_le

#check @QuaternaryQuadraticForms.splitQuadric_nonzero_fiber_card_le
#print axioms QuaternaryQuadraticForms.splitQuadric_nonzero_fiber_card_le

#check @QuaternaryQuadraticForms.poissonTestFunction_isSmoothWeight
#print axioms QuaternaryQuadraticForms.poissonTestFunction_isSmoothWeight

#check @QuaternaryQuadraticForms.poissonTestFunction_eventually_zero
#print axioms QuaternaryQuadraticForms.poissonTestFunction_eventually_zero

#check @QuaternaryQuadraticForms.poissonDeltaIntegral_eventually_zero
#print axioms QuaternaryQuadraticForms.poissonDeltaIntegral_eventually_zero

#check @QuaternaryQuadraticForms.mixedIntegerSummand_fourier_phase
#print axioms QuaternaryQuadraticForms.mixedIntegerSummand_fourier_phase

#check @QuaternaryQuadraticForms.poisson_mixed_fourier_coefficient
#print axioms QuaternaryQuadraticForms.poisson_mixed_fourier_coefficient

#check @QuaternaryQuadraticForms.poisson_mixed_complete_sum
#print axioms QuaternaryQuadraticForms.poisson_mixed_complete_sum

#check @QuaternaryQuadraticForms.realQuadraticValue_integerRealVector
#print axioms QuaternaryQuadraticForms.realQuadraticValue_integerRealVector

#check @QuaternaryQuadraticForms.realQuadraticValue_scaled_integerRealVector
#print axioms QuaternaryQuadraticForms.realQuadraticValue_scaled_integerRealVector

#check @QuaternaryQuadraticForms.poisson_delta_scaled_argument
#print axioms QuaternaryQuadraticForms.poisson_delta_scaled_argument

#check @QuaternaryQuadraticForms.poisson_delta_phase
#print axioms QuaternaryQuadraticForms.poisson_delta_phase

#check @QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_weight_eq_zero
#print axioms QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_weight_eq_zero

#check @QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_of_dvd
#print axioms QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_of_dvd

#check @QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_not_dvd
#print axioms QuaternaryQuadraticForms.poissonDeltaLatticeTerm_eq_zero_of_not_dvd

#check @QuaternaryQuadraticForms.poissonDeltaLatticeTerm_summable
#print axioms QuaternaryQuadraticForms.poissonDeltaLatticeTerm_summable

#check @QuaternaryQuadraticForms.weightedQuadraticZeroSum_pointwise_delta
#print axioms QuaternaryQuadraticForms.weightedQuadraticZeroSum_pointwise_delta

#check @QuaternaryQuadraticForms.poisson_tsum_comm_of_finite_left
#print axioms QuaternaryQuadraticForms.poisson_tsum_comm_of_finite_left

#check @QuaternaryQuadraticForms.weightedQuadraticZeroSum_delta
#print axioms QuaternaryQuadraticForms.weightedQuadraticZeroSum_delta

#check @QuaternaryQuadraticForms.poisson_test_function_complete_sum
#print axioms QuaternaryQuadraticForms.poisson_test_function_complete_sum

#check @QuaternaryQuadraticForms.poissonFrequencyTerm_eventually_zero
#print axioms QuaternaryQuadraticForms.poissonFrequencyTerm_eventually_zero

#check @QuaternaryQuadraticForms.poissonModulusTerm_finite_support
#print axioms QuaternaryQuadraticForms.poissonModulusTerm_finite_support

#check @QuaternaryQuadraticForms.compactSupport_integerRealVector_finite
#print axioms QuaternaryQuadraticForms.compactSupport_integerRealVector_finite

#check @QuaternaryQuadraticForms.scaledWeight_integerRealVector_finite
#print axioms QuaternaryQuadraticForms.scaledWeight_integerRealVector_finite

#check @QuaternaryQuadraticForms.weightedQuadraticZeroSum_finite_support
#print axioms QuaternaryQuadraticForms.weightedQuadraticZeroSum_finite_support

#check @QuaternaryQuadraticForms.poissonTestFunction_integerRealVector_finite
#print axioms QuaternaryQuadraticForms.poissonTestFunction_integerRealVector_finite

#check @QuaternaryQuadraticForms.weightedQuadraticZeroSum_extend_eq_source
#print axioms QuaternaryQuadraticForms.weightedQuadraticZeroSum_extend_eq_source

#check @QuaternaryQuadraticForms.poisson_normalization_factor
#print axioms QuaternaryQuadraticForms.poisson_normalization_factor

#check @QuaternaryQuadraticForms.poissonResidueVector_cast
#print axioms QuaternaryQuadraticForms.poissonResidueVector_cast

#check @QuaternaryQuadraticForms.poissonResidueVector_injective
#print axioms QuaternaryQuadraticForms.poissonResidueVector_injective

#check @QuaternaryQuadraticForms.poissonResidueVector_surjective
#print axioms QuaternaryQuadraticForms.poissonResidueVector_surjective

#check @QuaternaryQuadraticForms.poissonResidueEquiv_apply
#print axioms QuaternaryQuadraticForms.poissonResidueEquiv_apply

#check @QuaternaryQuadraticForms.integerRealVector_poissonResidueVector
#print axioms QuaternaryQuadraticForms.integerRealVector_poissonResidueVector

#check @QuaternaryQuadraticForms.poisson_tsum_residue_classes
#print axioms QuaternaryQuadraticForms.poisson_tsum_residue_classes

#check @QuaternaryQuadraticForms.poisson_phase_mul_summable
#print axioms QuaternaryQuadraticForms.poisson_phase_mul_summable

#check @QuaternaryQuadraticForms.poisson_residue_fourier_summable
#print axioms QuaternaryQuadraticForms.poisson_residue_fourier_summable

#check @QuaternaryQuadraticForms.poisson_periodic_weight
#print axioms QuaternaryQuadraticForms.poisson_periodic_weight

#check @QuaternaryQuadraticForms.poisson_integral_comp_inv_smul
#print axioms QuaternaryQuadraticForms.poisson_integral_comp_inv_smul

#check @QuaternaryQuadraticForms.poissonFourierIntegral_testFunction_general
#print axioms QuaternaryQuadraticForms.poissonFourierIntegral_testFunction_general

#check @QuaternaryQuadraticForms.poisson_frequency_scale
#print axioms QuaternaryQuadraticForms.poisson_frequency_scale

#check @QuaternaryQuadraticForms.poissonFourierIntegral_testFunction
#print axioms QuaternaryQuadraticForms.poissonFourierIntegral_testFunction

#check @QuaternaryQuadraticForms.integerRealVector_inner
#print axioms QuaternaryQuadraticForms.integerRealVector_inner

#check @QuaternaryQuadraticForms.poisson_affine_phase_eq_stdAddChar
#print axioms QuaternaryQuadraticForms.poisson_affine_phase_eq_stdAddChar

#check @QuaternaryQuadraticForms.poisson_affine_integer_lattice
#print axioms QuaternaryQuadraticForms.poisson_affine_integer_lattice

#check @QuaternaryQuadraticForms.mixedCompleteSum_extend_eq_source
#print axioms QuaternaryQuadraticForms.mixedCompleteSum_extend_eq_source

#check @QuaternaryQuadraticForms.weightedQuadraticZeroSum_poisson
#print axioms QuaternaryQuadraticForms.weightedQuadraticZeroSum_poisson

#check @QuaternaryQuadraticForms.source_delta_poisson
#print axioms QuaternaryQuadraticForms.source_delta_poisson

#check @QuaternaryQuadraticForms.Trusted.poisson_four_dimensional
#print axioms QuaternaryQuadraticForms.Trusted.poisson_four_dimensional

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error

#check @QuaternaryQuadraticForms.source_localized_frequency_integrals
#print axioms QuaternaryQuadraticForms.source_localized_frequency_integrals

#check @QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale
#print axioms QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale

#check @QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale
#print axioms QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale

#check @QuaternaryQuadraticForms.integerEuclidean_frequency_tail
#print axioms QuaternaryQuadraticForms.integerEuclidean_frequency_tail

#check @QuaternaryQuadraticForms.sourceMixedCompleteSum_trivial_bound
#print axioms QuaternaryQuadraticForms.sourceMixedCompleteSum_trivial_bound

#check @QuaternaryQuadraticForms.sourceCompositeWeight_zero_of_one_lt
#print axioms QuaternaryQuadraticForms.sourceCompositeWeight_zero_of_one_lt

#check @QuaternaryQuadraticForms.sourceMixedCompleteSum_zero_frequency
#print axioms QuaternaryQuadraticForms.sourceMixedCompleteSum_zero_frequency

#check @QuaternaryQuadraticForms.source_zero_frequency_contribution
#print axioms QuaternaryQuadraticForms.source_zero_frequency_contribution

#check @QuaternaryQuadraticForms.mem_poissonModuliBelow
#print axioms QuaternaryQuadraticForms.mem_poissonModuliBelow

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.largeFrequency
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.largeFrequency

#check @QuaternaryQuadraticForms.source_large_frequency_truncation
#print axioms QuaternaryQuadraticForms.source_large_frequency_truncation

#check @QuaternaryQuadraticForms.mem_offConeFrequencies
#print axioms QuaternaryQuadraticForms.mem_offConeFrequencies

#check @QuaternaryQuadraticForms.sourceMixedCompleteSum_sum_le_gcd_classes
#print axioms QuaternaryQuadraticForms.sourceMixedCompleteSum_sum_le_gcd_classes

#check @QuaternaryQuadraticForms.dualQuadraticValue_ball_bound
#print axioms QuaternaryQuadraticForms.dualQuadraticValue_ball_bound

#check @QuaternaryQuadraticForms.ScaledFrequencyIntegralBound.offCone_modulus_reduction
#print axioms QuaternaryQuadraticForms.ScaledFrequencyIntegralBound.offCone_modulus_reduction

#check @QuaternaryQuadraticForms.offCone_dual_growth
#print axioms QuaternaryQuadraticForms.offCone_dual_growth

#check @QuaternaryQuadraticForms.offCone_average_scale
#print axioms QuaternaryQuadraticForms.offCone_average_scale
