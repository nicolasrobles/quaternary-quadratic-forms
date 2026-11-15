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
    `QuaternaryQuadraticForms.exists_badReductionSystem_eval₂_zero_iff,
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
    `QuaternaryQuadraticForms.genericQuadricMatrix_map_eval₂Hom,
    `QuaternaryQuadraticForms.genericDegreeForm_map_eval₂Hom,
    `QuaternaryQuadraticForms.genericBadReductionSystem_map_eval₂Hom,
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
    `QuaternaryQuadraticForms.genericPlaneQuadricMatrix_map_eval₂Hom,
    `QuaternaryQuadraticForms.genericPlaneDegreeForm_map_eval₂Hom,
    `QuaternaryQuadraticForms.genericPlaneNormal_eval₂Hom,
    `QuaternaryQuadraticForms.genericPlaneReductionSystem_map_eval₂Hom,
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
    `QuaternaryQuadraticForms.totalDegree_eval₂_le_of_degree_one,
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
    `QuaternaryQuadraticForms.totient_mul_eq_sum_moebius]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"
  let inputNames : List Lean.Name := [
    `QuaternaryQuadraticForms.Trusted.weil_simple_roots,
    `QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data,
    `QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants,
    `QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent]
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
