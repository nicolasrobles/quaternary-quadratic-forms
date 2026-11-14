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
    `QuaternaryQuadraticForms.uniform_polynomial_fourier_bound]
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
