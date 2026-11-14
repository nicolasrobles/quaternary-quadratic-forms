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
    `QuaternaryQuadraticForms.projective_weil_bound]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"
  let inputNames : List Lean.Name := [
    `QuaternaryQuadraticForms.Trusted.weil_simple_roots]
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
