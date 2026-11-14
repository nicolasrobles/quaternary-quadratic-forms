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
    `QuaternaryQuadraticForms.integralProjectiveTrace_quadratic_dvd]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"

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
