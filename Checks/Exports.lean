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
    `QuaternaryQuadraticForms.integralFourierSum_of_dvd]
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
