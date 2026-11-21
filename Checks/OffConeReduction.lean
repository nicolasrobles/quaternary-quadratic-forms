import Lean
import QuaternaryQuadraticForms.OffConeFrequencyReduction
import QuaternaryQuadraticForms.OffConeFrequencyScales

run_cmd do
  let environment ← Lean.getEnv
  let names : List Lean.Name := [
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
  let allInputs : List Lean.Name := [
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
  let _ ← environment.constants.foldM (init := ()) fun _ name info => do
    if (`QuaternaryQuadraticForms).isPrefixOf name then
      match info with
      | .axiomInfo _ =>
        unless allInputs.contains name do
          Lean.throwError "Unregistered project axiom: {name}"
      | _ => pure ()
    else
      pure ()
  pure ()

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
